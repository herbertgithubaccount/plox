use std::{collections::{HashMap, HashSet}, ops};

use log::warn;
use petgraph::{
    dot::{Config, Dot},
    graph::NodeIndex,
    stable_graph::StableGraph,
};

use crate::{
    generate_pair_permutations, get_ordering_from_order_rules, nearend2, nearstart2, order2, parser::Parser, wild_contains, EOrderRule, ESupportedGame, EWarningRule, PluginData
};


// holds the nodes and edges
// should probably be given a better name
struct SorterGraph<'a> {
    parser: &'a Parser, // parser contains the rules used to generated edges.
    node_indices: HashMap<String, usize>,
    edges: HashSet<(usize, usize)>,
}

impl<'a> SorterGraph<'a> {

    pub fn new(parser: &'a Parser, plugin_datas: &'a [&'a PluginData]) -> Self {
        // list of all mod names that conflict with other mod names
        // key is a mod name, value is a set of conflicting mod names.
        // checking if mod A conflicts with mod B requires checking `conflicts.get(modA).contains(modB) && conflicts[modB].contains(modA)`,
        // which is kinda akward, but it's better than having to do more than 2 checks
        let conflicts: HashMap<&String, HashSet<&String>> = parser.warning_rules
            .iter()
            .filter_map(|rule| {
                // ignore the rules that aren't conflicts, or the conflicts that have fewer than 2 modnames
                if let EWarningRule::Conflict(conf) = rule {
                    if conf.plugins.len() > 2 {
                        // first index is special
                        return Some((&conf.plugins[0], conf.plugins[1..].iter().collect()));
                    }
                }
                return None
            }).collect();

        // closure that checks if two mods conflict with each other
        let check_conflicts = |data1: &String, data2: &String| -> bool{
            conflicts.get(data1).is_some_and(|confs| confs.contains(data2))
            || conflicts.get(data2).is_some_and(|confs| confs.contains(data1))
        };
        
        // get an iterator that holds all order pairs
        let order_pairs = parser.order_rules.iter()
            .filter_map(|rule| {
                if let EOrderRule::Order(ord) = rule {
                    let mut vec = vec![];
                    for (i, name) in ord.names.iter().enumerate() {
                        for name2 in ord.names.iter().skip(i) {
                            vec.push((name, name2));
                        }
                    }
                    return Some(vec);
                }
                None
            })
            .flatten();

        // names of all plugins, in lowercase
        let plugin_names: Vec<String> = plugin_datas.iter()
            .map(|p| p.name.to_lowercase().to_owned())
            .collect();

        // map that goes plugin_name -> node number
        let node_indices: HashMap<String, usize> = plugin_names.iter().enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();


        // turn the iterator of pairs of order rules into an iterator that stores the mod names matching those rules
        // its gonna be an iterator where each term is a  `(Vec<String>, Vec<String>)``
        let order_matches = order_pairs.filter_map(|(rule1, rule2)| {
            if let Some(rule1_matches) = wild_contains(&plugin_names, rule1) {
                if let Some(rule2_matches) = wild_contains(&plugin_names, rule2) {
                    return Some((rule1_matches, rule2_matches));
                }
            }
            None
        });

        let mut edges: HashSet<(usize, usize)> = HashSet::new();

        for (rule1_matches, rule2_matches) in order_matches {
            for (i, lt) in rule1_matches.iter().enumerate() {
                for gt in rule2_matches.iter().skip(i) {
                    if lt == gt {
                        warn!("Skipping circular edge: {}", i);
                        continue;
                    }
                    if check_conflicts(lt,gt) {
                        warn!("Skipping edge due to conflicts: {lt} < {gt}");
                        continue;
                    }
                    edges.insert((*node_indices.get(lt).unwrap(), *node_indices.get(gt).unwrap()));

                }
            }
        }
        Self {parser, node_indices, edges}
    }
}
// for nodes `x` and `y`, set 
//  `x < y` IF:
//  1) `x` and `y` have no conflicting masters, AND
//  2) any of the following hold:
//      i) `x` is a proper master of `y`
//      ii)  some `Order` rule says a master of `x` comes before a master of `y` (where `x` and `y` are also masters of themselves).
//      iii) some `Requires` rule says `x` is required by `y` (where `x` and `y` are also masters of themselves).



#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ESortType {
    Unstable,
    StableOpt,
    StableFull,
}

pub fn new_unstable_sorter() -> Sorter {
    Sorter::new(ESortType::Unstable, 0)
}

pub fn new_stable_sorter() -> Sorter {
    Sorter::new(ESortType::StableOpt, 100)
}

pub struct Sorter {
    pub sort_type: ESortType,
    pub max_iterations: usize,
}

impl Sorter {
    pub fn new(sort_type: ESortType, max_iterations: usize) -> Self {
        Self {
            sort_type,
            max_iterations,
        }
    }

    /// Sorts the input mods topologically. Mods input is case sensitive!
    ///
    /// # Panics
    ///
    /// Panics if .
    ///
    /// # Errors
    ///
    /// This function will return an error if any parsing fails
    pub fn topo_sort(
        &mut self,
        game: ESupportedGame,
        mods_cased: &[PluginData],
        order_rules: &[EOrderRule],
        warn_rules: &[EWarningRule],
    ) -> Result<Vec<String>, &'static str> {
        // early out
        if order_rules.is_empty() {
            log::info!("No order rules found, nothing to sort");
            return Err("No order rules found");
        }

        // build hashmaps for lookup
        // first map lowercase to cased, this is kinda dumb, but our input is small enough that I don't care about the memory hit
        let mut mods: Vec<String> = vec![];

        let mut index_dict: HashMap<String, usize> = HashMap::new();
        let mut index_dict_rev: HashMap<usize, String> = HashMap::default();
        let mut mod_map: HashMap<usize, String> = HashMap::default();
        for (i, cased_name) in mods_cased.iter().enumerate() {
            let lower_case = cased_name.name.to_lowercase();

            index_dict.insert(lower_case.clone(), i);
            index_dict_rev.insert(i, lower_case.clone());

            mod_map.insert(i, cased_name.name.to_owned());
            mods.push(lower_case.to_owned());
        }


        // add edges from order rules
        let order_pairs = get_ordering_from_order_rules(order_rules);
        let mut edges: Vec<(usize, usize)> = vec![];
        for (a, b) in order_pairs {
            if let (Some(results_for_a), Some(results_for_b)) 
                = (wild_contains(&mods, &a), wild_contains(&mods, &b)) 
            {
                    // foreach esp i, add an edge to all esps j
                for i in &results_for_a {
                    for j in &results_for_b {
                        if i == j {
                            warn!("Skipping circular edge: {}", i);
                            continue;
                        }
                        let idx_a = index_dict[i.as_str()];
                        let idx_b = index_dict[j.as_str()];

                        if !edges.contains(&(idx_a, idx_b)) {
                            edges.push((idx_a, idx_b));
                        }
                    }
                }
            }
        }

        // create graph from edges
        let mut g = StableGraph::<String, ()>::with_capacity(mods.len(), edges.len());
        for n in 0..mods.len() {
            let name = index_dict_rev[&n].clone();
            g.add_node(name);
        }
        // add edges
        for edge in &edges {
            g.add_edge(NodeIndex::new(edge.0), NodeIndex::new(edge.1), ());
        }

        // add edges from masters
        // for mod_data in mods_cased.iter() {
        //     // add an edge from the mod to all its masters
        //     let idx = index_dict[&mod_data.name.to_lowercase()];
        //     if let Some(masters) = &mod_data.masters {
        //         for (master, _hash) in masters {
        //             let master = master.to_lowercase();
        //             if let Some(results) = wild_contains(&mods, &master) {
        //                 for result in results {
        //                     let idx_master = index_dict[&result];
        //                     let edge = (idx_master, idx);
        //                     if !edges.contains(&edge) {
        //                         edges.push(edge);
        //                         g.add_edge(NodeIndex::new(edge.0), NodeIndex::new(edge.1), 1);
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }

        // cycle check
        if self.sort_type == ESortType::Unstable {
            let s = petgraph::algo::toposort(&g, None);
            let sort;
            if let Ok(result) = s {
                sort = result;

                // debug print to file
                let mut res = vec![];
                for idx in &sort {
                    res.push(idx.index());
                }
                let _ = std::fs::create_dir_all("tmp");
                let file = std::fs::File::create("tmp/toposort.json").expect("file create failed");
                serde_json::to_writer_pretty(file, &res).expect("serialize failed");
            } else {
                {
                    let viz = Dot::with_config(&g, &[Config::EdgeNoLabel]);
                    // write to file
                    let _ = std::fs::create_dir_all("tmp");
                    let mut file =
                        std::fs::File::create("tmp/graphviz.dot").expect("file create failed");
                    std::io::Write::write_all(&mut file, format!("{:?}", viz).as_bytes())
                        .expect("write failed");
                }

                // kosaraju_scc
                {
                    let scc = petgraph::algo::kosaraju_scc(&g);
                    let mut res: Vec<Vec<String>> = vec![];
                    for er in &scc {
                        if er.len() > 1 {
                            warn!("cycles:");
                            let mut cycle = vec![];
                            for e in er {
                                // lookup name
                                let name = index_dict_rev[&e.index()].clone();
                                warn!("\t{}: {}", e.index(), name);
                                cycle.push(name);
                            }
                            res.push(cycle);
                        }
                    }
                    // debug print to file
                    if !res.is_empty() {
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/kosaraju_scc.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &res).expect("serialize failed");
                    }
                }

                // tarjan_scc
                {
                    let scc = petgraph::algo::tarjan_scc(&g);
                    let mut res: Vec<Vec<String>> = vec![];
                    for er in &scc {
                        if er.len() > 1 {
                            warn!("cycles:");
                            let mut cycle = vec![];
                            for e in er {
                                // lookup name
                                let name = index_dict_rev[&e.index()].clone();
                                warn!("\t{}: {}", e.index(), name);
                                cycle.push(name);
                            }
                            res.push(cycle);
                        }
                    }
                    // debug print to file
                    if !res.is_empty() {
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/tarjan_scc.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &res).expect("serialize failed");

                        // find all rules that are part of a cycle
                        let mut cycle_rules = vec![];
                        for cycle in &res {
                            for rule in order_rules {
                                // switch
                                let mut names = vec![];
                                if let Some(nearstart) = nearstart2(rule) {
                                    names.push(nearstart.names);
                                } else if let Some(nearend) = nearend2(rule) {
                                    names.push(nearend.names);
                                } else if let Some(order) = order2(rule.clone()) {
                                    names.push(order.names);
                                }

                                // check that the names contain at least 2 mods
                                let mut found = 0;
                                for name in &names {
                                    for n in name {
                                        if cycle.contains(n) {
                                            found += 1;
                                        }
                                    }
                                }
                                if found > 1 {
                                    cycle_rules.push(rule.clone());
                                }
                            }
                        }

                        // print cycle rules to file
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/cycle_rules.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &cycle_rules).expect("serialize failed");
                    }
                }

                return Err("Graph contains a cycle");
            }

            // map sorted index back to mods
            let mut result = vec![];
            for idx in sort {
                result.push(mod_map[&idx.index()].to_owned());
            }
            return Ok(result);
        }

        // sort
        let mut mods_copy: Vec<String> = mods.to_vec();

        // nearstart rules
        for nearstart in order_rules
            .iter()
            .filter_map(nearstart2)
            .flat_map(|f| f.names)
            .rev()
        {
            if let Some(results) = wild_contains(&mods_copy, &nearstart) {
                // push to start of mods
                for r in results {
                    let index = mods_copy.iter().position(|f| f == &r).unwrap();
                    let element = mods_copy.remove(index);
                    mods_copy.insert(0, element);
                }
            }
        }

        // nearend rules
        for nearend in order_rules
            .iter()
            .filter_map(nearend2)
            .flat_map(|f| f.names)
            .rev()
        {
            if let Some(results) = wild_contains(&mods_copy, &nearend) {
                // push to end of mods
                for r in results {
                    let index = mods_copy.iter().position(|f| f == &r).unwrap();
                    let element = mods_copy.remove(index);
                    mods_copy.push(element);
                }
            }
        }

        let n = mods.len();

        let mut index = 0;

        edges.sort_by_key(|k| k.0);

        for i in 1..self.max_iterations {
            let any_change = self.stable_topo_sort_inner(
                n,
                &edges,
                &index_dict,
                &index_dict_rev,
                &mut mods_copy,
                &mut index,
            );

            // sort again
            if !any_change {
                // sort esms now?
                if game == ESupportedGame::Morrowind || game == ESupportedGame::Openmw {
                    // put all items in mods_copy ending with .esm at the start
                    let mut esms = vec![];
                    for (i, m) in mods_copy.iter().enumerate() {
                        if m.ends_with(".esm") || m.ends_with(".omwgame") {
                            esms.push(i);
                        }
                    }
                    // now sort the mods_copy list
                    for (last_i, i) in esms.iter().enumerate() {
                        let element = mods_copy.remove(*i);
                        mods_copy.insert(last_i, element);
                    }

                    // put standard tes3 esms at the start
                    // if mods_copy.contains(&"bloodmoon.esm".into()) {
                    //     let index = mods_copy.iter().position(|f| f == "bloodmoon.esm").unwrap();
                    //     let element = mods_copy.remove(index);
                    //     mods_copy.insert(0, element);
                    // }

                    // if mods_copy.contains(&"tribunal.esm".into()) {
                    //     let index = mods_copy.iter().position(|f| f == "tribunal.esm").unwrap();
                    //     let element = mods_copy.remove(index);
                    //     mods_copy.insert(0, element);
                    // }

                    if mods_copy.contains(&"morrowind.esm".into()) {
                        let index = mods_copy.iter().position(|f| f == "morrowind.esm").unwrap();
                        let element = mods_copy.remove(index);
                        mods_copy.insert(0, element);
                    }
                }

                // Return the sorted vector
                // map sorted index back to mods
                let mut result = vec![];
                for lower_case_name in mods_copy {
                    let idx = index_dict[&lower_case_name.clone()];
                    result.push(mod_map[&idx].to_owned());
                }
                return Ok(result);
            }

            if let Some(edge) = edges.get(index) {
                let resolved_0 = &index_dict_rev[&edge.0];
                let resolved_1 = &index_dict_rev[&edge.1];
                log::debug!("{}, index {} ({}, {})", i, index, resolved_0, resolved_1);
            } else {
                log::debug!("{}, index {}", i, index);
            }
        }

        log::error!("Out of iterations");
        Err("Out of iterations")
    }


    pub fn topo_sort2(
        &mut self,
        game: ESupportedGame,
        mods_cased: &[&PluginData],
        parser: &Parser,
    ) -> Result<Vec<String>, &'static str> {
        // early out
        if parser.order_rules.is_empty() {
            log::info!("No order rules found, nothing to sort");
            return Err("No order rules found");
        }

        let sorter_graph = SorterGraph::new(parser, mods_cased);
        let order_rules = &parser.order_rules;
        let warn_rules = &parser.warning_rules;
        // build hashmaps for lookup
        // first map lowercase to cased, this is kinda dumb, but our input is small enough that I don't care about the memory hit
        // let mut mods: Vec<String> = vec![];
        

        // let mut index_dict: HashMap<String, usize> = HashMap::new();
        // let mut index_dict_rev: HashMap<usize, String> = HashMap::default();
        // let mut mod_map: HashMap<usize, String> = HashMap::default();
        // for (i, cased_name) in mods_cased.iter().enumerate() {
        //     let lower_case = cased_name.name.to_lowercase();

        //     index_dict.insert(lower_case.clone(), i);
        //     index_dict_rev.insert(i, lower_case.clone());

        //     mod_map.insert(i, cased_name.name.to_owned());
        //     mods.push(lower_case.to_owned());
        // }


        // add edges from order rules
        // let order_pairs = get_ordering_from_order_rules(order_rules);
        // let mut edges: Vec<(usize, usize)> = vec![];
        // for (a, b) in order_pairs {
        //     if let (Some(results_for_a), Some(results_for_b)) 
        //         = (wild_contains(&mods, &a), wild_contains(&mods, &b)) 
        //     {
        //             // foreach esp i, add an edge to all esps j
        //         for i in &results_for_a {
        //             for j in &results_for_b {
        //                 if i == j {
        //                     warn!("Skipping circular edge: {}", i);
        //                     continue;
        //                 }
        //                 let idx_a = index_dict[i.as_str()];
        //                 let idx_b = index_dict[j.as_str()];

        //                 if !edges.contains(&(idx_a, idx_b)) {
        //                     edges.push((idx_a, idx_b));
        //                 }
        //             }
        //         }
        //     }
        // }

        // create graph from edges
        let mut g: StableGraph<&String, ()> = StableGraph::with_capacity(mods_cased.len(), sorter_graph.edges.len());
        for plugin in mods_cased.iter() {
            g.add_node(&plugin.name);
        }
        // add edges
        for (a,b) in sorter_graph.edges {
            g.add_edge(NodeIndex::new(a), NodeIndex::new(b), ());
        }

        // TODO: integrate from this point downwards

        // cycle check
        if self.sort_type == ESortType::Unstable {
            let s = petgraph::algo::toposort(&g, None);
            let sort;
            if let Ok(result) = s {
                sort = result;

                // debug print to file
                let mut res = vec![];
                for idx in &sort {
                    res.push(idx.index());
                }
                let _ = std::fs::create_dir_all("tmp");
                let file = std::fs::File::create("tmp/toposort.json").expect("file create failed");
                serde_json::to_writer_pretty(file, &res).expect("serialize failed");
            } else {
                {
                    let viz = Dot::with_config(&g, &[Config::EdgeNoLabel]);
                    // write to file
                    let _ = std::fs::create_dir_all("tmp");
                    let mut file =
                        std::fs::File::create("tmp/graphviz.dot").expect("file create failed");
                    std::io::Write::write_all(&mut file, format!("{:?}", viz).as_bytes())
                        .expect("write failed");
                }

                // kosaraju_scc
                {
                    let scc = petgraph::algo::kosaraju_scc(&g);
                    let mut res: Vec<Vec<&String>> = vec![];
                    for er in &scc {
                        if er.len() > 1 {
                            warn!("cycles:");
                            let mut cycle = vec![];
                            for e in er {
                                // lookup name
                                let name = &mods_cased[e.index()].name;
                                warn!("\t{}: {}", e.index(), name);
                                cycle.push(name);
                            }
                            res.push(cycle);
                        }
                    }
                    // debug print to file
                    if !res.is_empty() {
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/kosaraju_scc.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &res).expect("serialize failed");
                    }
                }

                // tarjan_scc
                {
                    let scc = petgraph::algo::tarjan_scc(&g);
                    let mut res: Vec<Vec<&String>> = vec![];
                    for er in &scc {
                        if er.len() > 1 {
                            warn!("cycles:");
                            let mut cycle = vec![];
                            for e in er {
                                // lookup name
                                let name = &mods_cased[e.index()].name;
                                warn!("\t{}: {}", e.index(), name);
                                cycle.push(name);
                            }
                            res.push(cycle);
                        }
                    }
                    // debug print to file
                    if !res.is_empty() {
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/tarjan_scc.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &res).expect("serialize failed");

                        // find all rules that are part of a cycle
                        let mut cycle_rules = vec![];
                        for cycle in &res {
                            for rule in order_rules {
                                // switch
                                let mut names = vec![];
                                if let Some(nearstart) = nearstart2(rule) {
                                    names.push(nearstart.names);
                                } else if let Some(nearend) = nearend2(rule) {
                                    names.push(nearend.names);
                                } else if let Some(order) = order2(rule.clone()) {
                                    names.push(order.names);
                                }

                                // check that the names contain at least 2 mods
                                let mut found = 0;
                                for name in &names {
                                    for n in name {
                                        if cycle.contains(&n) {
                                            found += 1;
                                        }
                                    }
                                }
                                if found > 1 {
                                    cycle_rules.push(rule.clone());
                                }
                            }
                        }

                        // print cycle rules to file
                        let _ = std::fs::create_dir_all("tmp");
                        let file = std::fs::File::create("tmp/cycle_rules.json")
                            .expect("file create failed");
                        serde_json::to_writer_pretty(file, &cycle_rules).expect("serialize failed");
                    }
                }

                return Err("Graph contains a cycle");
            }

            // map sorted index back to mods
            let mut result = vec![];
            for idx in sort {
                result.push(mods_cased[idx.index()].name.clone());
            }
            return Ok(result);
        }

        // sort
        let mods: Vec<String> = sorter_graph.node_indices.into_keys().collect();
        let mut mods_copy: Vec<String> = sorter_graph.node_indices.into_keys().collect();

        // nearstart rules
        for nearstart in order_rules
            .iter()
            .filter_map(nearstart2)
            .flat_map(|f| f.names)
            .rev()
        {
            if let Some(results) = wild_contains(&mods_copy, &nearstart) {
                // push to start of mods
                for r in results {
                    let index = mods_copy.iter().position(|f| f == &r).unwrap();
                    let element = mods_copy.remove(index);
                    mods_copy.insert(0, element);
                }
            }
        }

        // nearend rules
        for nearend in order_rules
            .iter()
            .filter_map(nearend2)
            .flat_map(|f| f.names)
            .rev()
        {
            if let Some(results) = wild_contains(&mods_copy, &nearend) {
                // push to end of mods
                for r in results {
                    let index = mods_copy.iter().position(|f| f == &r).unwrap();
                    let element = mods_copy.remove(index);
                    mods_copy.push(element);
                }
            }
        }

        let n = mods.len();

        let mut index = 0;

        edges.sort_by_key(|k| k.0);

        for i in 1..self.max_iterations {
            let any_change = self.stable_topo_sort_inner(
                n,
                &edges,
                &index_dict,
                &index_dict_rev,
                &mut mods_copy,
                &mut index,
            );

            // sort again
            if !any_change {
                // sort esms now?
                if game == ESupportedGame::Morrowind || game == ESupportedGame::Openmw {
                    // put all items in mods_copy ending with .esm at the start
                    let mut esms = vec![];
                    for (i, m) in mods_copy.iter().enumerate() {
                        if m.ends_with(".esm") || m.ends_with(".omwgame") {
                            esms.push(i);
                        }
                    }
                    // now sort the mods_copy list
                    for (last_i, i) in esms.iter().enumerate() {
                        let element = mods_copy.remove(*i);
                        mods_copy.insert(last_i, element);
                    }

                    // put standard tes3 esms at the start
                    // if mods_copy.contains(&"bloodmoon.esm".into()) {
                    //     let index = mods_copy.iter().position(|f| f == "bloodmoon.esm").unwrap();
                    //     let element = mods_copy.remove(index);
                    //     mods_copy.insert(0, element);
                    // }

                    // if mods_copy.contains(&"tribunal.esm".into()) {
                    //     let index = mods_copy.iter().position(|f| f == "tribunal.esm").unwrap();
                    //     let element = mods_copy.remove(index);
                    //     mods_copy.insert(0, element);
                    // }

                    if mods_copy.contains(&"morrowind.esm".into()) {
                        let index = mods_copy.iter().position(|f| f == "morrowind.esm").unwrap();
                        let element = mods_copy.remove(index);
                        mods_copy.insert(0, element);
                    }
                }

                // Return the sorted vector
                // map sorted index back to mods
                let mut result = vec![];
                for lower_case_name in mods_copy {
                    let idx = index_dict[&lower_case_name.clone()];
                    result.push(mod_map[&idx].to_owned());
                }
                return Ok(result);
            }

            if let Some(edge) = edges.get(index) {
                let resolved_0 = &index_dict_rev[&edge.0];
                let resolved_1 = &index_dict_rev[&edge.1];
                log::debug!("{}, index {} ({}, {})", i, index, resolved_0, resolved_1);
            } else {
                log::debug!("{}, index {}", i, index);
            }
        }

        log::error!("Out of iterations");
        Err("Out of iterations")
    }

    pub fn stable_topo_sort_inner(
        &self,
        n: usize,
        edges: &[(usize, usize)],
        index_dict: &HashMap<String, usize>,
        index_dict_rev: &HashMap<usize, String>,
        result: &mut Vec<String>,
        last_index: &mut usize,
    ) -> bool {
        let was_changed = match self.sort_type {
            ESortType::Unstable => panic!("not supported"),
            ESortType::StableOpt => {
                Self::stable_topo_sort_opt2(n, edges, index_dict_rev, result, last_index)
            }
            ESortType::StableFull => {
                Self::stable_topo_sort_full(n, edges, index_dict, result, last_index)
            }
        };

        // check if it is fine regardless of sorting
        if was_changed {}

        was_changed
    }

    pub fn stable_topo_sort_full(
        n: usize,
        edges: &[(usize, usize)],
        index_dict: &HashMap<String, usize>,
        result: &mut Vec<String>,
        last_index: &mut usize,
    ) -> bool {
        for i in 0..n {
            for j in 0..i {
                let x = index_dict[result[i].as_str()];
                let y = index_dict[result[j].as_str()];
                if edges.contains(&(x, y)) {
                    let t = result[i].to_owned();
                    result.remove(i);
                    result.insert(j, t);

                    *last_index = j;

                    return true;
                }
            }
        }
        false
    }

    pub fn stable_topo_sort_opt2(
        _n: usize,
        edges: &[(usize, usize)],
        index_dict_rev: &HashMap<usize, String>,
        result: &mut Vec<String>,
        last_index: &mut usize,
    ) -> bool {
        // optimize B: only check edges
        let mut b = false;
        for (idx, edge) in edges.iter().enumerate() {
            let i = edge.0;
            let j = edge.1;

            let x = &index_dict_rev[&i];
            let y = &index_dict_rev[&j];

            let idx_of_x = result.iter().position(|f| f == x).unwrap();
            let idx_of_y = result.iter().position(|f| f == y).unwrap();

            // if i not before j x should be before y
            if idx_of_x > idx_of_y {
                let t = result[idx_of_x].to_owned();
                result.remove(idx_of_x);
                result.insert(idx_of_y, t);

                *last_index = idx;

                b = true;

                // logging
                log::debug!("\t{}: {} -> {}: {}", idx_of_x, x, idx_of_y, y);
            }
        }

        b
    }
}
