use log::info;
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::BufRead;
use std::io::{self};
use std::path::Path;
use toposort_scc::IndexGraph;

pub mod expressions;
pub mod parser;
pub mod rules;

use rules::*;

////////////////////////////////////////////////////////////////////////
/// LOGIC
////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Copy)]
pub enum ESupportedGame {
    Morrowind,
    OpenMorrowind,
    Cyberpunk,
}

pub fn stable_topo_sort_inner(
    n: usize,
    edges: &[(usize, usize)],
    index_dict: &HashMap<&str, usize>,
    result: &mut Vec<String>,
    last_index: &mut (usize, usize),
    optimize: bool,
) -> bool {
    match optimize {
        true => stable_topo_sort_opt(n, edges, index_dict, result, last_index),
        false => stable_topo_sort_full(n, edges, index_dict, result, last_index),
    }
}

pub fn stable_topo_sort_full(
    n: usize,
    edges: &[(usize, usize)],
    index_dict: &HashMap<&str, usize>,
    result: &mut Vec<String>,
    last_index: &mut (usize, usize),
) -> bool {
    for i in 0..n {
        for j in 0..i {
            let x = index_dict[result[i].as_str()];
            let y = index_dict[result[j].as_str()];
            if edges.contains(&(x, y)) {
                let t = result[i].to_owned();
                result.remove(i);
                result.insert(j, t);

                *last_index = (i, j);

                return true;
            }
        }
    }
    false
}

pub fn stable_topo_sort_opt(
    n: usize,
    edges: &[(usize, usize)],
    index_dict: &HashMap<&str, usize>,
    result: &mut Vec<String>,
    last_index: &mut (usize, usize),
) -> bool {
    // optimize: skip checking already sorted items
    let start = last_index.1;

    for i in start..n {
        for j in 0..i {
            let x = index_dict[result[i].as_str()];
            let y = index_dict[result[j].as_str()];
            if edges.contains(&(x, y)) {
                let t = result[i].to_owned();
                result.remove(i);
                result.insert(j, t);

                *last_index = (i, j);

                return true;
            }
        }
    }
    false
}

pub fn topo_sort(
    mods: &Vec<String>,
    order: &Vec<(String, String)>,
    optimize: bool,
) -> Result<Vec<String>, &'static str> {
    let mut g = IndexGraph::with_vertices(mods.len());
    let mut index_dict: HashMap<&str, usize> = HashMap::new();
    for (i, m) in mods.iter().enumerate() {
        index_dict.insert(m, i);
    }
    // add edges
    let mut edges: Vec<(usize, usize)> = vec![];
    for (a, b) in order {
        if mods.contains(a) && mods.contains(b) {
            let idx_a = index_dict[a.as_str()];
            let idx_b = index_dict[b.as_str()];
            g.add_edge(idx_a, idx_b);
            edges.push((idx_a, idx_b));
        }
    }
    // cycle check
    let sort = g.toposort();
    if sort.is_none() {
        return Err("Graph contains a cycle");
    }

    // sort
    let mut result: Vec<String> = mods.iter().map(|e| (*e).to_owned()).collect();
    info!("{result:?}");

    let mut index = (0, 0);
    loop {
        if !stable_topo_sort_inner(
            mods.len(),
            &edges,
            &index_dict,
            &mut result,
            &mut index,
            optimize,
        ) {
            break;
        }
        //error!("{},{}", index.0, index.1);
    }

    // Return the sorted vector
    Ok(result)
}

////////////////////////////////////////////////////////////////////////
/// HELPERS
////////////////////////////////////////////////////////////////////////

/// flattens a list of ordered mod pairs into a list of mod names
pub fn debug_get_mods_from_rules(order: &[(String, String)]) -> Vec<String> {
    let mut result: Vec<String> = vec![];
    for r in order.iter() {
        let mut a = r.0.to_owned();
        if !result.contains(&a) {
            result.push(a);
        }
        a = r.1.to_owned();
        if !result.contains(&a) {
            result.push(a);
        }
    }
    result
}

/// Gets a list of mod names from the game root folder
///
/// # Errors
///
/// This function will return an error if IO operations fail
pub fn gather_mods<P>(root: &P, game: ESupportedGame) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    match game {
        ESupportedGame::Morrowind => gather_tes3_mods(root),
        ESupportedGame::Cyberpunk => gather_cp77_mods(root),
        ESupportedGame::OpenMorrowind => gather_openmw_mods(root),
    }
}

pub fn gather_tes3_mods<P>(_root: &P) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    todo!();
}

pub fn gather_openmw_mods<P>(_root: &P) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    todo!();
}

pub fn gather_cp77_mods<P>(root: &P) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    // gather mods from archive/pc/mod
    let archive_path = root.as_ref().join("archive").join("pc").join("mod");

    let mut entries = fs::read_dir(archive_path)?
        .map(|res| res.map(|e| e.path()))
        .filter_map(Result::ok)
        .filter_map(|e| {
            if !e.is_dir() {
                if let Some(os_ext) = e.extension() {
                    if let Some(ext) = os_ext.to_ascii_lowercase().to_str() {
                        if ext.contains("archive") {
                            if let Some(file_name) = e.file_name().and_then(|n| n.to_str()) {
                                return Some(file_name.to_owned());
                            }
                        }
                    }
                }
            }
            None
        })
        .collect::<Vec<_>>();

    // TODO gather REDmods from mods/<NAME>
    entries.sort();

    Ok(entries)
}

/// Extracts a list of ordering-pairs from the order rules
pub fn get_order_rules(rules: &Vec<Rule>) -> Vec<(String, String)> {
    let mut order: Vec<(String, String)> = vec![];
    for r in rules {
        if let Rule::Order(o) = r {
            order.push((o.name_a.to_owned(), o.name_b.to_owned()));
        }
    }

    order
}

////////////////////////////////////////////////////////////////////////
/// MISC HELPERS
////////////////////////////////////////////////////////////////////////

/// Returns an Iterator to the Reader of the lines of the file.
///
/// # Errors
///
/// This function will return an error if file io fails
pub fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

/// read file line by line into vector
pub fn read_file_as_list<P>(modlist_path: P) -> Vec<String>
where
    P: AsRef<Path>,
{
    let mut result: Vec<String> = vec![];
    if let Ok(lines) = read_lines(modlist_path) {
        for line in lines.flatten() {
            result.push(line);
        }
    }
    result
}
