use std::fs::File;
use std::io;
use std::io::BufRead;
use std::path::Path;
use topological_sort::TopologicalSort;

#[derive(Default)]
pub struct Rules {
    pub order: Vec<(String, String)>,
}

// sort the strings according to pairs
pub fn topo_sort<S>(input: Vec<S>, rules: &Rules) -> Result<Vec<String>, &'static str>
where
    S: AsRef<str>,
{
    // Create a new TopologicalSort instance
    let mut sort = TopologicalSort::<&str>::new();

    // Add all the strings as items
    for s in &input {
        sort.insert(s.as_ref());
    }

    // Add all the pairs as dependencies
    for (a, b) in &rules.order {
        sort.add_dependency(a.as_ref(), b.as_ref());
    }

    // Sort the items and collect them into a vector
    let mut result: Vec<String> = Vec::new();
    while let Some(s) = sort.pop() {
        result.push(s.into());
    }

    if result.len() != input.len() {
        return Err("cycle detected");
    }

    // Return the sorted vector
    Ok(result)
}

// Returns an Iterator to the Reader of the lines of the file.
pub fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

// custom rules parser
pub fn parse_rules(rules_path: &str) -> Result<Rules, &'static str> {
    let mut rules: Rules = Rules::default();
    let mut order: Vec<(String, String)> = vec![];

    let mut orders: Vec<Vec<String>> = vec![];

    if let Ok(lines) = read_lines(rules_path) {
        let mut parsing = false;
        let mut current_order: Vec<String> = vec![];

        // Consumes the iterator, returns an (Optional) String
        for line_or_error in lines {
            if let Ok(line) = line_or_error {
                // parse each line
                if line.starts_with(';') {
                    continue;
                }

                // order parsing
                if parsing && line.is_empty() {
                    parsing = false;
                    orders.push(current_order.to_owned());
                    current_order.clear();
                    continue;
                }

                if !parsing && line == "[Order]" {
                    parsing = true;
                    // TODO set type
                    continue;
                }

                if parsing {
                    current_order.push(line);
                }
            }
        }
        orders.push(current_order.to_owned());

        // process orders
        for o in orders {
            if o.len() < 2 {
                continue;
            } else if o.len() == 2 {
                order.push((o[0].to_owned(), o[1].to_owned()));
            } else {
                // add all pairs
                for i in 0..o.len() - 1 {
                    order.push((o[i].to_owned(), o[i + 1].to_owned()));
                }
            }
        }

        // set data
        rules.order = order;

        Ok(rules)
    } else {
        Err("failed reading file")
    }
}

// read file line by line into vector
pub fn read_file_as_list(modlist_path: &str) -> Vec<String> {
    let mut result: Vec<String> = vec![];
    if let Ok(lines) = read_lines(modlist_path) {
        for line in lines {
            if let Ok(ip) = line {
                result.push(ip);
            }
        }
    }
    result
}