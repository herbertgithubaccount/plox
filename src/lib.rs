use clap::ValueEnum;
use log::error;
use std::env;
use std::fs::{self, File};
use std::io::BufRead;
use std::io::{self};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub mod expressions;
pub mod parser;
pub mod rules;
pub mod sorter;

use rules::*;

#[derive(Debug, Clone, Copy, ValueEnum, Default)]
pub enum ELogLevel {
    Trace,
    Debug,
    #[default]
    Info,
    Warn,
    Error,
}

pub fn log_level_to_str(level: ELogLevel) -> String {
    match level {
        ELogLevel::Trace => "trace".into(),
        ELogLevel::Debug => "debug".into(),
        ELogLevel::Info => "info".into(),
        ELogLevel::Warn => "warn".into(),
        ELogLevel::Error => "error".into(),
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ESupportedGame {
    Morrowind,
    OpenMorrowind,
    Cyberpunk,
}
pub const PLOX_RULES_BASE: &str = "plox_base.txt";

////////////////////////////////////////////////////////////////////////
/// GAMES
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

/// Gets the default rules dir for a game
///
/// # Panics
///
/// Panics if .
///
/// # Errors
///
/// This function will return an error if .
pub fn get_default_rules_dir(game: ESupportedGame) -> Result<PathBuf, ExitCode> {
    Ok(match game {
        ESupportedGame::Morrowind => {
            if let Some(parent_dir) = env::current_dir().expect("No current working dir").parent() {
                parent_dir.join("mlox")
            } else {
                error!("Could not find rules directory");
                return Err(ExitCode::FAILURE);
            }
        }
        ESupportedGame::OpenMorrowind => {
            if let Some(parent_dir) = env::current_dir().expect("No current working dir").parent() {
                parent_dir.join("mlox")
            } else {
                error!("Could not find rules directory");
                return Err(ExitCode::FAILURE);
            }
        }
        ESupportedGame::Cyberpunk => PathBuf::from("plox"),
    })
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

/// Get all plugins (esp, omwaddon, omwscripts) in a folder
fn get_plugins_in_folder<P>(path: &P, use_omw_plugins: bool) -> Vec<PathBuf>
where
    P: AsRef<Path>,
{
    // get all plugins
    let mut results: Vec<PathBuf> = vec![];
    if let Ok(plugins) = std::fs::read_dir(path) {
        plugins.for_each(|p| {
            if let Ok(file) = p {
                let file_path = file.path();
                if file_path.is_file() {
                    if let Some(ext_os) = file_path.extension() {
                        let ext = ext_os.to_ascii_lowercase();
                        if ext == "esm"
                            || ext == "esp"
                            || (use_omw_plugins && ext == "omwaddon")
                            || (use_omw_plugins && ext == "omwscripts")
                        {
                            results.push(file_path);
                        }
                    }
                }
            }
        });
    }
    results
}

pub fn get_plugins_sorted<P>(path: &P, use_omw_plugins: bool) -> Vec<PathBuf>
where
    P: AsRef<Path>,
{
    // get plugins
    let mut plugins = get_plugins_in_folder(path, use_omw_plugins);

    // sort
    plugins.sort_by(|a, b| {
        fs::metadata(a.clone())
            .expect("filetime")
            .modified()
            .unwrap()
            .cmp(
                &fs::metadata(b.clone())
                    .expect("filetime")
                    .modified()
                    .unwrap(),
            )
    });
    plugins
}

#[macro_use]
extern crate ini;

pub fn gather_tes3_mods<P>(path: &P) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    let files = get_plugins_sorted(&path, false);

    let names = files
        .iter()
        .filter_map(|f| {
            if let Some(file_name) = f.file_name().and_then(|n| n.to_str()) {
                return Some(file_name.to_owned());
            }
            None
        })
        .collect::<Vec<_>>();

    // check against mw ini
    // Move one directory up
    if let Some(parent_dir) = PathBuf::from(path.as_ref()).parent() {
        // Construct the path to "morrowind.ini"
        let morrowind_ini_path = parent_dir.join("Morrowind.ini");

        // Check if the file exists
        if morrowind_ini_path.exists() {
            // parse ini
            if let Some(path) = morrowind_ini_path.to_str() {
                let map = ini!(path);

                let mut final_files: Vec<String> = vec![];
                if let Some(section) = map.get("Game Files".to_lowercase().as_str()) {
                    let mods_in_ini = section
                        .values()
                        .flatten()
                        .map(|f| f.to_owned())
                        .collect::<Vec<_>>();

                    for plugin_name in names {
                        if mods_in_ini.contains(&plugin_name) {
                            final_files.push(plugin_name.to_owned());
                        }
                    }

                    return Ok(final_files);
                }
            }
        }
    }

    Ok(names)
}

pub fn gather_openmw_mods<P>(path: &P) -> io::Result<Vec<String>>
where
    P: AsRef<Path>,
{
    let files = get_plugins_sorted(&path, true);

    let names = files
        .iter()
        .filter_map(|f| {
            if let Some(file_name) = f.file_name().and_then(|n| n.to_str()) {
                return Some(file_name.to_owned());
            }
            None
        })
        .collect::<Vec<_>>();

    // TODO parse omw cfg

    Ok(names)
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
                            //return Some(e);
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
/// HELPERS
////////////////////////////////////////////////////////////////////////

pub fn is_current_directory_name(name_to_check: &str) -> bool {
    // Get the current directory
    if let Ok(current_dir) = env::current_dir() {
        // Extract the directory name
        if let Some(dir_name) = current_dir.file_name() {
            // Convert the directory name to a string
            if let Some(name) = dir_name.to_str() {
                return name == name_to_check;
            }
        }
    }

    false
}

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
