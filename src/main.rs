use clap::{Parser, Subcommand};
use log::{error, info};
use std::path::PathBuf;
use std::process::ExitCode;

use plox::*;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Verbose output
    #[arg(short, long)]
    verbose: bool,

    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Lists the current mod load order
    List {
        /// Root game folder ("Cyberpunk 2077"). Default is current working directory
        #[arg(default_value_t = String::from("./"))]
        root: String,
    },
    /// Sorts the current mod load order according to specified rules
    Sort {
        /// Root game folder ("Cyberpunk 2077"). Default is current working directory
        #[arg(default_value_t = String::from("./"))]
        root: String,

        /// Folder to read sorting rules from. Default is ./plox
        #[arg(short, long, default_value_t = String::from("./plox"))]
        rules_dir: String,

        /// Just print the suggested load order without sorting
        #[arg(short, long)]
        dry_run: bool,

        /// Read the input mods from a file instead of checking the root folder
        #[arg(short, long)]
        mod_list: Option<PathBuf>,
    },
    /// Verifies integrity of the specified rules
    Verify {
        /// Folder to read sorting rules from. Default is ./plox
        #[arg(short, long, default_value_t = String::from("./plox"))]
        rules_dir: String,
    },
}
const CARGO_NAME: &str = env!("CARGO_PKG_NAME");

fn main() -> ExitCode {
    let cli = Cli::parse();
    let _ = simple_logging::log_to_file(format!("{}.log", CARGO_NAME), log::LevelFilter::Debug);

    // TODO fix from cli
    let parser = plox::parser::Parser::new_cyberpunk_parser();

    match &cli.command {
        Some(Commands::List { root }) => list_mods(&root.into(), parser.game),
        Some(Commands::Verify { rules_dir }) => {
            let rules_path = PathBuf::from(rules_dir).join("plox_rules_base.txt");
            verify(&rules_path, &parser)
        }
        Some(Commands::Sort {
            root,
            rules_dir,
            mod_list,
            dry_run,
        }) => sort(&parser, &root.into(), &rules_dir.into(), mod_list, *dry_run),
        None => ExitCode::FAILURE,
    }
}

/// Sorts the current mod load order according to specified rules
fn sort(
    parser: &parser::Parser,
    root: &PathBuf,
    rules_path: &PathBuf,
    mod_list: &Option<PathBuf>,
    dry_run: bool,
) -> ExitCode {
    // gather mods (optionally from a list)
    let mods: Vec<String>;
    if let Some(modlist_path) = mod_list {
        mods = read_file_as_list(modlist_path);
    } else {
        match gather_mods(root, parser.game) {
            Ok(m) => mods = m,
            Err(e) => {
                info!("No mods found: {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    //TODO CLI
    let optimize = false;

    match parser.parse_rules_from_path(rules_path) {
        Ok(rules) => match topo_sort(&mods, &get_order_rules(&rules), optimize) {
            Ok(result) => {
                if dry_run {
                    info!("Dry run...");
                    info!("{result:?}");
                } else {
                    info!("Sorting mods...");
                    info!("{:?}", &mods);
                    info!("New:");
                    info!("{result:?}");

                    //todo!()
                }

                ExitCode::SUCCESS
            }
            Err(e) => {
                error!("error sorting: {e:?}");
                ExitCode::FAILURE
            }
        },
        Err(e) => {
            error!("error parsing file: {e:?}");
            ExitCode::FAILURE
        }
    }
}

/// Verifies integrity of the specified rules
fn verify(rules_path: &PathBuf, parser: &parser::Parser) -> ExitCode {
    //info!("Verifying rules from {} ...", rules_path.display());
    // TODO CLI
    let optimize = false;

    match parser.parse_rules_from_path(rules_path) {
        Ok(rules) => {
            let order = get_order_rules(&rules);
            let mods = debug_get_mods_from_rules(&order);
            match topo_sort(&mods, &order, optimize) {
                Ok(_) => {
                    info!("true");
                    ExitCode::SUCCESS
                }
                Err(_) => {
                    error!("false");
                    ExitCode::FAILURE
                }
            }
        }
        Err(e) => {
            error!("error parsing file: {e:?}");
            ExitCode::FAILURE
        }
    }
}

/// Lists the current mod load order
fn list_mods(root: &PathBuf, game: ESupportedGame) -> ExitCode {
    //info!("Printing active mods...");

    match gather_mods(root, game) {
        Ok(mods) => {
            for m in mods {
                info!("{}", m);
            }

            ExitCode::SUCCESS
        }
        _ => ExitCode::FAILURE,
    }
}
