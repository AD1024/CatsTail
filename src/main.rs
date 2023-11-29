use p4::{example_progs, p4ir::Table};

mod extractors;
mod language;
mod p4;
mod rewrites;
mod utils;

struct RunArgs {
    target: String,
    prog_name: String,
    rewrites: Vec<String>,
}

fn get_prog(name: String) -> Vec<Table> {
    match name.as_str() {
        "stateful-fw" => example_progs::stateful_fw(),
        "rcp" => example_progs::rcp(),
        "flowlet-switching" => example_progs::flowlet(),
        "blue-increase" => example_progs::blue_increase(),
        _ => panic!("No such program: {}", name),
    }
}

fn main() {}
