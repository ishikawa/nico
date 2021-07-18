use nico::compiler;
use std::env;

fn main() {
    let command = compiler::Command::new();

    match command.run(env::args()) {
        Ok(output) => {
            print!("{}", output)
        }
        Err(err) => panic!("{}", err),
    };
}
