mod interpreter;
mod scanner;

use argh::FromArgs;
use std::fs::File;
use std::io::{Read, Result};

#[derive(FromArgs)]
/// file - The input file
struct Args {
    #[argh(positional)]
    file: String,
}

fn main() -> Result<()> {
    let args: Args = argh::from_env();
    let mut file = File::open(&args.file)?;

    let mut buffer = String::new();

    file.read_to_string(&mut buffer)?;

    match interpreter::interprete(&buffer) {
        Ok(value) => println!("{:?}", value),
        Err(e) => println!("Syntax error: {:?}", e),
    }

    Ok(())
}
