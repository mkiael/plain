use argh::FromArgs;

#[derive(FromArgs)]
/// file - The input file
struct Args {
    #[argh(positional)]
    file: String,
}

fn main() {
    let args: Args = argh::from_env();
    println!("Got file {}", args.file);
}
