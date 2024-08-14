/* CLI */

use algorithm_w::mutual_recursion::{elaborate, Program, ProgramTypes};

fn main() {
  match do_cli() {
    Ok(types) => {
      println!("{types}");
    }
    Err(e) => {
      eprintln!("{e}");
    }
  }
}

fn do_cli() -> Result<ProgramTypes, String> {
  // First argument is the file to parse.
  let mut args = std::env::args();
  args.next();
  let file = args.next().expect("missing file argument");

  // Read the file.
  let contents = std::fs::read_to_string(file).expect("failed to read file");

  // Parse the file.
  let program = contents.parse::<Program>()?;

  // Infer the types.
  let types = elaborate(program)?;
  Ok(types)
}
