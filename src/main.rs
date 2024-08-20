/* CLI */

use algorithm_w::mutual_recursion_adt as mr;
// use algorithm_w::recursion as r;
// use algorithm_w::simple as s;

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

use mr as mode;

fn do_cli() -> Result<mode::ProgramTypes, String> {
  // First argument is the file to parse.
  let mut args = std::env::args();
  args.next();
  let file = args.next().expect("missing file argument");

  // Read the file.
  let contents = std::fs::read_to_string(file).expect("failed to read file");

  // Parse the file.
  let program = contents.parse::<mode::Program>()?;

  // Infer the types.
  let types = mode::elaborate(program)?;
  Ok(types)
}
