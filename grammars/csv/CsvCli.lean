import Parser
open CsvParser

unsafe def main (args : List String) : IO Unit := do
  let mut fname := "examples/example1.csv"  -- default
  -- Try to read fname from args
  let mut gotFile := false
  for a in args do
    if !a.startsWith "--" then fname := a; gotFile := true
  
  IO.println s!"CSV Parser — {fname}"
  let content ← IO.FS.readFile fname
  match parse content with
  | .error msg => IO.eprintln s!"Error: {msg}"
  | .ok file =>
    IO.println (String.intercalate "," file.header)
    for row in file.rows do
      IO.println (String.intercalate "," row)
    IO.eprintln s!"\n{file.rows.length} rows"
