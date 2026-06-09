/-
CSV CLI — Parse example CSV files and display results.
-/
import Parser
import Query

open CsvParser
open CsvQuery

def processFile (path : String) : IO Unit := do
  let content ← IO.FS.readFile path
  match parse content with
  | .error msg => IO.eprintln s!"  FAIL: {path}: {msg}"
  | .ok file =>
    IO.println s!"  {path}: {file.header.length} cols, {file.rows.length} rows"
    for row in file.rows.take 5 do
      IO.println s!"    {String.intercalate " | " row}"

def main : IO Unit := do
  IO.println "=== CSV Parser CLI ===\n"
  processFile "examples/example1.csv"
  IO.println "\nDone!"
