/-
CSV Test Suite — Tests against grammars-v4 example.
-/
import Lexer
import Parser

open CsvParser

namespace CsvTest

def assertParse (label : String) (input : String) (expected : CsvFile) : IO Bool :=
  match parse input with
  | .error msg => do IO.eprintln s!"  FAIL: {label}: {msg}"; return false
  | .ok val =>
    if val == expected then do IO.println s!"  PASS: {label}"; return true
    else do IO.eprintln s!"  FAIL: {label}: expected {repr expected}, got {repr val}"; return false

def testSimple : IO Bool :=
  assertParse "simple" "a,b,c\n1,2,3\n"
    { header := ["a","b","c"], rows := [["1","2","3"]] }

def testQuoted : IO Bool :=
  assertParse "quoted" "\"hello\",\"world\"\n"
    { header := ["hello","world"], rows := [] }

def testEmptyField : IO Bool :=
  assertParse "empty field" "a,,c\n"
    { header := ["a","","c"], rows := [] }

def testMultiRow : IO Bool :=
  assertParse "multi row" "x,y\n1,2\n3,4\n"
    { header := ["x","y"], rows := [["1","2"],["3","4"]] }

def testEscapedQuote : IO Bool :=
  assertParse "escaped quote" "\"a\"\"b\",c\n"
    { header := ["a\"b","c"], rows := [] }

def testExampleFile : IO Bool := do
  try
    let content ← IO.FS.readFile "examples/example1.csv"
    match parse content with
    | .error msg => do IO.eprintln s!"  FAIL: example1.csv: {msg}"; return false
    | .ok file => do
      IO.println s!"  PASS: example1.csv ({file.header.length} columns, {file.rows.length} rows)"
      return true
  catch e =>
    IO.eprintln s!"  FAIL: cannot read example1.csv: {e}"
    return false

def analyze (input : String) : IO Unit := do
  match parse input with
  | .error msg => IO.eprintln s!"Parse error: {msg}"
  | .ok file =>
    IO.println s!"Columns: {file.header.length}"
    IO.println s!"Header: {file.header}"
    IO.println s!"Rows: {file.rows.length}"
    let mut idx := 1
    for row in file.rows do
      IO.println s!"  Row {idx}: {row}"
      idx := idx + 1

def main : IO Unit := do
  IO.println "=== CSV Parser Test Suite ==="
  let tests : List (String × IO Bool) := [
    ("simple", testSimple),
    ("quoted", testQuoted),
    ("empty field", testEmptyField),
    ("multi row", testMultiRow),
    ("escaped quote", testEscapedQuote)
  ]
  let mut passed := 0
  let mut failed := 0
  for (label, test) in tests do
    IO.println s!"[{label}]"
    match ← test with
    | true => passed := passed + 1
    | false => failed := failed + 1

  IO.println "\n--- Example File ---"
  match ← testExampleFile with
  | true => passed := passed + 1
  | false => failed := failed + 1

  IO.println s!"\nResults: {passed + failed} tests, {passed} passed, {failed} failed"

  -- Show analysis of the example file
  IO.println "\n--- Example Analysis ---"
  try
    let content ← IO.FS.readFile "examples/example1.csv"
    analyze content
  catch e =>
    IO.eprintln s!"Cannot read: {e}"

  if failed > 0 then IO.Process.exit 1

end CsvTest

def main : IO Unit := CsvTest.main
