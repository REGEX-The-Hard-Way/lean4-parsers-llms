import Lexer
import Parser
open GoParser

def main : IO Unit := do
  IO.println "=== Go Parser — Final Test ===\n"
  let tests : List (String × IO String) := [
    ("simple", pure "package main\nfunc f() {\n  return\n}"),
    ("call",   pure "package main\nimport \"fmt\"\nfunc main() {\n  fmt.Println(\"hello\")\n}"),
    ("vars",   pure "package main\nvar x int = 42\nvar y = \"hi\"\nconst Pi = 3.14"),
    ("ifelse", pure "package main\nfunc abs(x int) int {\n  if x > 0 {\n    return x\n  } else {\n    return -x\n  }\n}"),
    ("generics", IO.FS.readFile "examples/1_20_version.go")
  ]
  let mut ok := 0
  for (label, srcIO) in tests do
    let src ← srcIO
    match parse src with
    | .error msg => IO.eprintln s!"  FAIL: {label}: {msg}"
    | .ok _ => IO.println s!"  PASS: {label}"; ok := ok + 1
  IO.println s!"\n{ok}/{tests.length} passed"
  if ok != tests.length then IO.Process.exit 1
