import Lexer
open Antlr4Lexer

def main : IO Unit := do
  IO.println "=== ANTLR4 Lexer Test ==="
  let tests : List (String × String) := [
    ("Hello grammar", "grammar Hello;\nr : 'hello' ID;\nID : [a-z]+;\n"),
    ("Options", "grammar X;\noptions { language=Java; }\nr : 'x';\n")
  ]
  for (label, input) in tests do
    let tokens := tokenize input
    let kinds := String.intercalate " " (tokens.map Prod.snd)
    IO.println s!"[{label}]"
    IO.println s!"  Tokens: {kinds}"
    IO.println ""
  -- Parse example file
  IO.println "--- Hello.g4 ---"
  try
    let c ← IO.FS.readFile "examples/Hello.g4"
    let tokens := tokenize c
    IO.println s!"  Tokens ({tokens.length}): {String.intercalate " " (tokens.map Prod.snd)}"
  catch _ => IO.eprintln "  Cannot read file"
  IO.println "\nDone!"
