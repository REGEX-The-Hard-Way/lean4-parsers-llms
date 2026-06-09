import Lexer
import Parser
open GoParser

unsafe def main (args : List String) : IO Unit := do
  if args.length == 0 then IO.eprintln "Usage: parse-one <file.go>"; return
  let fname := args.head!
  let content ← IO.FS.readFile fname
  match parse content with
  | .error msg => IO.eprintln s!"FAIL {fname}: {msg}"
  | .ok _ => IO.println s!"OK {fname}"
