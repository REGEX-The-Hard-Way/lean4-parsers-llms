import JsonParser
open JsonParser

unsafe def main (args : List String) : IO Unit := do
  if args.length == 0 then IO.eprintln "Usage: parse-file <file.json>"; return
  let content ← IO.FS.readFile args.head!
  IO.println s!"{content.length} bytes"
  match parse content with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok _ => IO.println "OK"
