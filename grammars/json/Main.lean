import JsonParser

def main : IO Unit := do
  IO.println "JSON Parser Test"
  match JsonParser.parse "42" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "true" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "\"hello\"" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "null" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "[]" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "[1,2,3]" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "{}" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  match JsonParser.parse "{\"a\":1}" with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok val => IO.println s!"OK: {val}"

  IO.println "Done!"
