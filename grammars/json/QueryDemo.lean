import Query

open JsonQuery

def main : IO Unit := do
  IO.println "=== JSON Query Engine Demo ===\n"

  let exampleFile := "examples/example1.json"
  let content ← IO.FS.readFile exampleFile
  let jsonStr := content

  -- 1. FIELD PATH EXTRACTION
  IO.println "--- 1. Field Path Extraction ---"
  IO.println "Path: glossary.GlossDiv.title"
  match atPath "glossary.GlossDiv.title" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nPath: glossary.GlossDiv.GlossList.GlossEntry.ID"
  match atPath "glossary.GlossDiv.GlossList.GlossEntry.ID" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  -- 2. PATH WILDCARDS
  IO.println "\n--- 2. Path Wildcards ---"
  IO.println "Path: glossary.*.title (all titles one level deep)"
  match atPath "glossary.*.title" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nPath: **.ID (any ID field at any depth)"
  match atPath "**.ID" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  -- 3. VALUE PATTERN MATCHING
  IO.println "\n--- 3. Value Pattern Matching ---"
  IO.println "Match: strings starting with 'S'"
  match findMatching (strPre "S") jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nMatch: strings containing 'Markup'"
  match findMatching (strHas "Markup") jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nMatch: values that are 'SGML' (exact)"
  match findMatching (strEq "SGML") jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  -- 4. RECURSIVE FIELD SEARCH
  IO.println "\n--- 4. Recursive Field Search ---"
  IO.println "Search: all 'title' fields at any depth"
  match findAll "title" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nSearch: all 'GlossSeeAlso' fields at any depth"
  match findAll "GlossSeeAlso" jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  -- 5. STRUCTURAL VALIDATION
  IO.println "\n--- 5. Structural Validation ---"
  let entrySchema : Schema := .objectOf [
    ("ID", .string),
    ("SortAs", .string),
    ("GlossTerm", .string),
    ("Acronym", .string),
    ("Abbrev", .string),
    ("GlossSee", .string)
  ]
  IO.println "Schema: object with fields ID, SortAs, GlossTerm, Acronym, Abbrev, GlossSee"
  match checkSchema entrySchema jsonStr with
  | .error e => IO.eprintln s!"  Schema mismatch (expected — not root object): {e}"
  | .ok _ => IO.println "  Valid (no errors)"

  -- Validate a simpler schema against the whole document
  let rootSchema : Schema := .objectOf [("glossary", .any)]
  IO.println "\nSchema: {glossary: any}"
  match checkSchema rootSchema jsonStr with
  | .error e => IO.eprintln s!"  Schema errors:\n{e}"
  | .ok _ => IO.println "  Valid"

  -- 6. COMBINED: selector composition
  IO.println "\n--- 6. Composed Selector ---"
  IO.println "Select: glossary.GlossDiv.allFields where value is a string containing 'S'"
  let s := .pipe (.at (Path.ofString "glossary.GlossDiv")) (.allFields)
  match query s jsonStr with
  | .error e => IO.eprintln s!"  Error: {e}"
  | .ok hits =>
    for h in hits do IO.println s!"  {h}"

  IO.println "\nDone!"
