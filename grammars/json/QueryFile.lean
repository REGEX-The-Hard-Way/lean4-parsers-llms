import JsonParser
import Query
open JsonParser
open JsonQuery

partial def showTree (pre : String) (val : JsonValue) (deep : Bool) : IO Unit := do
  match val with
  | .object kvs =>
    for (k, v) in kvs do
      let lbl := pre ++ k
      match v with
      | .object sub => IO.println (lbl ++ " {" ++ toString sub.length ++ "}")
      | .array arr => IO.println (lbl ++ " [" ++ toString arr.length ++ "]")
      | .string s => IO.println (lbl ++ ": " ++ s)
      | .number n => IO.println (lbl ++ ": " ++ n)
      | .true_ => IO.println (lbl ++ ": true")
      | .false_ => IO.println (lbl ++ ": false")
      | .null_ => IO.println (lbl ++ ": null")
      if deep then
        match v with
        | .object _ => showTree (pre ++ "  ") v deep
        | _ => pure ()
  | .array arr => IO.println (pre ++ "[" ++ toString arr.length ++ " items]")
  | .string s => IO.println (pre ++ s)
  | .number n => IO.println (pre ++ n)
  | _ => pure ()

unsafe def main (args : List String) : IO Unit := do
  if args.length < 2 then
    IO.eprintln "Usage: query-file <file.json> [--keys] [--all] [--each N] [--count] [field ...]"
    return
  let fname := args.headD ""
  let mut showKeys := false
  let mut deep := false
  let mut showEach := false
  let mut eachN : Nat := 0
  let mut showCount := false
  let mut fieldPaths : List String := []

  let mut i := 1
  while i < args.length do
    let a := args.getD i ""
    if a == "--keys" then showKeys := true; i := i + 1
    else if a == "--all" then deep := true; i := i + 1
    else if a == "--count" then showCount := true; i := i + 1
    else if a == "--each" then
      showEach := true
      if i+1 < args.length then
        let next := args.getD (i+1) ""
        match next.toNat? with
        | some n => eachN := n; i := i + 1
        | none => pure ()
      i := i + 1
    else if !a.startsWith "--" then fieldPaths := fieldPaths ++ [a]; i := i + 1
    else i := i + 1

  let content ← IO.FS.readFile fname
  match parseAll content with
  | .error msg => IO.eprintln s!"FAIL: {msg}"
  | .ok values =>
    IO.println s!"{values.length} objects\n"

    -- Count types
    if showCount then
      let mut typeCounts : List (String × Nat) := []
      for v in values do
        let ty := match v with
          | .object kvs =>
            match kvs.find? (fun (k, _) => k == "type") with
            | some (_, .string s) => s | _ => "?"
          | _ => "?"
        -- Increment count (simple version)
        let mut found := false
        let mut newCounts : List (String × Nat) := []
        for (t, n) in typeCounts do
          if t == ty then
            newCounts := newCounts ++ [(t, n+1)]
            found := true
          else newCounts := newCounts ++ [(t, n)]
        if !found then newCounts := newCounts ++ [(ty, 1)]
        typeCounts := newCounts
      IO.println "Types:"
      for (t, n) in typeCounts do IO.println s!"  {t}: {n}"
      IO.println ""

    -- Show tree of first object
    if showKeys && !values.isEmpty then
      showTree "" (values.headD JsonValue.null_) deep
      IO.println ""

    -- Show each object
    if showEach then
      let limit := if eachN == 0 then values.length else minNat eachN values.length
      let mut n := 0
      for v in values do
        if n >= limit then break
        n := n + 1
        IO.println s!"--- Object {n} ---"
        for pathStr in fieldPaths do
          let hits := select (Selector.at (Path.ofString pathStr)) v []
          if hits.isEmpty then IO.eprintln (pathStr ++ ": NOT FOUND")
          else for h in hits do IO.println (pathStr ++ ": " ++ toString h.value)
        IO.println ""
    -- Show fields for first object only
    else if !fieldPaths.isEmpty then
      if values.length > 1 then
        IO.println s!"(showing first of {values.length} objects — use --each for all)"
        IO.println ""
      match values.head? with
      | some v =>
        for pathStr in fieldPaths do
          let hits := select (Selector.at (Path.ofString pathStr)) v []
          if hits.isEmpty then IO.eprintln (pathStr ++ ": NOT FOUND")
          else for h in hits do IO.println (toString h.value)
      | none => pure ()
where
  minNat (a b : Nat) : Nat := if a < b then a else b
