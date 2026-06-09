import Parser
import Query
open CsvParser
open CsvQuery

def main : IO Unit := do
  let csv := "Name,Age,City\nAlice,30,NYC\nBob,25,LA\nCharlie,35,NYC\nDiana,28,SF"
  
  IO.println "=== CSV Query Demo ===\n"
  
  -- 1. Parse
  match parse csv with
  | .error e => IO.eprintln s!"Parse error: {e}"
  | .ok file =>
    IO.println s!"1. Original: {file.header} / {file.rows.length} rows"
    
    -- 2. Filter: only people in NYC
    let nyc := whereEq file "City" "NYC"
    IO.println s!"2. where City=NYC: {nyc.rows.length} rows"
    for r in nyc.rows do IO.println s!"   {r}"
    
    -- 3. Select only Name and Age columns
    let slim := selectCols file ["Name", "Age"]
    IO.println s!"\n3. Select Name,Age: {slim.header}"
    for r in slim.rows do IO.println s!"   {r}"
    
    -- 4. Sort by Age
    let sorted := sortBy file "Age"
    IO.println s!"\n4. Sort by Age:"
    for r in sorted.rows.take 3 do IO.println s!"   {r}"
    
    -- 5. Filter by predicate: Age > 26
    let adults := filterRows file fun row =>
      let s := nth row 1  -- Age is column 1
      match s.toNat? with
      | some n => n > 26
      | none => false
    IO.println s!"\n5. Age > 26: {adults.rows.length} rows"
    for r in adults.rows do IO.println s!"   {r}"
    
    -- 6. Chained: NYC residents sorted by Age, only Name column
    let result := file
      |> (fun f => whereEq f "City" "NYC")
      |> (fun f => sortBy f "Age")
      |> (fun f => selectCols f ["Name", "Age"])
    IO.println s!"\n6. NYC sorted by Age, Name+Age only:"
    for r in result.rows do IO.println s!"   {r}"
  
  IO.println "\nDone!"
