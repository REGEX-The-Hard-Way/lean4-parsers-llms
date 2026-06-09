/-
CSV Query Engine — Filter rows, select columns, search values.
-/
import Parser

open CsvParser

namespace CsvQuery

/-- Filter rows by a predicate on fields. -/
def filterRows (file : CsvFile) (pred : Row → Bool) : CsvFile :=
  { file with rows := file.rows.filter pred }

partial def nth (r : List String) (n : Nat) : String :=
  match r with | [] => "" | x :: xs => if n == 0 then x else nth xs (n-1)

/-- Select specific columns by name (header match). -/
def selectCols (file : CsvFile) (names : List String) : CsvFile :=
  let indices := names.filterMap fun n => file.header.findIdx? (fun h => h == n)
  let newHeader := indices.map fun i => nth file.header i
  let newRows := file.rows.map fun row =>
    indices.map fun i => nth row i
  { header := newHeader, rows := newRows }

/-- Drop columns by name. -/
def dropCols (file : CsvFile) (names : List String) : CsvFile :=
  let keep := file.header.filter (fun h => !(names.contains h))
  selectCols file keep

/-- Filter rows where a named column matches a value. -/
def whereEq (file : CsvFile) (col : String) (val : String) : CsvFile :=
  match file.header.findIdx? (fun h => h == col) with
  | none => { file with rows := [] }
  | some idx =>
    filterRows file fun row => nth row idx == val

/-- Limit to first n rows. -/
def take (file : CsvFile) (n : Nat) : CsvFile :=
  { file with rows := file.rows.take n }

/-- Sort rows by a named column. -/
def sortBy (file : CsvFile) (col : String) : CsvFile :=
  match file.header.findIdx? (fun h => h == col) with
  | none => file
  | some idx =>
    let sorted := file.rows.mergeSort (fun a b => nth a idx < nth b idx)
    { file with rows := sorted }

-- API
def parseAndQuery (input : String) : Except String CsvFile :=
  CsvParser.parse input

end CsvQuery
