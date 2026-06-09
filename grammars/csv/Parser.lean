/-
CSV Parser — Parses CSV token stream into structured records.
Grammar: grammars-v4/csv/CSV.g4

csvFile : hdr row+ EOF
hdr     : row
row     : field (',' field)* '\r'? '\n'
field   : TEXT | STRING | (empty)
-/
import LeanParser
import Lexer

open LeanParser
open PM
open CsvLexer

namespace CsvParser

-- ============================================================
-- AST
-- ============================================================

/-- A single field value. -/
abbrev Field : Type := String

/-- A row is a list of fields. -/
abbrev Row : Type := List Field

/-- A CSV file: header row + data rows. -/
structure CsvFile where
  header : Row
  rows   : List Row
deriving Repr, BEq

instance : ToString CsvFile where
  toString f :=
    let hdr := String.intercalate "," f.header
    let body := String.intercalate "\n" (f.rows.map fun r => String.intercalate "," r)
    s!"{hdr}\n{body}"

-- ============================================================
-- Parser
-- ============================================================

instance : Nonempty (PM α) := ⟨fun _ => .err "nonempty"⟩

def matchKind (expected : String) : PM String := do
  let kind ← peek
  if kind == expected then let text ← peekText; next; return text
  else fail s!"expected {expected}, got {kind}"

/-- Parse a non-empty field: TEXT or STRING. Advances past the token. -/
def parseFieldValue : PM Field := do
  let kind ← peek
  match kind with
  | "TEXT"   => matchKind "TEXT"
  | "STRING" => matchKind "STRING"
  | _        => fail s!"expected TEXT or STRING, got {kind}"

/-- Parse a row: field (',' field)* NL.
    Each comma is a separator. Empty field = nothing between two commas,
    or nothing between start-of-row and first comma, or last comma and NL. -/
partial def parseRow : PM Row := do
  -- First field: may be empty if row starts with comma
  let firstKind ← peek
  let firstField ← match firstKind with
    | "TEXT"   => parseFieldValue
    | "STRING" => parseFieldValue
    | ","      => pure ""
    | "NL"     => let _ ← matchKind "NL"; return [""]
    | "EOF"    => return []
    | _        => fail s!"unexpected start of row: {firstKind}"
  
  -- Remaining fields: each preceded by a comma
  let mut fields := [firstField]
  let mut done := false
  while !done do
    let kind ← peek
    match kind with
    | "," =>
      let _ ← matchKind ","
      let nextKind ← peek
      match nextKind with
      | "TEXT"   => do let val ← parseFieldValue; fields := fields ++ [val]
      | "STRING" => do let val ← parseFieldValue; fields := fields ++ [val]
      | ","      => fields := fields ++ [""]   -- empty field between commas
      | "NL"     => fields := fields ++ [""]   -- trailing empty field
      | "EOF"    => fields := fields ++ [""]   -- trailing empty field at EOF
      | _        => fail s!"unexpected after comma: {nextKind}"
    | "NL" =>
      let _ ← matchKind "NL"; done := true
    | "EOF" =>
      done := true
    | _ =>
      fail s!"expected comma or newline, got {kind}"
  
  return fields

/-- Parse a CSV file: header row then data rows then EOF. -/
def parseCsvFile : PM CsvFile := do
  let hdr ← parseRow
  let dataRows ← many (do
    let kind ← peek
    match kind with
    | "EOF" => fail "done"
    | _ => parseRow)
  return { header := hdr, rows := dataRows }

/-- Top-level parse: csvFile then EOF. -/
def parseDocument : PM CsvFile := do
  let file ← parseCsvFile
  let kind ← peek
  if kind == "EOF" then let _ ← matchKind "EOF"; return file
  else pure file

def parse (input : String) : Except String CsvFile :=
  let pairs := CsvLexer.tokenize input
  let tokens := pairs.map Prod.fst
  let kinds := pairs.map Prod.snd
  let ts := TokenStream.ofLists tokens kinds
  match parseDocument ts with
  | .ok val _ => .ok val
  | .err msg => .error msg

end CsvParser
