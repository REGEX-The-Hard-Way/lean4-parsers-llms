/-
CSV Lexer — Procedural tokenizer for CSV files.
Grammar: grammars-v4/csv/CSV.g4

Tokens: TEXT (unquoted), STRING (double-quoted), comma, newline, EOF
Empty fields are implicit (adjacent commas).
-/
import LeanParser

open LeanParser

namespace CsvLexer

inductive CsvToken where
  | text      : String → CsvToken
  | stringLit : String → CsvToken
  | comma
  | newline
  | eof
deriving Repr, BEq

def CsvToken.toKind : CsvToken → String
  | .text _      => "TEXT"
  | .stringLit _ => "STRING"
  | .comma       => ","
  | .newline     => "NL"
  | .eof         => "EOF"

def CsvToken.toText : CsvToken → String
  | .text s      => s
  | .stringLit s => s
  | .comma       => ","
  | .newline     => "\n"
  | .eof         => ""

/-- Procedural CSV lexer. Handles text fields, quoted fields with escaped quotes, and empty fields. -/
partial def lex (s : String) : List CsvToken :=
  let chars := s.toList
  let rec go (cs : List Char) (acc : List CsvToken) : List CsvToken :=
    match cs with
    | [] => (.eof :: acc).reverse
    | c :: rest =>
      if c == ',' then go rest (.comma :: acc)
      else if c == '\n' then go rest (.newline :: acc)
      else if c == '\r' then
        -- Eat \r, optionally followed by \n
        match rest with
        | '\n' :: rest' => go rest' (.newline :: acc)
        | _ => go rest (.newline :: acc)
      else if c == '"' then
        -- Quoted field: read until unescaped closing quote
        let rec readQuoted (cs' : List Char) (chars : List Char) : List Char × List Char :=
          match cs' with
          | [] => (cs', chars)
          | '"' :: '"' :: rest' =>
            -- Escaped quote: "" -> "
            readQuoted rest' ('"' :: chars)
          | '"' :: rest' =>
            -- Closing quote
            (rest', chars)
          | d :: rest' =>
            readQuoted rest' (d :: chars)
        let (rest', chars) := readQuoted rest []
        let strVal := String.ofList chars.reverse
        go rest' (.stringLit strVal :: acc)
      else
        -- Unquoted text field: read until comma or newline
        let rec readText (cs' : List Char) (chars : List Char) : List Char × List Char :=
          match cs' with
          | [] => (cs', chars)
          | d :: rest' =>
            if d == ',' || d == '\n' || d == '\r' then (cs', chars)
            else readText rest' (d :: chars)
        let (rest', chars) := readText rest [c]
        let textVal := String.ofList chars.reverse
        go rest' (.text textVal :: acc)
  go chars []

/-- Tokenize and return parallel arrays for the PM parser. -/
def tokenize (s : String) : List (String × String) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind))

end CsvLexer
