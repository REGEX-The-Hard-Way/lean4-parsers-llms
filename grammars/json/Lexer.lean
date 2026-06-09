import LeanParser

open LeanParser

namespace JsonLexer

inductive JsonToken where
  | lbrace | rbrace | lbracket | rbracket | colon | comma
  | stringLit : String → JsonToken
  | numberLit : String → JsonToken
  | kwTrue | kwFalse | kwNull
  | eof
deriving Repr, BEq

def JsonToken.toKind : JsonToken → String
  | .lbrace => "{" | .rbrace => "}" | .lbracket => "[" | .rbracket => "]"
  | .colon => ":" | .comma => ","
  | .stringLit _ => "STRING" | .numberLit _ => "NUMBER"
  | .kwTrue => "TRUE" | .kwFalse => "FALSE" | .kwNull => "NULL"
  | .eof => "EOF"

def JsonToken.toText : JsonToken → String
  | .lbrace => "{" | .rbrace => "}" | .lbracket => "[" | .rbracket => "]"
  | .colon => ":" | .comma => ","
  | .stringLit s => s | .numberLit s => s
  | .kwTrue => "true" | .kwFalse => "false" | .kwNull => "null"
  | .eof => ""

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

partial def lexJson (s : String) : List JsonToken :=
  let chars := s.toList
  let rec go (cs : List Char) (acc : List JsonToken) : List JsonToken :=
    match cs with
    | [] => (.eof :: acc).reverse
    | c :: rest =>
      if isWs c then go rest acc
      else if c == '{' then go rest (.lbrace :: acc)
      else if c == '}' then go rest (.rbrace :: acc)
      else if c == '[' then go rest (.lbracket :: acc)
      else if c == ']' then go rest (.rbracket :: acc)
      else if c == ':' then go rest (.colon :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == '"' then
        let rec readStr (cs' : List Char) (chars : List Char) : List Char × List Char :=
          match cs' with
          | [] => (cs', chars)
          | d :: rest' =>
            if d == '"' then (rest', chars)
            else if d == '\\' then
              match rest' with
              | e :: rest'' =>
                if e == 'u' then
                  match rest'' with
                  | _ :: _ :: _ :: _ :: rest5 => readStr rest5 (chars)
                  | _ => (rest', chars)
                else readStr rest'' (e :: chars)
              | [] => (rest', chars)
            else readStr rest' (d :: chars)
        let (rest', chars) := readStr rest []
        let strVal := String.ofList chars.reverse
        go rest' (.stringLit strVal :: acc)
      else if c == 't' then
        match rest with
        | 'r' :: 'u' :: 'e' :: rest4 => go rest4 (.kwTrue :: acc)
        | _ => go rest acc
      else if c == 'f' then
        match rest with
        | 'a' :: 'l' :: 's' :: 'e' :: rest5 => go rest5 (.kwFalse :: acc)
        | _ => go rest acc
      else if c == 'n' then
        match rest with
        | 'u' :: 'l' :: 'l' :: rest4 => go rest4 (.kwNull :: acc)
        | _ => go rest acc
      else if c == '-' || isDigit c then
        let rec readNum (cs' : List Char) (chars : List Char) : List Char × List Char :=
          match cs' with
          | [] => (cs', chars)
          | d :: rest' =>
            if isDigit d || d == '.' || d == 'e' || d == 'E' || d == '+' || d == '-' then
              readNum rest' (d :: chars)
            else (cs', chars)
        let (rest', chars) := readNum rest [c]
        let numVal := String.ofList chars.reverse
        go rest' (.numberLit numVal :: acc)
      else go rest acc
  go chars []

def tokenize (s : String) : List (String × String) :=
  let tokens := lexJson s
  tokens.map (fun t => (t.toText, t.toKind))

end JsonLexer
