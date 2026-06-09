import LeanParser
import Lexer

open LeanParser
open PM
open JsonLexer

namespace JsonParser

inductive JsonValue where
  | string  : String → JsonValue
  | number  : String → JsonValue
  | object  : List (String × JsonValue) → JsonValue
  | array   : List JsonValue → JsonValue
  | true_   : JsonValue
  | false_  : JsonValue
  | null_   : JsonValue
deriving Repr, BEq

partial def JsonValue.toString : JsonValue → String
  | .string s => "\"" ++ s ++ "\""
  | .number s => s
  | .object kvs =>
    let inner := String.intercalate ", " (kvs.map fun (k, v) => "\"" ++ k ++ "\": " ++ JsonValue.toString v)
    "{" ++ inner ++ "}"
  | .array vs =>
    let inner := String.intercalate ", " (vs.map JsonValue.toString)
    "[" ++ inner ++ "]"
  | .true_ => "true" | .false_ => "false" | .null_ => "null"

instance : ToString JsonValue where
  toString := JsonValue.toString

instance : Nonempty (PM α) := ⟨fun _ => .err "nonempty"⟩

def matchKind (expected : String) : PM String := do
  let kind ← peek
  if kind == expected then let text ← peekText; next; return text
  else fail s!"expected {expected}, got {kind}"

mutual

partial def parseValue : PM JsonValue := do
  let kind ← peek
  match kind with
  | "STRING" => let s ← matchKind "STRING"; return JsonValue.string s
  | "NUMBER" => let s ← matchKind "NUMBER"; return JsonValue.number s
  | "{" => parseObject
  | "[" => parseArray
  | "TRUE" => next; return JsonValue.true_
  | "FALSE" => next; return JsonValue.false_
  | "NULL" => next; return JsonValue.null_
  | _ => fail s!"unexpected token: {kind}"

partial def parseObject : PM JsonValue := do
  let _ ← matchKind "{"
  let kind ← peek
  if kind == "}" then let _ ← matchKind "}"; return JsonValue.object []
  else do let pairs ← parseMembers; let _ ← matchKind "}"; return JsonValue.object pairs

partial def parseMembers : PM (List (String × JsonValue)) := do
  let first ← parsePair
  let rest ← many (do let _ ← matchKind ","; parsePair)
  return (first :: rest)

partial def parsePair : PM (String × JsonValue) := do
  let key ← matchKind "STRING"
  let _ ← matchKind ":"
  let val ← parseValue
  return (key, val)

partial def parseArray : PM JsonValue := do
  let _ ← matchKind "["
  let kind ← peek
  if kind == "]" then let _ ← matchKind "]"; return JsonValue.array []
  else do let vals ← parseElements; let _ ← matchKind "]"; return JsonValue.array vals

partial def parseElements : PM (List JsonValue) := do
  let first ← parseValue
  let rest ← many (do let _ ← matchKind ","; parseValue)
  return (first :: rest)

end

def parseJson : PM JsonValue := do
  let val ← parseValue
  let _ ← matchKind "EOF"
  return val

/-- Parse a single JSON value from token stream. -/
def parseOne (ts : TokenStream) : TokenStepResult JsonValue := parseJson ts

/-- Parse all JSON values until EOF (for NDJSON / line-delimited JSON). -/
partial def parseLines : PM (List JsonValue) := do
  let kind ← peek
  if kind == "EOF" then return [] else
    let val ← parseValue
    let rest ← parseLines
    return (val :: rest)

def parse (input : String) : Except String JsonValue :=
  let pairs := JsonLexer.tokenize input
  let tokens := pairs.map Prod.fst
  let kinds := pairs.map Prod.snd
  let ts := TokenStream.ofLists tokens kinds
  match parseJson ts with
  | .ok val _ => .ok val
  | .err msg => .error msg

/-- Parse all JSON objects from input (NDJSON). -/
def parseAll (input : String) : Except String (List JsonValue) :=
  let pairs := JsonLexer.tokenize input
  let tokens := pairs.map Prod.fst
  let kinds := pairs.map Prod.snd
  let ts := TokenStream.ofLists tokens kinds
  match parseLines ts with
  | .ok vals _ => .ok vals
  | .err msg => .error msg

end JsonParser
