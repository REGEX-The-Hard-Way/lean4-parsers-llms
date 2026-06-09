/-
Cypher Lexer — Procedural tokenizer for openCypher.
Grammar: grammars-v4/cypher/CypherLexer.g4
Features: case-insensitive keywords, multiple string types, line/block comments.
-/
import LeanParser

open LeanParser

namespace CypherLexer

inductive CypherToken where
  | kwCall | kwYield | kwFilter | kwExtract | kwCount | kwAny | kwNone | kwSingle | kwAll
  | kwAsc | kwAscending | kwBy | kwCreate | kwDelete | kwDesc | kwDescending | kwDetach
  | kwExists | kwLimit | kwMatch | kwMerge | kwOn | kwOptional | kwOrder | kwRemove
  | kwReturn | kwSet | kwSkip | kwWhere | kwWith | kwUnion | kwUnwind
  | kwAnd | kwAs | kwContains | kwDistinct | kwEnds | kwIn | kwIs | kwNot | kwOr
  | kwStarts | kwXor | kwFalse | kwTrue | kwNull
  | kwConstraint | kwDo | kwFor | kwRequire | kwUnique
  | kwCase | kwWhen | kwThen | kwElse | kwEnd | kwMandatory | kwScalar | kwOf
  | kwAdd | kwDrop
  | ident     : String → CypherToken
  | escIdent  : String → CypherToken
  | stringLit : String → CypherToken
  | charLit   : String → CypherToken
  | numberLit : String → CypherToken
  | semicolon | dot | comma | lparen | rparen | lbrace | rbrace | lbrack | rbrack
  | colon | stick | dollar | assign | addAssign | le | ge | gt | lt | notEqual | range
  | sub | plus | div_ | mod_ | caret | mult
  | eof
deriving Repr, BEq

-- Map lowercase keyword strings to token constructors
def kwmap : List (String × CypherToken) := [
  ("call", .kwCall), ("yield", .kwYield), ("filter", .kwFilter),
  ("extract", .kwExtract), ("count", .kwCount), ("any", .kwAny),
  ("none", .kwNone), ("single", .kwSingle), ("all", .kwAll),
  ("asc", .kwAsc), ("ascending", .kwAscending), ("by", .kwBy),
  ("create", .kwCreate), ("delete", .kwDelete), ("desc", .kwDesc),
  ("descending", .kwDescending), ("detach", .kwDetach),
  ("exists", .kwExists), ("limit", .kwLimit), ("match", .kwMatch),
  ("merge", .kwMerge), ("on", .kwOn), ("optional", .kwOptional),
  ("order", .kwOrder), ("remove", .kwRemove), ("return", .kwReturn),
  ("set", .kwSet), ("skip", .kwSkip), ("where", .kwWhere),
  ("with", .kwWith), ("union", .kwUnion), ("unwind", .kwUnwind),
  ("and", .kwAnd), ("as", .kwAs), ("contains", .kwContains),
  ("distinct", .kwDistinct), ("ends", .kwEnds), ("in", .kwIn),
  ("is", .kwIs), ("not", .kwNot), ("or", .kwOr),
  ("starts", .kwStarts), ("xor", .kwXor), ("false", .kwFalse),
  ("true", .kwTrue), ("null", .kwNull),
  ("constraint", .kwConstraint), ("do", .kwDo), ("for", .kwFor),
  ("require", .kwRequire), ("unique", .kwUnique),
  ("case", .kwCase), ("when", .kwWhen), ("then", .kwThen),
  ("else", .kwElse), ("end", .kwEnd), ("mandatory", .kwMandatory),
  ("scalar", .kwScalar), ("of", .kwOf), ("add", .kwAdd), ("drop", .kwDrop)
]

def lookupKw (s : String) : Option CypherToken :=
  let lower := s.toLower
  match kwmap.find? (fun (k, _) => k == lower) with
  | none => none
  | some (_, tok) => some tok

def CypherToken.toKind : CypherToken → String
  | .kwOn => "ON"  | .kwMatch => "MATCH" | .kwReturn => "RETURN" | .kwWhere => "WHERE"
  | .kwCreate => "CREATE" | .kwMerge => "MERGE" | .kwSet => "SET"
  | .kwDelete => "DELETE" | .kwDetach => "DETACH" | .kwRemove => "REMOVE"
  | .kwCall => "CALL" | .kwYield => "YIELD" | .kwWith => "WITH"
  | .kwUnwind => "UNWIND" | .kwOrder => "ORDER" | .kwBy => "BY"
  | .kwLimit => "LIMIT" | .kwSkip => "SKIP" | .kwOptional => "OPTIONAL"
  | .kwUnion => "UNION" | .kwAnd => "AND" | .kwOr => "OR" | .kwXor => "XOR"
  | .kwNot => "NOT" | .kwIn => "IN" | .kwIs => "IS" | .kwAs => "AS"
  | .kwTrue => "TRUE" | .kwFalse => "FALSE" | .kwNull => "NULL"
  | .kwDistinct => "DISTINCT" | .kwContains => "CONTAINS"
  | .kwStarts => "STARTS" | .kwEnds => "ENDS"
  | .kwExists => "EXISTS" | .kwCase => "CASE" | .kwWhen => "WHEN"
  | .kwThen => "THEN" | .kwElse => "ELSE" | .kwEnd => "END"
  | .kwCount => "COUNT" | .kwFilter => "FILTER" | .kwExtract => "EXTRACT"
  | .kwAll => "ALL" | .kwAny => "ANY" | .kwNone => "NONE" | .kwSingle => "SINGLE"
  | .kwAsc => "ASC" | .kwAscending => "ASCENDING"
  | .kwDesc => "DESC" | .kwDescending => "DESCENDING"
  | .kwConstraint => "CONSTRAINT" | .kwDo => "DO" | .kwFor => "FOR"
  | .kwRequire => "REQUIRE" | .kwUnique => "UNIQUE"
  | .kwMandatory => "MANDATORY" | .kwScalar => "SCALAR" | .kwOf => "OF"
  | .kwAdd => "ADD" | .kwDrop => "DROP"
  | .ident _ => "IDENT" | .escIdent _ => "ESC_IDENT"
  | .stringLit _ => "STRING" | .charLit _ => "CHAR"
  | .numberLit _ => "NUMBER"
  | .semicolon => ";" | .dot => "." | .comma => "," | .lparen => "("
  | .rparen => ")" | .lbrace => "{" | .rbrace => "}" | .lbrack => "["
  | .rbrack => "]" | .colon => ":" | .stick => "|" | .dollar => "$"
  | .assign => "=" | .addAssign => "+=" | .le => "<=" | .ge => ">="
  | .gt => ">" | .lt => "<" | .notEqual => "<>" | .range => ".."
  | .sub => "-" | .plus => "+" | .div_ => "/" | .mod_ => "%"
  | .caret => "^" | .mult => "*"
  | .eof => "EOF"

def CypherToken.toText : CypherToken → String
  | .ident s => s | .escIdent s => s | .stringLit s => s
  | .charLit s => s | .numberLit s => s
  | .kwOn => "ON" | .kwMatch => "MATCH" | .kwReturn => "RETURN" | .kwWhere => "WHERE"
  | .kwCreate => "CREATE" | .kwMerge => "MERGE" | .kwSet => "SET"
  | .kwDelete => "DELETE" | .kwDetach => "DETACH" | .kwRemove => "REMOVE"
  | .kwCall => "CALL" | .kwYield => "YIELD" | .kwWith => "WITH"
  | .kwUnwind => "UNWIND" | .kwOrder => "ORDER" | .kwBy => "BY"
  | .kwLimit => "LIMIT" | .kwSkip => "SKIP" | .kwOptional => "OPTIONAL"
  | .kwUnion => "UNION" | .kwAnd => "AND" | .kwOr => "OR" | .kwXor => "XOR"
  | .kwNot => "NOT" | .kwIn => "IN" | .kwIs => "IS" | .kwAs => "AS"
  | .kwTrue => "TRUE" | .kwFalse => "FALSE" | .kwNull => "NULL"
  | .kwDistinct => "DISTINCT" | .kwContains => "CONTAINS"
  | .kwStarts => "STARTS" | .kwEnds => "ENDS"
  | .kwExists => "EXISTS" | .kwCase => "CASE" | .kwWhen => "WHEN"
  | .kwThen => "THEN" | .kwElse => "ELSE" | .kwEnd => "END"
  | .kwCount => "COUNT" | .kwFilter => "FILTER" | .kwExtract => "EXTRACT"
  | .kwAll => "ALL" | .kwAny => "ANY" | .kwNone => "NONE" | .kwSingle => "SINGLE"
  | .kwAsc => "ASC" | .kwAscending => "ASCENDING"
  | .kwDesc => "DESC" | .kwDescending => "DESCENDING"
  | .kwConstraint => "CONSTRAINT" | .kwDo => "DO" | .kwFor => "FOR"
  | .kwRequire => "REQUIRE" | .kwUnique => "UNIQUE"
  | .kwMandatory => "MANDATORY" | .kwScalar => "SCALAR" | .kwOf => "OF"
  | .kwAdd => "ADD" | .kwDrop => "DROP"
  | .semicolon => ";" | .dot => "." | .comma => "," | .lparen => "("
  | .rparen => ")" | .lbrace => "{" | .rbrace => "}" | .lbrack => "["
  | .rbrack => "]" | .colon => ":" | .stick => "|" | .dollar => "$"
  | .assign => "=" | .addAssign => "+=" | .le => "<=" | .ge => ">="
  | .gt => ">" | .lt => "<" | .notEqual => "<>" | .range => ".."
  | .sub => "-" | .plus => "+" | .div_ => "/" | .mod_ => "%"
  | .caret => "^" | .mult => "*"
  | .eof => ""

-- Character predicates
def isWs (c : Char) : Bool := c == ' ' ∨ c == '\t' ∨ c == '\r' ∨ c == '\n'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isHexDigit (c : Char) : Bool := isDigit c ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')
def isLetter (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
def isIdentChar (c : Char) : Bool := isLetter c ∨ isDigit c ∨ c == '_'

-- Read a quoted string (single or double quote)
def readQuoted (quote : Char) (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '\\' :: c :: rest => go (c :: '\\' :: acc) rest
    | '\\' :: [] => (cs', '\\' :: acc)
    | c :: rest => if c == quote then (rest, acc) else go (c :: acc) rest
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read a backtick-quoted identifier
def readBacktick (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '`' :: rest => (rest, acc)
    | c :: rest => go (c :: acc) rest
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read an identifier or keyword
def readIdent (cs : List Char) : List Char × CypherToken :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest => if isIdentChar c then go (c :: acc) rest else (cs', acc)
  let (rest, chars) := go [] cs
  let name := String.ofList chars.reverse
  match lookupKw name with
  | some tok => (rest, tok)
  | none => (rest, .ident name)

-- Read a number
def readNumber (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest =>
      if isDigit c ∨ c == '.' ∨ c == 'x' ∨ c == 'X' ∨ c == 'e' ∨ c == 'E'
         ∨ c == '+' ∨ c == '-' ∨ c == '_'
         ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F') then
        go (c :: acc) rest
      else (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

partial def lex (s : String) : List CypherToken :=
  let chars := s.toList
  let rec go (cs : List Char) (acc : List CypherToken) : List CypherToken :=
    match cs with
    | [] => (.eof :: acc).reverse
    | c :: rest =>
      -- Whitespace: skip
      if isWs c then go rest acc
      -- Line comment
      else if c == '/' && rest.head? == some '/' then
        let rec skipLine (cs' : List Char) : List Char :=
          match cs' with
          | [] => cs' | '\n' :: r => r | _ :: r => skipLine r
        go (skipLine rest) acc
      -- Block comment
      else if c == '/' && rest.head? == some '*' then
        let rec skipBlock (cs' : List Char) : List Char :=
          match cs' with
          | [] => cs'
          | '*' :: '/' :: r => r
          | _ :: r => skipBlock r
        go (skipBlock rest) acc
      -- Operators (longest match first)
      else if c == '+' then
        if rest.head? == some '=' then go (rest.tail!) (.addAssign :: acc)
        else go rest (.plus :: acc)
      else if c == '<' then
        if rest.head? == some '=' then go (rest.tail!) (.le :: acc)
        else if rest.head? == some '>' then go (rest.tail!) (.notEqual :: acc)
        else go rest (.lt :: acc)
      else if c == '>' then
        if rest.head? == some '=' then go (rest.tail!) (.ge :: acc)
        else go rest (.gt :: acc)
      else if c == '.' then
        if rest.head? == some '.' then go (rest.tail!) (.range :: acc)
        else go rest (.dot :: acc)
      -- Single-char operators
      else if c == '=' then go rest (.assign :: acc)
      else if c == ';' then go rest (.semicolon :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == '{' then go rest (.lbrace :: acc)
      else if c == '}' then go rest (.rbrace :: acc)
      else if c == '[' then go rest (.lbrack :: acc)
      else if c == ']' then go rest (.rbrack :: acc)
      else if c == ':' then go rest (.colon :: acc)
      else if c == '|' then go rest (.stick :: acc)
      else if c == '$' then go rest (.dollar :: acc)
      else if c == '-' then go rest (.sub :: acc)
      else if c == '/' then go rest (.div_ :: acc)
      else if c == '%' then go rest (.mod_ :: acc)
      else if c == '^' then go rest (.caret :: acc)
      else if c == '*' then go rest (.mult :: acc)
      -- Strings
      else if c == '\"' then
        let (rest', s) := readQuoted '"' rest
        go rest' (.stringLit s :: acc)
      else if c == '\'' then
        let (rest', s) := readQuoted '\'' rest
        go rest' (.charLit s :: acc)
      else if c == '`' then
        let (rest', s) := readBacktick rest
        go rest' (.escIdent s :: acc)
      -- Numbers
      else if isDigit c then
        let (rest', s) := readNumber (c :: rest)
        go rest' (.numberLit s :: acc)
      -- Identifiers / keywords (may start with letter or underscore)
      else if isLetter c ∨ c == '_' then
        let (rest', tok) := readIdent (c :: rest)
        go rest' (tok :: acc)
      -- Skip unknown char (ERRCHAR -> hidden)
      else go rest acc
  go chars []

def tokenize (s : String) : List (String × String) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind))

end CypherLexer
