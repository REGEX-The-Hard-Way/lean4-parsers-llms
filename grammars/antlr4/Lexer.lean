import LeanParser
open LeanParser

namespace Antlr4Lexer

inductive Antlr4Token where
  | kwGrammar | kwLexer | kwParser | kwFragment | kwImport | kwMode
  | kwOptions | kwTokens | kwChannels | kwReturns | kwLocals | kwThrows
  | kwCatch | kwFinally | kwProtected | kwPublic | kwPrivate
  | colon | coloncolon | comma | semi | lparen | rparen | lbrace | rbrace
  | lbrack | rbrack | rarrow | lt | gt | assign | question | star
  | plusAssign | plus | or_ | dollar | range | dot | at | pound | not_
  | stringLit : String → Antlr4Token
  | intLit    : String → Antlr4Token
  | id        : String → Antlr4Token
  | action    : String → Antlr4Token
  | comment   : String → Antlr4Token
  | eof
deriving Repr, BEq

def Antlr4Token.toKind : Antlr4Token → String
  | .kwGrammar => "GRAMMAR" | .kwLexer => "LEXER" | .kwParser => "PARSER"
  | .kwFragment => "FRAGMENT" | .kwImport => "IMPORT" | .kwMode => "MODE"
  | .kwOptions => "OPTIONS" | .kwTokens => "TOKENS" | .kwChannels => "CHANNELS"
  | .kwReturns => "RETURNS" | .kwLocals => "LOCALS" | .kwThrows => "THROWS"
  | .kwCatch => "CATCH" | .kwFinally => "FINALLY"
  | .kwProtected => "PROTECTED" | .kwPublic => "PUBLIC" | .kwPrivate => "PRIVATE"
  | .colon => ":" | .coloncolon => "::" | .comma => "," | .semi => ";"
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .lbrack => "[" | .rbrack => "]" | .rarrow => "->"
  | .lt => "<" | .gt => ">" | .assign => "=" | .question => "?"
  | .star => "*" | .plusAssign => "+=" | .plus => "+" | .or_ => "|"
  | .dollar => "$" | .range => ".." | .dot => "." | .at => "@"
  | .pound => "#" | .not_ => "~"
  | .stringLit _ => "STRING_LITERAL" | .intLit _ => "INT" | .id _ => "ID"
  | .action _ => "ACTION" | .comment _ => "COMMENT" | .eof => "EOF"

def Antlr4Token.toText : Antlr4Token → String
  | .kwGrammar => "grammar" | .kwLexer => "lexer" | .kwParser => "parser"
  | .kwFragment => "fragment" | .kwImport => "import" | .kwMode => "mode"
  | .kwOptions => "options" | .kwTokens => "tokens" | .kwChannels => "channels"
  | .kwReturns => "returns" | .kwLocals => "locals" | .kwThrows => "throws"
  | .kwCatch => "catch" | .kwFinally => "finally"
  | .kwProtected => "protected" | .kwPublic => "public" | .kwPrivate => "private"
  | .colon => ":" | .coloncolon => "::" | .comma => "," | .semi => ";"
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .lbrack => "[" | .rbrack => "]" | .rarrow => "->"
  | .lt => "<" | .gt => ">" | .assign => "=" | .question => "?"
  | .star => "*" | .plusAssign => "+=" | .plus => "+" | .or_ => "|"
  | .dollar => "$" | .range => ".." | .dot => "." | .at => "@"
  | .pound => "#" | .not_ => "~"
  | .stringLit s => s | .intLit s => s | .id s => s
  | .action s => s | .comment s => s | .eof => ""

def isWs (c : Char) : Bool := c == ' ' ∨ c == '\t' ∨ c == '\r' ∨ c == '\n' ∨ c == '\x0c'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isLetter (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')

def kwmap : List (String × Antlr4Token) := [
  ("grammar", .kwGrammar), ("lexer", .kwLexer), ("parser", .kwParser),
  ("fragment", .kwFragment), ("import", .kwImport), ("mode", .kwMode),
  ("options", .kwOptions), ("tokens", .kwTokens), ("channels", .kwChannels),
  ("returns", .kwReturns), ("locals", .kwLocals), ("throws", .kwThrows),
  ("catch", .kwCatch), ("finally", .kwFinally),
  ("protected", .kwProtected), ("public", .kwPublic), ("private", .kwPrivate)
]

def lookupKw (s : String) : Option Antlr4Token :=
  match kwmap.find? (fun (k, _) => k == s) with
  | none => none
  | some (_, tok) => some tok

partial def readStringLit (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '\'' :: rest => (rest, acc)
    | '\\' :: c :: rest => go (c :: '\\' :: acc) rest
    | '\\' :: [] => (cs', '\\' :: acc)
    | c :: rest => go (c :: acc) rest
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

partial def readId (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest =>
      if isLetter c ∨ isDigit c ∨ c == '_' then go (c :: acc) rest
      else (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

partial def readInt (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest => if isDigit c then go (c :: acc) rest else (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

partial def readAction (cs : List Char) : List Char × String :=
  let rec go (depth : Nat) (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '{' :: rest => go (depth+1) ('{' :: acc) rest
    | '}' :: rest =>
      if depth == 1 then (rest, '}' :: acc)
      else go (depth-1) ('}' :: acc) rest
    | '\'' :: rest =>
      let rec takeStr (cnt : List Char) (cs'' : List Char) : List Char × List Char :=
        match cs'' with
        | [] => (cnt, cs'')
        | '\\' :: c :: r => takeStr (c :: '\\' :: cnt) r
        | '\'' :: r => ('\'' :: cnt, r)
        | c :: r => takeStr (c :: cnt) r
      let (strChars, rest') := takeStr ['\''] rest
      go depth (strChars ++ acc) rest'
    | '"' :: rest =>
      let rec takeDStr (cnt : List Char) (cs'' : List Char) : List Char × List Char :=
        match cs'' with
        | [] => (cnt, cs'')
        | '\\' :: c :: r => takeDStr (c :: '\\' :: cnt) r
        | '"' :: r => ('"' :: cnt, r)
        | c :: r => takeDStr (c :: cnt) r
      let (strChars, rest') := takeDStr ['"'] rest
      go depth (strChars ++ acc) rest'
    | '/' :: '*' :: rest =>
      let rec skipBlock (cs'' : List Char) : List Char :=
        match cs'' with
        | [] => cs''
        | '*' :: '/' :: r => r
        | _ :: r => skipBlock r
      let rest' := skipBlock rest
      go depth acc rest'
    | '/' :: '/' :: rest =>
      let rec skipLine (cs'' : List Char) : List Char :=
        match cs'' with
        | [] => cs''
        | '\n' :: r => r
        | _ :: r => skipLine r
      let rest' := skipLine rest
      go depth acc rest'
    | c :: rest => go depth (c :: acc) rest
  let (rest, chars) := go 1 [] cs
  (rest, String.ofList chars.reverse)

partial def lex (s : String) : List Antlr4Token :=
  let chars := s.toList
  let rec go (cs : List Char) (acc : List Antlr4Token) : List Antlr4Token :=
    match cs with
    | [] => (.eof :: acc).reverse
    | c :: rest =>
      if isWs c then go rest acc
      else if c == '/' && rest.head? == some '/' then
        let rec skipLine (cs' : List Char) : List Char :=
          match cs' with | [] => cs' | '\n' :: r => r | _ :: r => skipLine r
        let rest' := skipLine rest
        go rest' acc
      else if c == '/' && rest.head? == some '*' then
        let rec skipBlock (cs' : List Char) : List Char :=
          match cs' with | [] => cs' | '*' :: '/' :: r => r | _ :: r => skipBlock r
        let rest' := skipBlock rest
        go rest' acc
      else if c == ':' && rest.head? == some ':' then go (rest.tail!) (.coloncolon :: acc)
      else if c == '+' && rest.head? == some '=' then go (rest.tail!) (.plusAssign :: acc)
      else if c == '-' && rest.head? == some '>' then go (rest.tail!) (.rarrow :: acc)
      else if c == '.' && rest.head? == some '.' then go (rest.tail!) (.range :: acc)
      else if c == ':' then go rest (.colon :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == ';' then go rest (.semi :: acc)
      else if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == '{' then
        let (rest', s) := readAction rest
        go rest' (.action s :: acc)
      else if c == '}' then go rest (.rbrace :: acc)
      else if c == '[' then go rest (.lbrack :: acc)
      else if c == ']' then go rest (.rbrack :: acc)
      else if c == '<' then go rest (.lt :: acc)
      else if c == '>' then go rest (.gt :: acc)
      else if c == '=' then go rest (.assign :: acc)
      else if c == '?' then go rest (.question :: acc)
      else if c == '*' then go rest (.star :: acc)
      else if c == '+' then go rest (.plus :: acc)
      else if c == '|' then go rest (.or_ :: acc)
      else if c == '$' then go rest (.dollar :: acc)
      else if c == '@' then go rest (.at :: acc)
      else if c == '#' then go rest (.pound :: acc)
      else if c == '~' then go rest (.not_ :: acc)
      else if c == '\'' then
        let (rest', s) := readStringLit rest
        go rest' (.stringLit s :: acc)
      else if isDigit c then
        let (rest', s) := readInt (c :: rest)
        go rest' (.intLit s :: acc)
      else if isLetter c ∨ c == '_' then
        let (rest', s) := readId (c :: rest)
        match lookupKw s with
        | some tok => go rest' (tok :: acc)
        | none => go rest' (.id s :: acc)
      else go rest acc
  go chars []

def tokenize (s : String) : List (String × String) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind))

end Antlr4Lexer
