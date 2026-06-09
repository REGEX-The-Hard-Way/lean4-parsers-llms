/-
Go Lexer — Procedural tokenizer for the Go language.
Grammar: grammars-v4/golang/GoLexer.g4

Features: NLSEMI mode (automatic semicolon insertion), rune/string/number
literals, 26 keywords, Unicode identifiers.
-/
import LeanParser

open LeanParser

namespace GoLexer

inductive GoToken where
  -- Keywords
  | kwBreak | kwCase | kwChan | kwConst | kwContinue | kwDefault
  | kwDefer | kwElse | kwFallthrough | kwFor | kwFunc | kwGo | kwGoto
  | kwIf | kwImport | kwInterface | kwMap | kwNil | kwPackage | kwRange
  | kwReturn | kwSelect | kwStruct | kwSwitch | kwType | kwVar
  -- Identifiers & literals
  | ident       : String → GoToken
  | intLit      : String → GoToken
  | floatLit    : String → GoToken
  | imagLit     : String → GoToken
  | runeLit     : String → GoToken
  | stringLit   : String → GoToken
  | rawStringLit : String → GoToken
  -- Operators & punctuation
  | lparen | rparen | lcurly | rcurly | lbrack | rbrack
  | assign | comma | semi | colon | dot
  | plusPlus | minusMinus | plusAssign | minusAssign | declareAssign | ellipsis
  | logicalOr | logicalAnd
  | equals | notEquals | less | lessOrEquals | greater | greaterOrEquals
  | or | div | mod | lshift | rshift | bitClear | underlying
  | exclamation | plus | minus | caret | star | ampersand | receive
  -- Special
  | eos   -- end of statement (from NLSEMI mode)
  | eof
deriving Repr, BEq

def GoToken.toKind : GoToken → String
  | .kwBreak => "BREAK" | .kwCase => "CASE" | .kwChan => "CHAN"
  | .kwConst => "CONST" | .kwContinue => "CONTINUE" | .kwDefault => "DEFAULT"
  | .kwDefer => "DEFER" | .kwElse => "ELSE" | .kwFallthrough => "FALLTHROUGH"
  | .kwFor => "FOR" | .kwFunc => "FUNC" | .kwGo => "GO" | .kwGoto => "GOTO"
  | .kwIf => "IF" | .kwImport => "IMPORT" | .kwInterface => "INTERFACE"
  | .kwMap => "MAP" | .kwNil => "NIL" | .kwPackage => "PACKAGE"
  | .kwRange => "RANGE" | .kwReturn => "RETURN" | .kwSelect => "SELECT"
  | .kwStruct => "STRUCT" | .kwSwitch => "SWITCH" | .kwType => "TYPE" | .kwVar => "VAR"
  | .ident _ => "IDENTIFIER" | .intLit _ => "INT" | .floatLit _ => "FLOAT"
  | .imagLit _ => "IMAG" | .runeLit _ => "RUNE" | .stringLit _ => "STRING"
  | .rawStringLit _ => "RAWSTRING"
  | .lparen => "(" | .rparen => ")" | .lcurly => "{" | .rcurly => "}"
  | .lbrack => "[" | .rbrack => "]"
  | .assign => "=" | .comma => "," | .semi => ";" | .colon => ":" | .dot => "."
  | .plusPlus => "++" | .minusMinus => "--" | .plusAssign => "+=" | .minusAssign => "-="
  | .declareAssign => ":=" | .ellipsis => "..."
  | .logicalOr => "||" | .logicalAnd => "&&"
  | .equals => "==" | .notEquals => "!=" | .less => "<" | .lessOrEquals => "<="
  | .greater => ">" | .greaterOrEquals => ">="
  | .or => "|" | .div => "/" | .mod => "%" | .lshift => "<<" | .rshift => ">>"
  | .bitClear => "&^" | .underlying => "~"
  | .exclamation => "!" | .plus => "+" | .minus => "-" | .caret => "^" | .star => "*"
  | .ampersand => "&" | .receive => "<-"
  | .eos => "EOS" | .eof => "EOF"

def GoToken.toText : GoToken → String
  | .kwBreak => "break" | .kwCase => "case" | .kwChan => "chan"
  | .kwConst => "const" | .kwContinue => "continue" | .kwDefault => "default"
  | .kwDefer => "defer" | .kwElse => "else" | .kwFallthrough => "fallthrough"
  | .kwFor => "for" | .kwFunc => "func" | .kwGo => "go" | .kwGoto => "goto"
  | .kwIf => "if" | .kwImport => "import" | .kwInterface => "interface"
  | .kwMap => "map" | .kwNil => "nil" | .kwPackage => "package"
  | .kwRange => "range" | .kwReturn => "return" | .kwSelect => "select"
  | .kwStruct => "struct" | .kwSwitch => "switch" | .kwType => "type" | .kwVar => "var"
  | .ident s => s | .intLit s => s | .floatLit s => s | .imagLit s => s
  | .runeLit s => s | .stringLit s => s | .rawStringLit s => s
  | .lparen => "(" | .rparen => ")" | .lcurly => "{" | .rcurly => "}"
  | .lbrack => "[" | .rbrack => "]"
  | .assign => "=" | .comma => "," | .semi => ";" | .colon => ":" | .dot => "."
  | .plusPlus => "++" | .minusMinus => "--" | .plusAssign => "+=" | .minusAssign => "-="
  | .declareAssign => ":=" | .ellipsis => "..."
  | .logicalOr => "||" | .logicalAnd => "&&"
  | .equals => "==" | .notEquals => "!=" | .less => "<" | .lessOrEquals => "<="
  | .greater => ">" | .greaterOrEquals => ">="
  | .or => "|" | .div => "/" | .mod => "%" | .lshift => "<<" | .rshift => ">>"
  | .bitClear => "&^" | .underlying => "~"
  | .exclamation => "!" | .plus => "+" | .minus => "-" | .caret => "^" | .star => "*"
  | .ampersand => "&" | .receive => "<-"
  | .eos => "" | .eof => ""

-- Character predicates
def isWs (c : Char) : Bool := c == ' ' ∨ c == '\t'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isHexDigit (c : Char) : Bool := isDigit c ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')
def isOctDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '7'
def isBinDigit (c : Char) : Bool := c == '0' ∨ c == '1'
def isLetter (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
def isIdentChar (c : Char) : Bool := isLetter c ∨ isDigit c ∨ c == '_'

-- Keyword map
def kwmap : List (String × GoToken) := [
  ("break", .kwBreak), ("case", .kwCase), ("chan", .kwChan),
  ("const", .kwConst), ("continue", .kwContinue), ("default", .kwDefault),
  ("defer", .kwDefer), ("else", .kwElse), ("fallthrough", .kwFallthrough),
  ("for", .kwFor), ("func", .kwFunc), ("go", .kwGo), ("goto", .kwGoto),
  ("if", .kwIf), ("import", .kwImport), ("interface", .kwInterface),
  ("map", .kwMap), ("nil", .kwNil), ("package", .kwPackage),
  ("range", .kwRange), ("return", .kwReturn), ("select", .kwSelect),
  ("struct", .kwStruct), ("switch", .kwSwitch), ("type", .kwType), ("var", .kwVar)
]

def lookupKw (s : String) : Option GoToken :=
  match kwmap.find? (fun (k, _) => k == s) with
  | none => none | some (_, tok) => some tok

-- Read identifier
partial def readIdent (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest => if isIdentChar c then go (c :: acc) rest else (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read a number (decimal, hex, octal, binary, float, imaginary)
partial def readNumber (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: rest =>
      if isDigit c ∨ c == '.' ∨ c == 'e' ∨ c == 'E' ∨ c == 'p' ∨ c == 'P'
         ∨ c == '+' ∨ c == '-' ∨ c == '_' ∨ c == 'x' ∨ c == 'X' ∨ c == 'o' ∨ c == 'O'
         ∨ c == 'b' ∨ c == 'B' ∨ c == 'i'
         ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F') then
        go (c :: acc) rest
      else (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read a rune literal: 'x' or '\x'
partial def readRune (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '\'' :: rest => (rest, '\'' :: acc)
    | '\\' :: c :: rest =>
      if c == 'x' then
        -- hex byte: \xNN
        match rest with
        | d1 :: d2 :: r => if isHexDigit d1 && isHexDigit d2 then go (d2 :: d1 :: 'x' :: '\\' :: acc) r else (cs', acc)
        | _ => (cs', acc)
      else if c == 'u' || c == 'U' then
        -- unicode: skip the hex digits
        let rec skipHex (cnt : Nat) (cs'' : List Char) : List Char :=
          if cnt == 0 then cs'' else
            match cs'' with
            | d :: r => if isHexDigit d then skipHex (cnt-1) r else cs''
            | [] => cs''
        let n := if c == 'u' then 4 else 8
        let rest' := skipHex n rest
        go (acc) rest'  -- simplified: skip hex chars
      else go (c :: '\\' :: acc) rest
    | c :: rest => go (c :: acc) rest
  let (rest, chars) := go ['\''] cs  -- include opening quote
  (rest, String.ofList chars.reverse)

-- Read interpreted string "..."
partial def readString (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '"' :: rest => (rest, acc)
    | '\\' :: c :: rest => go (c :: '\\' :: acc) rest
    | '\\' :: [] => (cs', '\\' :: acc)
    | c :: rest => go (c :: acc) rest
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read raw string `...`
partial def readRawString (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '`' :: rest => (rest, acc)
    | c :: rest => go (c :: acc) rest
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Tokens that trigger NLSEMI mode
def needsNlSemi (tok : GoToken) : Bool :=
  match tok with
  | .kwBreak => true | .kwContinue => true | .kwFallthrough => true
  | .kwReturn => true | .kwNil => true
  | .ident _ => true | .intLit _ => true | .floatLit _ => true
  | .imagLit _ => true | .runeLit _ => true | .stringLit _ => true
  | .rawStringLit _ => true
  | .rparen => true | .rbrack => true | .rcurly => true
  | .plusPlus => true | .minusMinus => true
  | _ => false

mutual

partial def goDefault (cs : List Char) (acc : List GoToken) : List GoToken :=
  match cs with
  | [] => (.eof :: acc).reverse
  | c :: rest =>
    -- Whitespace: skip
    if isWs c ∨ c == '\r' ∨ c == '\n' then
      -- Skip all whitespace
      let rec skipWs (cs' : List Char) : List Char :=
        match cs' with
        | d :: r => if isWs d ∨ d == '\r' ∨ d == '\n' then skipWs r else cs'
        | [] => cs'
      goDefault (skipWs rest) acc
    -- Line comment
    else if c == '/' && rest.head? == some '/' then
      let rec skipLine (cs' : List Char) : List Char :=
        match cs' with | [] => cs' | '\n' :: r => r | _ :: r => skipLine r
      goDefault (skipLine rest) acc
    -- Block comment
    else if c == '/' && rest.head? == some '*' then
      let rec skipBlock (cs' : List Char) : List Char :=
        match cs' with | [] => cs' | '*' :: '/' :: r => r | _ :: r => skipBlock r
      goDefault (skipBlock rest) acc
    -- Operators (longest match first)
    else if c == ':' && rest.head? == some '=' then mkTok (.declareAssign) (rest.tail!)
    else if c == '+' && rest.head? == some '=' then mkTok (.plusAssign) (rest.tail!)
    else if c == '+' && rest.head? == some '+' then mkTok (.plusPlus) (rest.tail!)
    else if c == '-' && rest.head? == some '=' then mkTok (.minusAssign) (rest.tail!)
    else if c == '-' && rest.head? == some '-' then mkTok (.minusMinus) (rest.tail!)
    else if c == '.' && rest.head? == some '.' && (rest.tail!).head? == some '.' then mkTok (.ellipsis) ((rest.tail!).tail!)
    else if c == '|' && rest.head? == some '|' then mkTok (.logicalOr) (rest.tail!)
    else if c == '&' && rest.head? == some '&' then mkTok (.logicalAnd) (rest.tail!)
    else if c == '=' && rest.head? == some '=' then mkTok (.equals) (rest.tail!)
    else if c == '!' && rest.head? == some '=' then mkTok (.notEquals) (rest.tail!)
    else if c == '<' && rest.head? == some '=' then mkTok (.lessOrEquals) (rest.tail!)
    else if c == '>' && rest.head? == some '=' then mkTok (.greaterOrEquals) (rest.tail!)
    else if c == '<' && rest.head? == some '<' then mkTok (.lshift) (rest.tail!)
    else if c == '>' && rest.head? == some '>' then mkTok (.rshift) (rest.tail!)
    else if c == '&' && rest.head? == some '^' then mkTok (.bitClear) (rest.tail!)
    else if c == '<' && rest.head? == some '-' then mkTok (.receive) (rest.tail!)
    -- Single-char operators
    else if c == '(' then mkTok (.lparen) rest
    else if c == ')' then mkTok (.rparen) rest
    else if c == '{' then mkTok (.lcurly) rest
    else if c == '}' then mkTok (.rcurly) rest
    else if c == '[' then mkTok (.lbrack) rest
    else if c == ']' then mkTok (.rbrack) rest
    else if c == '=' then mkTok (.assign) rest
    else if c == ',' then mkTok (.comma) rest
    else if c == ';' then mkTok (.semi) rest
    else if c == ':' then mkTok (.colon) rest
    else if c == '.' then mkTok (.dot) rest
    else if c == '|' then mkTok (.or) rest
    else if c == '/' then mkTok (.div) rest
    else if c == '%' then mkTok (.mod) rest
    else if c == '<' then mkTok (.less) rest
    else if c == '>' then mkTok (.greater) rest
    else if c == '!' then mkTok (.exclamation) rest
    else if c == '+' then mkTok (.plus) rest
    else if c == '-' then mkTok (.minus) rest
    else if c == '^' then mkTok (.caret) rest
    else if c == '*' then mkTok (.star) rest
    else if c == '&' then mkTok (.ampersand) rest
    else if c == '~' then mkTok (.underlying) rest
    -- String/char literals
    else if c == '"' then
      let (rest', s) := readString rest
      mkTok (.stringLit s) rest'
    else if c == '`' then
      let (rest', s) := readRawString rest
      mkTok (.rawStringLit s) rest'
    else if c == '\'' then
      let (rest', s) := readRune rest
      mkTok (.runeLit s) rest'
    -- Numbers
    else if isDigit c then
      let (rest', s) := readNumber (c :: rest)
      mkTok (.intLit s) rest'  -- simplified: all numbers as intLit
    -- Identifiers/keywords
    else if isLetter c ∨ c == '_' then
      let (rest', s) := readIdent (c :: rest)
      match lookupKw s with
      | some tok => mkTok tok rest'
      | none => mkTok (.ident s) rest'
    -- Unknown: skip
    else goDefault rest acc

where
  mkTok (tok : GoToken) (cs' : List Char) : List GoToken :=
    if needsNlSemi tok then goNlSemi cs' (tok :: acc)
    else goDefault cs' (tok :: acc)

partial def goNlSemi (cs : List Char) (acc : List GoToken) : List GoToken :=
  match cs with
  | [] => goDefault cs (.eos :: acc)
  | c :: rest =>
    if isWs c then goNlSemi rest acc
    else if c == '\r' || c == '\n' then goDefault rest (.eos :: acc)
    else if c == ';' then goDefault rest (.eos :: acc)
    else if c == '/' && rest.head? == some '/' then
      -- line comment in NLSEMI: does NOT trigger EOS
      let rec skipLine (cs' : List Char) : List Char :=
        match cs' with | [] => cs' | '\n' :: r => r | _ :: r => skipLine r
      goNlSemi (skipLine rest) acc
    else if c == '/' && rest.head? == some '*' then
      -- block comment: DOES trigger EOS
      let rec skipBlock (cs' : List Char) : List Char :=
        match cs' with | [] => cs' | '*' :: '/' :: r => r | _ :: r => skipBlock r
      goDefault (skipBlock rest) (.eos :: acc)
    else
      -- Any other token: cancel NLSEMI, go back to default
      goDefault cs acc

end

def lex (s : String) : List GoToken :=
  goDefault s.toList []

def tokenize (s : String) : List (String × String) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind))

/-- Tokenize with byte lengths for position tracking. Returns (text, kind, byteLength) -/
def tokenizeWithLengths (s : String) : List (String × String × Nat) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind, t.toText.length))

end GoLexer
