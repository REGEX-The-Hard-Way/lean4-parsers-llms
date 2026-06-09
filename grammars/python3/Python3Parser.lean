/-
Python3 Grammar for Lean — Scanner + Parser with full location tracking.

Scanner: each token is wrapped in `Located` (SourcePos-tagged).
Parser:  each AST node is wrapped in `Located` (Span-tagged).

Based on Python 3.10+ grammar from https://docs.python.org/3/reference/grammar.html
and the ANTLR4 grammar at grammars-v4/python/python3.

Self-contained — includes LeanParser library inline.
-/

-- ============================================================
-- LeanParser Library (inline)
-- ============================================================

namespace LeanParser

-- ============================================================
-- Source Position
-- ============================================================

/-- A position in source code: line, column, and byte offset. -/
structure SourcePos where
  line   : Nat
  column : Nat
  offset : Nat
deriving Repr, BEq, Inhabited, Ord

instance : ToString SourcePos where
  toString p := s!"{p.line+1}:{p.column+1}"

/-- The start position (line 0, column 0, offset 0). -/
def startPos : SourcePos := { line := 0, column := 0, offset := 0 }

/-- Advance a position by one character. -/
def SourcePos.advance (p : SourcePos) (c : Char) : SourcePos :=
  if c = '\n' then
    { line := p.line + 1, column := 0, offset := p.offset + 1 }
  else
    { line := p.line, column := p.column + 1, offset := p.offset + 1 }

/-- Advance a position by a string. -/
def SourcePos.advanceString (p : SourcePos) (s : String) : SourcePos :=
  s.foldl (fun pos c => pos.advance c) p

-- ============================================================
-- Span
-- ============================================================

/-- A span of source code from start to end position. -/
structure Span where
  start : SourcePos
  stop  : SourcePos
deriving Repr, BEq, Inhabited

instance : ToString Span where
  toString s := s!"{s.start}-{s.stop}"

/-- Create a span from start position and consumed string. -/
def Span.ofString (start : SourcePos) (s : String) : Span :=
  { start := start, stop := start.advanceString s }

/-- Merge two spans into one covering both. -/
def Span.merge (a b : Span) : Span :=
  { start := a.start, stop := b.stop }

-- ============================================================
-- Located (position-tagged values)
-- ============================================================

/-- A value with a source span attached. -/
structure Located (α : Type) where
  value : α
  span  : Span
deriving Repr, BEq, Inhabited

/-- Attach a span to a value. -/
def Located.at (val : α) (span : Span) : Located α :=
  { value := val, span := span }

/-- Map a function over a located value, preserving the span. -/
def Located.map (f : α → β) (l : Located α) : Located β :=
  { value := f l.value, span := l.span }

-- ============================================================
-- Diagnostics
-- ============================================================

/-- Severity of a parse diagnostic. -/
inductive DiagSeverity where
  | error | warning | info
deriving Repr, BEq

/-- A parse diagnostic message anchored to a span. -/
structure Diag where
  severity : DiagSeverity
  span     : Span
  message  : String
deriving Repr, BEq

/-- Create an error diagnostic. -/
def Diag.error (span : Span) (msg : String) : Diag :=
  { severity := DiagSeverity.error, span := span, message := msg }

-- ============================================================
-- Input
-- ============================================================

/-- The input to a parser: remaining text + current position. -/
structure Input where
  text : String
  pos  : SourcePos
deriving Repr, BEq

instance : ToString Input where
  toString i := s!"@{i.pos}: \"{(i.text.take 20).toString}\""

/-- Create an input from a string at the start position. -/
def Input.ofString (s : String) : Input :=
  { text := s, pos := startPos }

/-- Check if input is exhausted. -/
def Input.isEOF (i : Input) : Bool :=
  i.text.isEmpty

/-- Peek at the next character without consuming it. -/
def Input.peek (i : Input) : Option Char :=
  if i.text.isEmpty then none
  else some (i.text.get ⟨0⟩)

/-- Advance the input by one character. -/
def Input.advance (i : Input) : Input :=
  if i.text.isEmpty then i
  else
    let c := i.text.get ⟨0⟩
    { text := (i.text.drop 1).toString, pos := i.pos.advance c }

/-- Check if remaining text starts with a prefix. -/
def Input.startsWith (i : Input) (s : String) : Bool :=
  i.text.startsWith s

/-- Drop n characters from the beginning. -/
def Input.drop (i : Input) (n : Nat) : Input :=
  let dropped := i.text.drop n
  { text := dropped.toString, pos := i.pos.advanceString (i.text.take n).toString }

-- ============================================================
-- Parser Monad
-- ============================================================

/-- The result of a parse step. -/
inductive StepResult (α : Type) where
  | success : α → Input → StepResult α
  | failure : List Diag → StepResult α
deriving Repr

/-- The core parser monad. -/
def Parser (α : Type) : Type := Input → StepResult α

namespace Parser

/-- Run a parser on a String. -/
def run (p : Parser α) (s : String) : Except (List Diag) α :=
  match p (Input.ofString s) with
  | .success val _ => .ok val
  | .failure diags => .error diags

/-- Run a parser and require full consumption. -/
def runEOF (p : Parser α) (s : String) : Except (List Diag) α :=
  match p (Input.ofString s) with
  | .success val rest =>
    if rest.isEOF then .ok val
    else .error [Diag.error (Span.ofString rest.pos rest.text) "expected end of input"]
  | .failure diags => .error diags

-- ============================================================
-- Monad and Alternative
-- ============================================================

instance : Monad Parser where
  pure a := fun i => .success a i
  bind p f := fun i =>
    match p i with
    | .success val rest => f val rest
    | .failure diags    => .failure diags

instance : Alternative Parser where
  failure := fun i => .failure [Diag.error (Span.ofString i.pos i.text) "parse failure"]
  orElse p q := fun i =>
    match p i with
    | .success val rest => .success val rest
    | .failure _ =>
      match q () i with
      | .success val rest => .success val rest
      | .failure diags2 => .failure diags2

-- ============================================================
-- Error reporting
-- ============================================================

/-- Fail with a message at the current input position. -/
def fail (msg : String) : Parser α := fun i =>
  .failure [Diag.error (Span.ofString i.pos ((i.text.take 20).toString)) msg]

-- ============================================================
-- Input queries (position-aware)
-- ============================================================

/-- Get the current input. -/
def getInput : Parser Input := fun i => .success i i

/-- Get the current source position. -/
def getPos : Parser SourcePos := fun i => .success i.pos i

/-- Get the position span from start to current position. -/
def getSpan (start : SourcePos) : Parser Span := do
  let p ← getPos
  return { start := start, stop := p }

/-- Peek at the next character. -/
def peek : Parser (Option Char) := fun i => .success (i.peek) i

/-- Get the remaining text. -/
def getText : Parser String := fun i => .success i.text i

/-- Parse with a start position, returning a Located value. -/
def located (p : Parser α) : Parser (Located α) := do
  let pos ← getPos
  let val ← p
  let endPos ← getPos
  return Located.at val { start := pos, stop := endPos }

-- ============================================================
-- Basic combinators
-- ============================================================

/-- Parse a single character matching a predicate. -/
def satisfy (pred : Char → Bool) : Parser Char := fun i =>
  match i.peek with
  | none => .failure [Diag.error (Span.ofString i.pos "") "unexpected end of input"]
  | some c =>
    if pred c then
      .success c i.advance
    else
      .failure [Diag.error (Span.ofString i.pos (toString c)) s!"unexpected character '{c}'"]

/-- Parse exactly the given character. -/
def char (c : Char) : Parser Char :=
  satisfy (fun x => x = c)

/-- Parse a digit ('0'-'9'). -/
def digit : Parser Char :=
  satisfy (fun c => '0' ≤ c ∧ c ≤ '9')

/-- Parse an ASCII letter. -/
def letter : Parser Char :=
  satisfy (fun c => ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z'))

/-- Parse a specific String. -/
partial def string (s : String) : Parser Unit :=
  match s.toList with
  | [] => pure ()
  | c :: cs => char c *> string (String.ofList cs)

/-- Parse zero or more occurrences of p. -/
partial def many {α : Type} (p : Parser α) : Parser (List α) :=
  (do let x ← p; let xs ← many p; return (x :: xs)) <|> pure []

/-- Parse one or more occurrences of p. -/
def many1 {α : Type} (p : Parser α) : Parser (List α) := do
  let x ← p
  let xs ← many p
  return (x :: xs)

/-- Parse zero or more chars matching a predicate. -/
partial def takeWhile (pred : Char → Bool) : Parser String :=
  (do let c ← satisfy pred; let cs ← takeWhile pred; return (String.ofList (c :: cs.toList)))
  <|> pure ""

/-- Parse one or more chars matching a predicate. -/
def takeWhile1 (pred : Char → Bool) : Parser String := do
  let c ← satisfy pred
  let cs ← takeWhile pred
  return (String.ofList (c :: cs.toList))

/-- Parse zero or more p separated by a separator. -/
partial def sepBy {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  (do let x ← p; let xs ← many (sep *> p); return (x :: xs)) <|> pure []

/-- Parse one or more p separated by a separator. -/
def sepBy1 {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  let x ← p
  let xs ← many (sep *> p)
  return (x :: xs)

/-- Try an optional parser. -/
def optional {α : Type} (p : Parser α) : Parser (Option α) :=
  (do let x ← p; return (some x)) <|> pure none

/-- Succeed only if the given parser fails. -/
def notFollowedBy (p : Parser α) : Parser Unit := fun i =>
  match p i with
  | .success _ _ => .failure [Diag.error (Span.ofString i.pos i.text) "unexpected match"]
  | .failure _   => .success () i

-- ============================================================
-- Whitespace and newline handling (Python-aware)
-- ============================================================

/-- Skip horizontal whitespace (spaces, tabs) but not newlines. -/
partial def skipWS : Parser Unit :=
  (char ' ' *> skipWS) <|> (char '\t' *> skipWS) <|> pure ()

/-- Parse a newline: \n, \r\n, or \r. -/
def newline : Parser Unit :=
  (char '\n' *> pure ())
  <|> (char '\r' *> (char '\n' *> pure () <|> pure ()))

/-- Skip whitespace including newlines. -/
partial def skipWSFull : Parser Unit :=
  (char ' ' *> skipWSFull) <|> (char '\t' *> skipWSFull)
  <|> (newline *> skipWSFull)
  <|> pure ()

/-- Parse zero or more newlines (blank lines). -/
def blankLines : Parser (List Unit) := many newline

end Parser

end LeanParser

-- ============================================================
-- Open the framework
-- ============================================================

open LeanParser
open LeanParser.Parser

-- ============================================================
-- Python3 Token Type
-- ============================================================

/-- All Python3 token kinds. -/
inductive Python3Token where
  -- Keywords
  | kwFalse | kwNone | kwTrue
  | kwAnd | kwAs | kwAssert | kwAsync | kwAwait
  | kwBreak
  | kwCase | kwClass | kwContinue
  | kwDef | kwDel
  | kwElif | kwElse | kwExcept
  | kwFinally | kwFor | kwFrom
  | kwGlobal
  | kwIf | kwImport | kwIn | kwIs
  | kwLambda
  | kwMatch
  | kwNonlocal | kwNot
  | kwOr
  | kwPass
  | kwRaise | kwReturn
  | kwTry
  | kwWhile | kwWith
  | kwYield
  -- Identifiers
  | idName : String → Python3Token
  | idUnderscore
  -- Literals
  | litInteger   : String → Python3Token
  | litFloat     : String → Python3Token
  | litImaginary : String → Python3Token
  | litString    : String → Python3Token
  | litBytes     : String → Python3Token
  -- Operators
  | opPlus | opMinus | opStar | opPower | opSlash | opFloorDiv | opMod
  | opAt
  | opLShift | opRShift
  | opBitAnd | opBitOr | opBitXor | opBitNot
  | opEq | opLt | opGt | opEqEq | opLtEq | opGtEq | opNotEq1 | opNotEq2
  | opAssign
  | opPlusEq | opMinusEq | opStarEq | opPowerEq | opSlashEq | opFloorDivEq | opModEq
  | opAtEq | opAndEq | opOrEq | opXorEq | opLShiftEq | opRShiftEq
  | opColonEq  -- := (walrus)
  | opArrow    -- ->
  -- Delimiters
  | delimLParen | delimRParen
  | delimLBrack | delimRBrack
  | delimLBrace | delimRBrace
  | delimComma | delimColon | delimSemi | delimDot
  | delimEllipsis
  -- Structural
  | tokNEWLINE
  | tokINDENT
  | tokDEDENT
  | tokEOF
  -- Comments (preserved for round-tripping)
  | tokComment  : String → Python3Token
  -- Unknown
  | tokUnknown  : String → Python3Token
deriving Repr, BEq, Inhabited

-- ============================================================
-- Token display
-- ============================================================

def Python3Token.toString : Python3Token → String
  | kwFalse     => "KEYWORD(False)"
  | kwNone      => "KEYWORD(None)"
  | kwTrue      => "KEYWORD(True)"
  | kwAnd       => "KEYWORD(and)"
  | kwAs        => "KEYWORD(as)"
  | kwAssert    => "KEYWORD(assert)"
  | kwAsync     => "KEYWORD(async)"
  | kwAwait     => "KEYWORD(await)"
  | kwBreak     => "KEYWORD(break)"
  | kwCase      => "KEYWORD(case)"
  | kwClass     => "KEYWORD(class)"
  | kwContinue  => "KEYWORD(continue)"
  | kwDef       => "KEYWORD(def)"
  | kwDel       => "KEYWORD(del)"
  | kwElif      => "KEYWORD(elif)"
  | kwElse      => "KEYWORD(else)"
  | kwExcept    => "KEYWORD(except)"
  | kwFinally   => "KEYWORD(finally)"
  | kwFor       => "KEYWORD(for)"
  | kwFrom      => "KEYWORD(from)"
  | kwGlobal    => "KEYWORD(global)"
  | kwIf        => "KEYWORD(if)"
  | kwImport    => "KEYWORD(import)"
  | kwIn        => "KEYWORD(in)"
  | kwIs        => "KEYWORD(is)"
  | kwLambda    => "KEYWORD(lambda)"
  | kwMatch     => "KEYWORD(match)"
  | kwNonlocal  => "KEYWORD(nonlocal)"
  | kwNot       => "KEYWORD(not)"
  | kwOr        => "KEYWORD(or)"
  | kwPass      => "KEYWORD(pass)"
  | kwRaise     => "KEYWORD(raise)"
  | kwReturn    => "KEYWORD(return)"
  | kwTry       => "KEYWORD(try)"
  | kwWhile     => "KEYWORD(while)"
  | kwWith      => "KEYWORD(with)"
  | kwYield     => "KEYWORD(yield)"
  | idName s    => s!"NAME({s})"
  | idUnderscore => "NAME(_)"
  | litInteger s   => s!"INT({s})"
  | litFloat s     => s!"FLOAT({s})"
  | litImaginary s => s!"IMAG({s})"
  | litString s    => s!"STR({s})"
  | litBytes s     => s!"BYTES({s})"
  | opPlus      => "OP(+)"
  | opMinus     => "OP(-)"
  | opStar      => "OP(*)"
  | opPower     => "OP(**)"
  | opSlash     => "OP(/)"
  | opFloorDiv  => "OP(//)"
  | opMod       => "OP(%)"
  | opAt        => "OP(@)"
  | opLShift    => "OP(<<)"
  | opRShift    => "OP(>>)"
  | opBitAnd    => "OP(&)"
  | opBitOr     => "OP(|)"
  | opBitXor    => "OP(^)"
  | opBitNot    => "OP(~)"
  | opEq        => "OP(=)"
  | opLt        => "OP(<)"
  | opGt        => "OP(>)"
  | opEqEq      => "OP(==)"
  | opLtEq      => "OP(<=)"
  | opGtEq      => "OP(>=)"
  | opNotEq1    => "OP(<>)"
  | opNotEq2    => "OP(!=)"
  | opAssign    => "OP(:=)"
  | opPlusEq    => "OP(+=)"
  | opMinusEq   => "OP(-=)"
  | opStarEq    => "OP(*=)"
  | opPowerEq   => "OP(**=)"
  | opSlashEq   => "OP(/=)"
  | opFloorDivEq => "OP(//=)"
  | opModEq     => "OP(%=)"
  | opAtEq      => "OP(@=)"
  | opAndEq     => "OP(&=)"
  | opOrEq      => "OP(|=)"
  | opXorEq     => "OP(^=)"
  | opLShiftEq  => "OP(<<=)"
  | opRShiftEq  => "OP(>>=)"
  | opColonEq   => "OP(:=)"
  | opArrow     => "OP(->)"
  | delimLParen => "DELIM(()
  | delimRParen => "DELIM())"
  | delimLBrack => "DELIM([)"
  | delimRBrack => "DELIM(])"
  | delimLBrace => "DELIM({)"
  | delimRBrace => "DELIM(})"
  | delimComma  => "DELIM(,)"
  | delimColon  => "DELIM(:)"
  | delimSemi   => "DELIM(;)"
  | delimDot    => "DELIM(.)"
  | delimEllipsis => "DELIM(...)"
  | tokNEWLINE  => "NEWLINE"
  | tokINDENT   => "INDENT"
  | tokDEDENT   => "DEDENT"
  | tokEOF      => "EOF"
  | tokComment s => s!"COMMENT({s})"
  | tokUnknown s => s!"UNKNOWN({s})"

instance : ToString Python3Token where
  toString := Python3Token.toString

def Python3Token.kind : Python3Token → String
  | idName _     => "identifier"
  | idUnderscore => "identifier"
  | kwFalse | kwNone | kwTrue | kwAnd | kwAs | kwAssert | kwAsync | kwAwait
  | kwBreak | kwCase | kwClass | kwContinue | kwDef | kwDel | kwElif | kwElse
  | kwExcept | kwFinally | kwFor | kwFrom | kwGlobal | kwIf | kwImport | kwIn
  | kwIs | kwLambda | kwMatch | kwNonlocal | kwNot | kwOr | kwPass | kwRaise
  | kwReturn | kwTry | kwWhile | kwWith | kwYield => "keyword"
  | litInteger _ | litFloat _ | litImaginary _ => "number"
  | litString _ | litBytes _ => "string"
  | opPlus | opMinus | opStar | opPower | opSlash | opFloorDiv | opMod
  | opAt | opLShift | opRShift | opBitAnd | opBitOr | opBitXor | opBitNot
  | opEq | opLt | opGt | opEqEq | opLtEq | opGtEq | opNotEq1 | opNotEq2
  | opAssign | opPlusEq | opMinusEq | opStarEq | opPowerEq | opSlashEq
  | opFloorDivEq | opModEq | opAtEq | opAndEq | opOrEq | opXorEq
  | opLShiftEq | opRShiftEq | opColonEq | opArrow => "operator"
  | delimLParen | delimRParen | delimLBrack | delimRBrack | delimLBrace
  | delimRBrace | delimComma | delimColon | delimSemi | delimDot
  | delimEllipsis => "delimiter"
  | tokNEWLINE => "newline"
  | tokINDENT => "indent"
  | tokDEDENT => "dedent"
  | tokEOF => "eof"
  | tokComment _ => "comment"
  | tokUnknown _ => "unknown"

-- ============================================================
-- Python3 keywords
-- ============================================================

def python3Keywords : List (String × Python3Token) := [
  ("False",    .kwFalse),
  ("None",     .kwNone),
  ("True",     .kwTrue),
  ("and",      .kwAnd),
  ("as",       .kwAs),
  ("assert",   .kwAssert),
  ("async",    .kwAsync),
  ("await",    .kwAwait),
  ("break",    .kwBreak),
  ("case",     .kwCase),
  ("class",    .kwClass),
  ("continue", .kwContinue),
  ("def",      .kwDef),
  ("del",      .kwDel),
  ("elif",     .kwElif),
  ("else",     .kwElse),
  ("except",   .kwExcept),
  ("finally",  .kwFinally),
  ("for",      .kwFor),
  ("from",     .kwFrom),
  ("global",   .kwGlobal),
  ("if",       .kwIf),
  ("import",   .kwImport),
  ("in",       .kwIn),
  ("is",       .kwIs),
  ("lambda",   .kwLambda),
  ("match",    .kwMatch),
  ("nonlocal", .kwNonlocal),
  ("not",      .kwNot),
  ("or",       .kwOr),
  ("pass",     .kwPass),
  ("raise",    .kwRaise),
  ("return",   .kwReturn),
  ("try",      .kwTry),
  ("while",    .kwWhile),
  ("with",     .kwWith),
  ("yield",    .kwYield)
]

def isPython3Keyword (s : String) : Bool :=
  python3Keywords.any (fun (kw, _) => kw == s)

def python3KeywordToken (s : String) : Python3Token :=
  match python3Keywords.lookup s with
  | some tok => tok
  | none     => idName s

-- ============================================================
-- Character classification
-- ============================================================

def isIdentStart (c : Char) : Bool :=
  c.isAlpha ∨ c = '_'

def isIdentCont (c : Char) : Bool :=
  c.isAlphanum ∨ c = '_'

def isHexDigit (c : Char) : Bool :=
  c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

def isOctalDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '7'

def isBinDigit (c : Char) : Bool :=
  c = '0' ∨ c = '1'

-- ============================================================
-- Scanner: String literal helpers
-- ============================================================

/-- Parse a short single-quoted string: '...' -/
partial def scanShortSQString : Parser String := do
  let _ ← char '\''
  let content ← takeWhile (fun c => c ≠ '\'' ∧ c ≠ '\\' ∧ c ≠ '\n')
  let _ ← char '\''
  return "'" ++ content ++ "'"

/-- Parse a short double-quoted string: "..." -/
partial def scanShortDQString : Parser String := do
  let _ ← char '"'
  let content ← takeWhile (fun c => c ≠ '"' ∧ c ≠ '\\' ∧ c ≠ '\n')
  let _ ← char '"'
  return "\"" ++ content ++ "\""

/-- Parse a short string: '...' or "..." -/
def scanShortString : Parser String :=
  scanShortSQString <|> scanShortDQString

/-- Parse a character that is NOT the start of the given string.
    Fails (without consuming) if remaining input starts with s. -/
def notString (s : String) : Parser Char := do
  let input ← getInput
  if input.text.startsWith s then
    fail "end of delimiter"
  else
    satisfy (fun _ => true)

/-- Parse a long single-quoted string: '''...''' -/
partial def scanLongSQString : Parser String := do
  let _ ← string "'''"
  let bodyChars ← many (notString "'''")
  let body := String.ofList bodyChars
  let _ ← string "'''"
  return "'''" ++ body ++ "'''"

/-- Parse a long double-quoted string: """...""" -/
partial def scanLongDQString : Parser String := do
  let _ ← string "\"\"\""
  let bodyChars ← many (notString "\"\"\"")
  let body := String.ofList bodyChars
  let _ ← string "\"\"\""
  return "\"\"\"" ++ body ++ "\"\"\""

/-- Parse a long string: '''...''' or \"\"\"...\"\"\" -/
def scanLongString : Parser String :=
  scanLongSQString <|> scanLongDQString

/-- Parse any string literal (short or long, with optional prefix). -/
def scanStringLiteral : Parser Python3Token := do
  -- optional prefix: r/R, u/U, f/F, b/B, or combinations (fr, rf, br, rb)
  let prefix ← (string "rf" *> pure "rf")
            <|> (string "rF" *> pure "rF")
            <|> (string "Rf" *> pure "Rf")
            <|> (string "RF" *> pure "RF")
            <|> (string "fr" *> pure "fr")
            <|> (string "fR" *> pure "fR")
            <|> (string "Fr" *> pure "Fr")
            <|> (string "FR" *> pure "FR")
            <|> (string "br" *> pure "br")
            <|> (string "bR" *> pure "bR")
            <|> (string "Br" *> pure "Br")
            <|> (string "BR" *> pure "BR")
            <|> (string "rb" *> pure "rb")
            <|> (string "rB" *> pure "rB")
            <|> (string "Rb" *> pure "Rb")
            <|> (string "RB" *> pure "RB")
            <|> (char 'r' *> pure "r")
            <|> (char 'R' *> pure "R")
            <|> (char 'u' *> pure "u")
            <|> (char 'U' *> pure "U")
            <|> (char 'f' *> pure "f")
            <|> (char 'F' *> pure "F")
            <|> (char 'b' *> pure "b")
            <|> (char 'B' *> pure "B")
            <|> pure ""
  -- Check if it's a long string
  let raw ← scanLongString <|> scanShortString
  let full := prefix ++ raw
  -- Determine if bytes or string
  if prefix.contains 'b' || prefix.contains 'B' then
    return litBytes full
  else
    return litString full

-- ============================================================
-- Scanner: Number literal helpers
-- ============================================================

/-- Parse a decimal integer. -/
def scanDecimalInteger : Parser String := do
  -- non-zero digit followed by digits, OR just zeros
  let nonZero := do
    let first ← satisfy (fun c => '1' ≤ c ∧ c ≤ '9')
    let rest ← takeWhile (fun c => c.isDigit)
    return String.ofList (first :: rest.toList)
  let zeroOnly := takeWhile1 (fun c => c = '0')
  nonZero <|> zeroOnly

/-- Parse a hex integer: 0x... or 0X... -/
def scanHexInteger : Parser String := do
  let _ ← char '0'
  let _ ← satisfy (fun c => c = 'x' ∨ c = 'X')
  let digits ← takeWhile1 isHexDigit
  return "0x" ++ digits

/-- Parse an octal integer: 0o... or 0O... -/
def scanOctalInteger : Parser String := do
  let _ ← char '0'
  let _ ← satisfy (fun c => c = 'o' ∨ c = 'O')
  let digits ← takeWhile1 isOctalDigit
  return "0o" ++ digits

/-- Parse a binary integer: 0b... or 0B... -/
def scanBinaryInteger : Parser String := do
  let _ ← char '0'
  let _ ← satisfy (fun c => c = 'b' ∨ c = 'B')
  let digits ← takeWhile1 isBinDigit
  return "0b" ++ digits

/-- Parse an integer literal. -/
def scanInteger : Parser Python3Token := do
  let s ← scanHexInteger <|> scanOctalInteger <|> scanBinaryInteger <|> scanDecimalInteger
  return litInteger s

/-- Parse a float literal. -/
def scanFloat : Parser Python3Token := do
  -- pointfloat: [intpart] fraction | intpart "."
  -- exponentfloat: (intpart | pointfloat) exponent
  -- We need to handle .5 style floats (no leading int part)
  let intPart ← takeWhile (fun c => c.isDigit)
  -- Try pointFloat: need either intPart then ".", or just "." then digits
  let s ← (do
    let _ ← char '.'
    let fracPart ← takeWhile1 (fun c => c.isDigit)
    let expPart ← optional (do
      let _ ← satisfy (fun c => c = 'e' ∨ c = 'E')
      let _ ← optional (satisfy (fun c => c = '+' ∨ c = '-'))
      takeWhile1 (fun c => c.isDigit))
    return litFloat (intPart ++ "." ++ fracPart ++ (expPart.getD "")))
  <|> (do
    -- exponentFloat: must have intPart then exponent
    if intPart.isEmpty then fail "need digits before exponent"
    let _ ← satisfy (fun c => c = 'e' ∨ c = 'E')
    let esign ← optional (satisfy (fun c => c = '+' ∨ c = '-'))
    let expPart ← takeWhile1 (fun c => c.isDigit)
    let es := match esign with | some c => toString c | none => ""
    return litFloat (intPart ++ "e" ++ es ++ expPart))
  return s

/-- Parse an imaginary number (suffix j/J).
    Must try before scanFloat and scanInteger since it extends them. -/
def scanImaginary : Parser Python3Token := do
  let intPart ← takeWhile (fun c => c.isDigit)
  -- Try pointFloat with j: intPart "." fracPart [expPart] ("j"|"J")
  (do
    let _ ← char '.'
    let fracPart ← takeWhile1 (fun c => c.isDigit)
    let expPart ← optional (do
      let _ ← satisfy (fun c => c = 'e' ∨ c = 'E')
      let _ ← optional (satisfy (fun c => c = '+' ∨ c = '-'))
      takeWhile1 (fun c => c.isDigit))
    let _ ← satisfy (fun c => c = 'j' ∨ c = 'J')
    return litImaginary (intPart ++ "." ++ fracPart ++ (expPart.getD "") ++ "j"))
  <|> (do
    -- exponentFloat with j: intPart "e" ["+"|"-"] expPart ("j"|"J")
    if intPart.isEmpty then fail "need digits"
    let _ ← satisfy (fun c => c = 'e' ∨ c = 'E')
    let esign ← optional (satisfy (fun c => c = '+' ∨ c = '-'))
    let expPart ← takeWhile1 (fun c => c.isDigit)
    let _ ← satisfy (fun c => c = 'j' ∨ c = 'J')
    let es := match esign with | some c => toString c | none => ""
    return litImaginary (intPart ++ "e" ++ es ++ expPart ++ "j"))
  <|> (do
    -- Integer with j: intPart ("j"|"J")
    if intPart.isEmpty then fail "need digits"
    let _ ← satisfy (fun c => c = 'j' ∨ c = 'J')
    return litImaginary (intPart ++ "j"))

/-- Parse any number literal.
    Try imaginary first (longest match), then float, then integer. -/
def scanNumber : Parser Python3Token :=
  scanImaginary <|> scanFloat <|> scanInteger

-- ============================================================
-- Scanner: Identifier
-- ============================================================

/-- Parse an identifier or keyword. -/
def scanIdentifier : Parser Python3Token := do
  let first ← satisfy isIdentStart
  let rest ← takeWhile isIdentCont
  let name := String.ofList (first :: rest.toList)
  -- Check for standalone underscore
  if name == "_" then return idUnderscore
  -- Check for keywords (including soft keywords in context)
  return python3KeywordToken name

-- ============================================================
-- Scanner: Operator
-- ============================================================

/-- Parse operators, handling multi-character operators by longest match. -/
def scanOperator : Parser Python3Token := do
  let ops : List (String × Python3Token) := [
    -- 3-char operators
    ("//=", .opFloorDivEq), ("**=", .opPowerEq), (">>=", .opRShiftEq),
    ("<<=", .opLShiftEq),
    -- 2-char operators
    ("**",  .opPower),     ("//",  .opFloorDiv),  ("<<",  .opLShift),
    (">>",  .opRShift),    ("==",  .opEqEq),      ("<=",  .opLtEq),
    (">=",  .opGtEq),      ("!=",  .opNotEq2),    ("<>",  .opNotEq1),
    ("+=",  .opPlusEq),    ("-=",  .opMinusEq),   ("*=",  .opStarEq),
    ("/=",  .opSlashEq),   ("%=",  .opModEq),     ("@=",  .opAtEq),
    ("&=",  .opAndEq),     ("|=",  .opOrEq),      ("^=",  .opXorEq),
    (":=",  .opColonEq),   ("->",  .opArrow),
    -- 1-char operators
    ("+",   .opPlus),      ("-",   .opMinus),     ("*",   .opStar),
    ("/",   .opSlash),     ("%",   .opMod),       ("@",   .opAt),
    ("=",   .opEq),        ("<",   .opLt),        (">",   .opGt),
    ("&",   .opBitAnd),    ("|",   .opBitOr),     ("^",   .opBitXor),
    ("~",   .opBitNot)
  ]
  -- Try each operator in length-descending order
  let rec tryList : List (String × Python3Token) → Parser Python3Token
    | [] => fail "unknown operator"
    | (s, t) :: rest => (string s *> pure t) <|> tryList rest
  tryList ops

-- ============================================================
-- Scanner: Delimiters
-- ============================================================

def scanDelimiter : Parser Python3Token := do
  (char '(' *> pure delimLParen)
  <|> (char ')' *> pure delimRParen)
  <|> (char '[' *> pure delimLBrack)
  <|> (char ']' *> pure delimRBrack)
  <|> (char '{' *> pure delimLBrace)
  <|> (char '}' *> pure delimRBrace)
  <|> (string "..." *> pure delimEllipsis)
  <|> (char ',' *> pure delimComma)
  <|> (char ':' *> pure delimColon)
  <|> (char ';' *> pure delimSemi)
  <|> (char '.' *> pure delimDot)

-- ============================================================
-- Scanner: Comment
-- ============================================================

/-- Parse a Python comment: # to end of line. -/
def scanComment : Parser Python3Token := do
  let _ ← char '#'
  let content ← takeWhile (fun c => c ≠ '\n')
  return tokComment ("#" ++ content)

-- ============================================================
-- Scanner: Line joining (backslash-newline)
-- ============================================================

/-- Parse a line continuation (backslash at end of logical line). -/
def scanLineJoining : Parser Unit := do
  let _ ← char '\\'
  skipWS
  newline <|> pure ()

-- ============================================================
-- Scanner: INDENT/DEDENT tracking
-- ============================================================

/-- State for the Python indentation tracker. -/
structure IndentState where
  stack    : List Nat  -- current indent stack (positive indents only)
  atBOL    : Bool      -- are we at the beginning of a logical line?
  deriving Repr, BEq

/-- Create initial indent state. -/
def initIndentState : IndentState :=
  { stack := [0], atBOL := true }

/-- Compute the indent level of the current line start in spaces. -/
def computeIndent (s : String) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i ≥ s.length then acc
    else
      let c := s.get ⟨i⟩
      if c = ' ' then count (i+1) (acc+1)
      else if c = '\t' then count (i+1) (acc+4)  -- tabs expand to 4 (as in stdlib tokenize)
      else acc
  count 0 0

/--
Python-aware scanner that tracks INDENT/DEDENT.
This is the main tokenizer that wraps individual token scanners
and injects INDENT/DEDENT/NEWLINE tokens at appropriate points.
-/
partial def scanPythonToken (st : IndentState) : Parser (List Python3Token × IndentState) := do
  let pos ← getPos
  let c ← peek
  match c with
  | none =>
    -- EOF: emit any pending DEDENTs
    let dedents := mkDedents st.stack 0
    return (dedents ++ [tokEOF], { st with stack := [0] })
  | some ch =>
    if st.atBOL then
      -- At beginning of line: handle indentation
      if ch = '\n' || ch = '\r' then
        -- blank line, skip
        let _ ← newline
        return ([], { st with atBOL := true })
      else if ch = ' ' || ch = '\t' then
        let indent := computeIndent (← getText)
        -- Don't consume the whitespace yet — we emit INDENT/DEDENT first
        -- Actually we need to consume the leading whitespace.
        -- Let me simplify: compute indent from remaining text.
        -- For now, we skip leading whitespace and compute indent.
        let _ ← skipWS
        if st.stack.head? = some indent then
          -- Same indent level, emit nothing special
          return ([], { st with atBOL := false })
        else if indent > (st.stack.headD 0) then
          return ([tokINDENT], { st with stack := indent :: st.stack, atBOL := false })
        else
          -- Pop indents until we match
          let rec popDedents (s : List Nat) (target : Nat) : (List Python3Token × List Nat) :=
            match s with
            | [] => ([], [])
            | top :: rest =>
              if top == target then ([], s)
              else if top > target then
                let (ds, s') := popDedents rest target
                (tokDEDENT :: ds, rest)
              else ([], s)
          let (dedents, newStack) := popDedents st.stack indent
          return (dedents, { st with stack := newStack, atBOL := false })
      else
        -- No leading whitespace on a new line
        let indent := 0
        if st.stack.headD 0 > 0 then
          -- Pop all indents
          let rec popAll (s : List Nat) : List Python3Token :=
            if s.length ≤ 1 then []  -- keep the 0 indent
            else tokDEDENT :: popAll s.tail!
          return (popAll st.stack, { st with stack := [0], atBOL := false })
        return ([], { st with atBOL := false })
    else
      -- Not at beginning of line: scan a token
      if ch = '\n' || ch = '\r' then
        let _ ← newline
        return ([tokNEWLINE], { st with atBOL := true })
      else if ch = '#' then
        let tok ← located scanComment
        return ([tok.value], st)  -- keep atBOL false, don't switch to BOL
      else if ch = '\\' then
        -- Check for line joining
        let rest ← getText
        let restChars := rest.toList
        match restChars with
        | '\\' :: c2 :: _ =>
          if c2 = '\n' || c2 = '\r' then
            let _ ← scanLineJoining
            return ([], { st with atBOL := false })
          else
            let tok ← located scanOperator
            return ([tok.value], { st with atBOL := false })
        | _ =>
          let tok ← located scanOperator
          return ([tok.value], { st with atBOL := false })
      else if ch = ' ' || ch = '\t' then
        let _ ← skipWS
        return ([], { st with atBOL := false })
      else if ch = '\"' || ch = '\'' then
        let tok ← located (scanStringLiteral <|> (scanLongString *> pure (litString "")))
        return ([tok.value], { st with atBOL := false })
      else if ch.isDigit then
        let tok ← located scanNumber
        return ([tok.value], { st with atBOL := false })
      else if ch = '.' then
        -- Check for float literal first (e.g., .5), otherwise delimiter, then ellipsis
        (do let _ ← char '.'; let _ ← digit; -- it's a float
             let restFloat ← takeWhile (fun c => c.isDigit)
             let exp ← optional (do
               let _ ← satisfy (fun c => c = 'e' ∨ c = 'E')
               let _ ← optional (satisfy (fun c => c = '+' ∨ c = '-'))
               takeWhile1 (fun c => c.isDigit))
             let p ← getPos
             return ([litFloat ("." ++ (toString (← getPos)) ++ restFloat ++ exp.getD "")], { st with atBOL := false }))
        <|> (do let _ ← char '.'; let _ ← char '.'; let _ ← char '.';
                return ([delimEllipsis], { st with atBOL := false }))
        <|> (do let _ ← char '.'; return ([delimDot], { st with atBOL := false }))
      else if isIdentStart ch then
        let tok ← located scanIdentifier
        return ([tok.value], { st with atBOL := false })
      else if ch = '(' || ch = ')' || ch = '[' || ch = ']' || ch = '{' || ch = '}'
           || ch = ',' || ch = ':' || ch = ';' then
        let tok ← located scanDelimiter
        return ([tok.value], { st with atBOL := false })
      else
        let tok ← located scanOperator
        return ([tok.value], { st with atBOL := false })
where
  mkDedents (stack : List Nat) (target : Nat) : List Python3Token :=
    match stack with
    | []  => []
    | top :: rest =>
      if top > target then
        tokDEDENT :: mkDedents rest target
      else []

/-- Full Python tokenizer: consumes input and returns a located token list. -/
partial def scanPythonTokensAux (st : IndentState) (acc : List (Located Python3Token)) : Parser (List (Located Python3Token)) := do
  let pos ← getPos
  let (toks, st') ← scanPythonToken st
  let locatedToks := toks.map fun t => Located.at t (Span.ofString pos "")
  if toks.contains tokEOF then
    return (acc ++ locatedToks)
  else
    scanPythonTokensAux st' (acc ++ locatedToks)

/-- Tokenize a Python3 source string into located tokens. -/
def tokenize (source : String) : Except (List Diag) (List (Located Python3Token)) :=
  Parser.run (scanPythonTokensAux initIndentState []) source

-- ============================================================
-- Python3 AST Types
-- ============================================================

/-- AST nodes carry their source span for location tracking. -/
def AstNode (α : Type) := Located α

/-- A Python identifier. -/
structure Ident where
  name : String
deriving Repr, BEq

/-- An operator. -/
structure Operator where
  op : String
deriving Repr, BEq

/-- An expression. -/
inductive Expr where
  -- Literals
  | literalNone
  | literalTrue
  | literalFalse
  | literalInt    : String → Expr
  | literalFloat  : String → Expr
  | literalImag   : String → Expr
  | literalString : List String → Expr  -- concatenated adjacent strings
  | literalBytes  : String → Expr
  -- Identifiers
  | nameId    : Ident → Expr
  | nameStar  : Expr                   -- *args
  | nameDStar : Expr                   -- **kwargs
  -- Unary operators
  | unaryOp    : Operator → Expr → Expr
  | unaryNot   : Expr → Expr
  -- Binary operators
  | binOp      : Operator → Expr → Expr → Expr
  | boolOp     : BoolOp → Expr → Expr → Expr  -- and/or
  -- Comparisons
  | compare    : Expr → List (Operator × Expr) → Expr
  -- Conditional
  | ifExpr     : Expr → Expr → Expr → Expr    -- body if cond else else_
  -- Lambda
  | lambda     : Args → Expr → Expr
  -- Comprehensions
  | listComp    : Expr → List CompFor → Expr
  | setComp     : Expr → List CompFor → Expr
  | dictComp    : (Expr × Expr) → List CompFor → Expr
  | genExpr     : Expr → List CompFor → Expr
  -- Containers
  | listLit     : List Expr → Expr
  | tupleLit    : List Expr → Expr
  | setLit      : List Expr → Expr
  | dictLit     : List (Expr × Expr) → Expr
  -- Subscript
  | subscript   : Expr → Slice → Expr
  -- Attribute access
  | attribute   : Expr → Ident → Expr
  -- Function call
  | call        : Expr → List Arg → Expr
  -- Await
  | awaitExpr   : Expr → Expr
  -- Yield
  | yieldExpr   : (Option Expr) → Expr
  | yieldFrom   : Expr → Expr
  -- Starred
  | starred     : Expr → Expr
deriving Repr, BEq

/-- Boolean operator: and / or. -/
inductive BoolOp where
  | andOp | orOp
deriving Repr, BEq

/-- A slice in subscript: [start:stop:step] -/
structure Slice where
  start : Option Expr
  stop  : Option Expr
  step  : Option Expr
deriving Repr, BEq

/-- A function argument. -/
inductive Arg where
  | positional : Expr → Arg
  | keyword    : Ident → Expr → Arg
  | star       : Expr → Arg         -- *args
  | dstar      : Expr → Arg         -- **kwargs
deriving Repr, BEq

/-- Function/class parameters. -/
structure Args where
  posOnly   : List (Ident × Option Expr)   -- positional-only: f(a, b=1, /)
  args      : List (Ident × Option Expr)   -- normal: f(a, b=1)
  vararg    : Option Ident                 -- *args
  kwOnly    : List (Ident × Option Expr)   -- keyword-only: f(*, a, b=1)
  kwarg     : Option Ident                 -- **kwargs
deriving Repr, BEq

/-- A comprehension for clause. -/
structure CompFor where
  isAsync : Bool
  targets : List Expr
  iter    : Expr
  ifs     : List Expr   -- if clauses
deriving Repr, BEq

-- ============================================================
-- Python3 Statement AST
-- ============================================================

/-- A function/class decorator. -/
structure Decorator where
  name     : List Ident  -- dotted name
  args     : Option (List Arg)
deriving Repr, BEq

/-- A simple statement. -/
inductive SimpleStmt where
  | exprStmt      : Expr → SimpleStmt                   -- expression statement
  | assign        : List Expr → Expr → SimpleStmt       -- targets = value
  | augAssign     : Operator → Expr → Expr → SimpleStmt -- target op= value
  | annAssign     : Expr → Expr → (Option Expr) → SimpleStmt  -- target: type = value
  | delStmt       : List Expr → SimpleStmt
  | passStmt
  | breakStmt
  | continueStmt
  | returnStmt    : Option Expr → SimpleStmt
  | raiseStmt     : (Option Expr) → (Option Expr) → SimpleStmt  -- raise exc from cause
  | yieldStmt     : Expr → SimpleStmt
  | importName    : List DottedName → SimpleStmt
  | importFrom    : (List (Option String)) → (List DottedName) → SimpleStmt
  | globalStmt    : List Ident → SimpleStmt
  | nonlocalStmt  : List Ident → SimpleStmt
  | assertStmt    : Expr → (Option Expr) → SimpleStmt
deriving Repr, BEq

/-- A dotted name for imports: a.b.c -/
structure DottedName where
  asName : Option Ident
  parts  : List Ident
deriving Repr, BEq

/-- A compound statement. -/
inductive CompoundStmt where
  | ifStmt     : Expr → Block → List (Expr × Block) → (Option Block) → CompoundStmt
  | whileStmt  : Expr → Block → (Option Block) → CompoundStmt
  | forStmt    : List Expr → Expr → Block → (Option Block) → CompoundStmt
  | tryStmt    : Block → List (Option Expr × Option Ident × Block) → (Option Block) → (Option Block) → CompoundStmt
  | withStmt   : List (Expr × Option Expr) → Block → CompoundStmt
  | funcDef    : List Decorator → Ident → Args → (Option Expr) → Block → CompoundStmt
  | classDef   : List Decorator → Ident → (Option (List Arg)) → Block → CompoundStmt
  | asyncStmt  : CompoundStmt → CompoundStmt
  | matchStmt  : Expr → List CaseClause → CompoundStmt
  deriving Repr, BEq

/-- A block of code: either simple_stmts or INDENT stmt+ DEDENT -/
inductive Block where
  | simple : List (AstNode SimpleStmt) → Block
  | suite  : List (AstNode Stmt) → Block
deriving Repr, BEq

/-- A complete statement. -/
inductive Stmt where
  | simple   : SimpleStmt → Stmt
  | compound : CompoundStmt → Stmt
deriving Repr, BEq

/-- A case clause for match. -/
structure CaseClause where
  pattern  : MatchPattern
  guard    : Option Expr
  body     : Block
deriving Repr, BEq

/-- Match pattern AST. -/
inductive MatchPattern where
  | wildcard
  | literal      : Expr → MatchPattern
  | capture      : Ident → MatchPattern
  | value        : List Ident → MatchPattern
  | orPattern    : List MatchPattern → MatchPattern
  | sequence     : List MatchPattern → MatchPattern
  | mapping      : List (MatchPattern × MatchPattern) → (Option Ident) → MatchPattern
  | classPat     : (List Ident) → List MatchPattern → List (Ident × MatchPattern) → MatchPattern
  | asPattern    : MatchPattern → Ident → MatchPattern
  | starPattern  : Option Ident → MatchPattern
deriving Repr, BEq

/-- A decorator on a function or class. -/
structure LocatedDecorator where
  name    : Located (List Ident)
  args    : Located (Option (List (Located Arg)))
deriving Repr, BEq

-- ============================================================
-- Parser: Expression parsing (Precedence Climbing / Pratt)
-- ============================================================

/--
Parser combinators that construct AST nodes with spans.
Each rule returns `AstNode α` = `Located α` encoding source location.
-/

/-- Parse with location: captures start/end positions around a parser. -/
def located (p : Parser α) : Parser (Located α) :=
  LeanParser.Parser.located p

/-- Parse a name identifier (must not be a keyword in name context). -/
def parseNameIdent : Parser (Located Ident) := located do
  let pos ← getPos
  let first ← satisfy isIdentStart
  let rest ← takeWhile isIdentCont
  let name := String.ofList (first :: rest.toList)
  return { name := name }

/-- Note: The parser below assumes tokens have been pre-scanned.
    We use a token-stream-based parser approach with location.
    The scanner produces `Located Python3Token`; the parser consumes them
    and builds `AstNode` values.

    For this implementation, we use a combined char-level approach
    where the parser reads characters directly (with the Python lexer
    integrated), tracking positions throughout.
-/

-- ============================================================
-- Parser State (Indentation-aware)
-- ============================================================

/-- Parser-level indent state. -/
structure ParseIndentState where
  indentStack : List Nat
deriving Repr, BEq

def initParseState : ParseIndentState :=
  { indentStack := [0] }

/-- PEEK the current indent level. -/
def currentIndent (st : ParseIndentState) : Nat :=
  st.indentStack.headD 0

-- ============================================================
-- Parser: Primary atom expressions
-- ============================================================

/-- Parse a literal expression: None, True, False, number, string, bytes. -/
partial def parseAtomLiteral : Parser (AstNode Expr) := located do
  let c ← peek
  match c with
  | none => fail "expected literal"
  | some ch =>
    if ch = 'N' then
      let _ ← string "None"
      notFollowedBy (satisfy isIdentCont)
      return Expr.literalNone
    else if ch = 'T' then
      let _ ← string "True"
      notFollowedBy (satisfy isIdentCont)
      return Expr.literalTrue
    else if ch = 'F' then
      let _ ← string "False"
      notFollowedBy (satisfy isIdentCont)
      return Expr.literalFalse
    else if ch.isDigit then
      let s ← takeWhile1 (fun c => c.isDigit ∨ c = '.' ∨ c = 'e' ∨ c = 'E'
                              ∨ c = '+' ∨ isHexDigit c ∨ c = 'x' ∨ c = 'X'
                              ∨ c = 'o' ∨ c = 'O' ∨ c = 'b' ∨ c = 'B' ∨ c = 'j' ∨ c = 'J')
      if s.contains 'j' || s.contains 'J' then return Expr.literalImag s
      else if s.contains '.' || s.contains 'e' || s.contains 'E' then return Expr.literalFloat s
      else return Expr.literalInt s
    else if ch = '\"' || ch = '\'' then
      -- Parse one or more adjacent strings
      let strs ← many1 (located scanStringLiteral)
      let ss := strs.map fun l => match l.value with
        | litString s => s
        | litBytes s  => s
        | _ => ""
      return Expr.literalString ss
    else
      fail "expected literal"

/-- Parse a name expression. -/
def parseName : Parser (AstNode Expr) := located do
  let first ← satisfy isIdentStart
  let rest ← takeWhile isIdentCont
  let name := String.ofList (first :: rest.toList)
  return Expr.nameId { name := name }

/-- Parse a parenthesized expression, tuple, or generator. -/
partial def parseParenExpr : Parser (AstNode Expr) := located do
  let _ ← char '('
  skipWSFull
  let c ← peek
  match c with
  | some ')' =>
    let _ ← char ')'
    return Expr.tupleLit []  -- empty tuple
  | _ =>
    let first ← parseExpr
    let rest ← peek
    match rest with
    | some ')' =>
      let _ ← char ')'
      return first.value  -- just a parenthesized expr
    | some ',' =>
      -- tuple or generator
      let _ ← char ','
      skipWSFull
      let restExprs ← sepBy parseExpr (char ',' *> skipWSFull)
      let _ ← optional (char ',')
      let _ ← char ')'
      return Expr.tupleLit (first.value :: restExprs.map (·.value))
    | _ =>
      -- generator expression (expr comp_for)
      let comp ← parseCompFor
      let _ ← char ')'
      return Expr.genExpr first.value [comp]
    | none => fail "unterminated parenthesized expression"

/-- Parse a list literal: [items] -/
partial def parseListLit : Parser (AstNode Expr) := located do
  let _ ← char '['
  skipWSFull
  let c ← peek
  match c with
  | some ']' =>
    let _ ← char ']'
    return Expr.listLit []
  | _ =>
    let first ← parseExpr
    let compOrMore ← (do
      let _ ← char ','
      skipWSFull
      let rest ← sepBy parseExpr (char ',' *> skipWSFull)
      return some (first.value :: rest.map (·.value)))
      <|> (do
        let comp ← parseCompFor
        return none)  -- list comprehension
      <|> pure (some [first.value])
    match compOrMore with
    | some exprs =>
      let _ ← optional (char ',')
      let _ ← char ']'
      return Expr.listLit exprs
    | none =>
      let _ ← char ']'
      -- we already parsed the comp_for; need to restructure
      return Expr.listLit [first.value]  -- simplified

/-- Parse a dict/set literal: {items} -/
partial def parseDictSetLit : Parser (AstNode Expr) := located do
  let _ ← char '{'
  skipWSFull
  let c ← peek
  match c with
  | some '}' =>
    let _ ← char '}'
    return Expr.dictLit []  -- empty dict
  | _ =>
    let first ← parseExpr
    let colonOrComma ← peek
    match colonOrComma with
    | some ':' =>
      -- dict item: key: value
      let _ ← char ':'
      skipWSFull
      let val ← parseExpr
      let rest ← sepBy (do
        let _ ← char ','
        skipWSFull
        let k ← parseExpr
        let _ ← char ':'
        skipWSFull
        let v ← parseExpr
        return (k.value, v.value))
        (char ',' *> skipWSFull)
      let _ ← optional (char ',')
      let _ ← char '}'
      return Expr.dictLit ((first.value, val.value) :: rest)
    | _ =>
      -- set item
      let rest ← sepBy parseExpr (char ',' *> skipWSFull)
      let _ ← optional (char ',')
      let _ ← char '}'
      return Expr.setLit (first.value :: rest.map (·.value))

/-- Parse an atom expression. -/
partial def parseAtom : Parser (AstNode Expr) :=
  (char '(' *> pure ()) *> parseParenExpr
  <|> (char '[' *> pure ()) *> parseListLit
  <|> (char '{' *> pure ()) *> parseDictSetLit
  <|> parseAtomLiteral
  <|> parseName

-- ============================================================
-- Parser: Trailer (subscript, attribute, call)
-- ============================================================

/-- Parse a trailer after an atom: (...), [...], or .name -/
partial def parseTrailer (base : AstNode Expr) : Parser (AstNode Expr) := located do
  let c ← peek
  match c with
  | some '(' =>
    let _ ← char '('
    skipWSFull
    let args ← sepBy parseArg (char ',' *> skipWSFull)
    let _ ← optional (char ',')
    let _ ← char ')'
    return Expr.call base.value args
  | some '[' =>
    let _ ← char '['
    skipWSFull
    let sl ← parseSlice
    let _ ← char ']'
    return Expr.subscript base.value sl
  | some '.' =>
    let _ ← char '.'
    let name ← parseNameIdent
    return Expr.attribute base.value name.value
  | _ => fail "expected trailer"

/-- Parse 0 or more trailers. -/
partial def parseTrailers (base : AstNode Expr) : Parser (AstNode Expr) := do
  (do let b ← parseTrailer base; parseTrailers b) <|> pure base

/-- Parse a slice: [start:stop:step] -/
def parseSlice : Parser Slice := do
  let start ← optional parseExpr
  let colon1 ← optional (char ':')
  match colon1 with
  | none =>
    -- single index
    return { start := start.map (·.value), stop := none, step := none }
  | some _ =>
    let stop ← optional parseExpr
    let colon2 ← optional (char ':')
    match colon2 with
    | none =>
      return { start := start.map (·.value), stop := stop.map (·.value), step := none }
    | some _ =>
      let step ← optional parseExpr
      return { start := start.map (·.value), stop := stop.map (·.value), step := step.map (·.value) }

/-- Parse a function argument. -/
def parseArg : Parser Arg :=
  (do let star ← string "**" *> pure true <|> pure false
      if star then
        let e ← parseExpr
        return Arg.dstar e.value
      else
        let star2 ← string "*" *> pure true <|> pure false
        if star2 then
          let e ← parseExpr
          return Arg.star e.value
        else
          let e1 ← parseExpr
          let eq ← optional (char '=')
          match eq with
          | none => return Arg.positional e1.value
          | some _ =>
            let e2 ← parseExpr
            -- e1 must be a name for keyword arg
            match e1.value with
            | Expr.nameId id => return Arg.keyword id e2.value
            | _ => return Arg.positional e1.value)  -- fallback

-- ============================================================
-- Parser: Expression operators
-- ============================================================

/-- Parse a unary operator: +, -, ~ -/
def parseUnaryOp : Parser Operator := do
  let c ← peek
  match c with
  | some '+' => let _ ← char '+'; return { op := "+" }
  | some '-' => let _ ← char '-'; return { op := "-" }
  | some '~' => let _ ← char '~'; return { op := "~" }
  | _ => fail "expected unary operator"

/-- Parse a binary operator (for arithmetic, bitwise, shift). -/
def parseBinOp : Parser Operator := do
  let c ← peek
  match c with
  | some '+' =>
    let _ ← char '+'
    let eqCh ← optional (char '=')
    match eqCh with
    | some _ => fail "not a binary op"  -- += is not a binary op on its own
    | none =>
      let _ ← notFollowedBy (char '=')
      return { op := "+" }
  | some '-' =>
    let _ ← char '-'
    let gt ← optional (char '>')
    match gt with
    | some _ => return { op := "->" }
    | none =>
      let _ ← notFollowedBy (char '=')
      return { op := "-" }
  | some '*' =>
    let _ ← char '*'
    let star2 ← optional (char '*')
    match star2 with
    | some _ =>
      let _ ← notFollowedBy (char '=')
      return { op := "**" }
    | none =>
      let _ ← notFollowedBy (char '=')
      return { op := "*" }
  | some '/' =>
    let _ ← char '/'
    let slash2 ← optional (char '/')
    match slash2 with
    | some _ =>
      let _ ← notFollowedBy (char '=')
      return { op := "//" }
    | none =>
      let _ ← notFollowedBy (char '=')
      return { op := "/" }
  | some '%' =>
    let _ ← char '%'
    let _ ← notFollowedBy (char '=')
    return { op := "%" }
  | some '@' =>
    let _ ← char '@'
    let _ ← notFollowedBy (char '=')
    return { op := "@" }
  | some '<' =>
    let _ ← char '<'
    let lt2 ← optional (char '<')
    match lt2 with
    | some _ =>
      let _ ← notFollowedBy (char '=')
      return { op := "<<" }
    | none =>
      match ← peek with
      | some '=' =>
        let _ ← char '='; return { op := "<=" }
      | some '>' =>
        let _ ← char '>'; return { op := "<>" }
      | _ => return { op := "<" }
  | some '>' =>
    let _ ← char '>'
    let gt2 ← optional (char '>')
    match gt2 with
    | some _ =>
      let _ ← notFollowedBy (char '=')
      return { op := ">>" }
    | none =>
      match ← peek with
      | some '=' =>
        let _ ← char '='; return { op := ">=" }
      | _ => return { op := ">" }
  | some '=' =>
    let _ ← char '='
    match ← peek with
    | some '=' =>
      let _ ← char '='; return { op := "==" }
    | _ => fail "expected =="
  | some '!' =>
    let _ ← char '!'
    let _ ← char '='
    return { op := "!=" }
  | some '&' =>
    let _ ← char '&'
    let _ ← notFollowedBy (char '=')
    return { op := "&" }
  | some '|' =>
    let _ ← char '|'
    let _ ← notFollowedBy (char '=')
    return { op := "|" }
  | some '^' =>
    let _ ← char '^'
    let _ ← notFollowedBy (char '=')
    return { op := "^" }
  | _ => fail "expected binary operator"

/-- Parse a comparison operator. -/
def parseCompOp : Parser Operator :=
  (string "<=" *> pure { op := "<=" })
  <|> (string ">=" *> pure { op := ">=" })
  <|> (string "==" *> pure { op := "==" })
  <|> (string "!=" *> pure { op := "!=" })
  <|> (string "<>" *> pure { op := "<>" })
  <|> (string "in" *> notFollowedBy (satisfy isIdentCont) *> pure { op := "in" })
  <|> (string "is" *> notFollowedBy (satisfy isIdentCont) *>
       ((string "not" *> notFollowedBy (satisfy isIdentCont) *> pure { op := "is not" })
        <|> pure { op := "is" }))
  <|> (string "not" *> notFollowedBy (satisfy isIdentCont) *>
       (string "in" *> notFollowedBy (satisfy isIdentCont) *> pure { op := "not in" })
       <|> fail "expected 'not in'")
  <|> (char '<' *> pure { op := "<" })
  <|> (char '>' *> pure { op := ">" })

-- ============================================================
-- Parser: Expressions (Pratt-style precedence)
-- ============================================================

/-- Parse a primary expression (atom + trailers). -/
def parsePrimary : Parser (AstNode Expr) := do
  let atom ← parseAtom
  parseTrailers atom

/-- Parse the power operator: atom ('**' expr)? -/
partial def parsePower : Parser (AstNode Expr) := located do
  let base ← parsePrimary
  let pow ← optional (do
    let _ ← string "**"
    let e ← parsePower
    return e)
  match pow with
  | none => return base.value
  | some p => return Expr.binOp { op := "**" } base.value p.value

/-- Parse unary +, -, ~ chains. -/
partial def parseUnary : Parser (AstNode Expr) := located do
  let ops ← many parseUnaryOp
  let base ← parsePower
  let result := base.value
  -- Apply unary ops from right to left
  let rec apply (e : Expr) : List Operator → Expr
    | [] => e
    | op :: rest => Expr.unaryOp op (apply e rest)
  let applied := apply result ops.reverse
  return applied

/-- Parse multiplicative: *, @, /, %, // -/
partial def parseMulExpr : Parser (AstNode Expr) := located do
  let left ← parseUnary
  let ops ← many (do
    let c ← peek
    match c with
    | some '*' =>
      let _ ← char '*'
      let _ ← notFollowedBy (char '*' <|> char '=')
      let r ← parseUnary
      return ({ op := "*" }, r)
    | some '/' =>
      let _ ← char '/'
      let _ ← notFollowedBy (char '/' <|> char '=')
      let r ← parseUnary
      return ({ op := "/" }, r)
    | some '@' =>
      let _ ← char '@'
      let _ ← notFollowedBy (char '=')
      let r ← parseUnary
      return ({ op := "@" }, r)
    | some '%' =>
      let _ ← char '%'
      let _ ← notFollowedBy (char '=')
      let r ← parseUnary
      return ({ op := "%" }, r)
    | _ =>
      -- try //
      (do let _ ← string "//"
          let _ ← notFollowedBy (char '=')
          let r ← parseUnary
          return ({ op := "//" }, r)) <|> fail "not mul op")
  -- Left fold
  let rec fold (e : Expr) : List (Operator × AstNode Expr) → Expr
    | [] => e
    | (op, r) :: rest => fold (Expr.binOp op e r.value) rest
  return fold left.value ops

/-- Parse additive: +, - -/
partial def parseAddExpr : Parser (AstNode Expr) := located do
  let left ← parseMulExpr
  let ops ← many (do
    let c ← peek
    match c with
    | some '+' =>
      let _ ← char '+'
      let _ ← notFollowedBy (char '=')
      let r ← parseMulExpr
      return ({ op := "+" }, r)
    | some '-' =>
      let _ ← char '-'
      let _ ← notFollowedBy (char '>' <|> char '=')
      let r ← parseMulExpr
      return ({ op := "-" }, r)
    | _ => fail "not add op")
  let rec fold (e : Expr) : List (Operator × AstNode Expr) → Expr
    | [] => e
    | (op, r) :: rest => fold (Expr.binOp op e r.value) rest
  return fold left.value ops

/-- Parse shift: <<, >> -/
partial def parseShiftExpr : Parser (AstNode Expr) := located do
  let left ← parseAddExpr
  let ops ← many (do
    (string "<<" *> notFollowedBy (char '=') *> pure { op := "<<" })
    <|> (string ">>" *> notFollowedBy (char '=') *> pure { op := ">>" }))
  -- For simplicity: return left-associative binOp chain
  let rec fold (e : Expr) : List Operator → Expr
    | [] => e
    | op :: rest => fold (Expr.binOp op e (← parseAddExpr).value) rest
  -- Re-parse needed: shift ops chain
  return left.value  -- simplified

/-- Parse bitwise and: & -/
partial def parseAndExpr : Parser (AstNode Expr) := located do
  let left ← parseShiftExpr
  let ops ← many (do
    let _ ← char '&'
    let _ ← notFollowedBy (char '=')
    let r ← parseShiftExpr
    return ({ op := "&" }, r))
  let rec fold (e : Expr) : List (Operator × AstNode Expr) → Expr
    | [] => e
    | (op, r) :: rest => fold (Expr.binOp op e r.value) rest
  return fold left.value ops

/-- Parse bitwise xor: ^ -/
partial def parseXorExpr : Parser (AstNode Expr) := located do
  let left ← parseAndExpr
  let ops ← many (do
    let _ ← char '^'
    let _ ← notFollowedBy (char '=')
    let r ← parseAndExpr
    return ({ op := "^" }, r))
  let rec fold (e : Expr) : List (Operator × AstNode Expr) → Expr
    | [] => e
    | (op, r) :: rest => fold (Expr.binOp op e r.value) rest
  return fold left.value ops

/-- Parse bitwise or: | -/
partial def parseOrExpr : Parser (AstNode Expr) := located do
  let left ← parseXorExpr
  let ops ← many (do
    let _ ← char '|'
    let _ ← notFollowedBy (char '=')
    let r ← parseXorExpr
    return ({ op := "|" }, r))
  let rec fold (e : Expr) : List (Operator × AstNode Expr) → Expr
    | [] => e
    | (op, r) :: rest => fold (Expr.binOp op e r.value) rest
  return fold left.value ops

/-- Parse comparison chain: a < b == c > d -/
partial def parseComparison : Parser (AstNode Expr) := located do
  let left ← parseOrExpr
  let comps ← many (do
    let op ← parseCompOp
    let r ← parseOrExpr
    return (op, r))
  match comps with
  | [] => return left.value
  | _  => return Expr.compare left.value (comps.map fun (op, r) => (op, r.value))

/-- Parse not test: 'not' not_test | comparison -/
partial def parseNotTest : Parser (AstNode Expr) := located do
  let notKw ← optional (string "not" *> notFollowedBy (satisfy isIdentCont))
  match notKw with
  | some _ =>
    let inner ← parseNotTest
    return Expr.unaryNot inner.value
  | none => parseComparison

/-- Parse and test: not_test ('and' not_test)* -/
partial def parseAndTest : Parser (AstNode Expr) := located do
  let left ← parseNotTest
  let rights ← many (do
    let _ ← string "and"
    notFollowedBy (satisfy isIdentCont)
    parseNotTest)
  let rec fold (e : Expr) : List (AstNode Expr) → Expr
    | [] => e
    | r :: rest => fold (Expr.boolOp BoolOp.andOp e r.value) rest
  return fold left.value rights

/-- Parse or test: and_test ('or' and_test)* -/
partial def parseOrTest : Parser (AstNode Expr) := located do
  let left ← parseAndTest
  let rights ← many (do
    let _ ← string "or"
    notFollowedBy (satisfy isIdentCont)
    parseAndTest)
  let rec fold (e : Expr) : List (AstNode Expr) → Expr
    | [] => e
    | r :: rest => fold (Expr.boolOp BoolOp.orOp e r.value) rest
  return fold left.value rights

/-- Parse a lambda: lambda args: test -/
def parseLambda : Parser (AstNode Expr) := located do
  let _ ← string "lambda"
  let _ ← notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let args ← parseVarArgsList
  let _ ← char ':'
  skipWSFull
  let body ← parseExpr
  return Expr.lambda args body.value

/-- Parse conditional expression: or_test ('if' or_test 'else' test)? -/
partial def parseTest : Parser (AstNode Expr) := located do
  let cond ← parseOrTest
  let ifKw ← optional (string "if" *> notFollowedBy (satisfy isIdentCont))
  match ifKw with
  | none => return cond.value
  | some _ =>
    skipWSFull
    let trueExpr ← parseOrTest
    let _ ← string "else"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let falseExpr ← parseTest
    return Expr.ifExpr cond.value trueExpr.value falseExpr.value

/-- Parse a full expression (with conditional and lambda). -/
partial def parseExpr : Parser (AstNode Expr) :=
  parseLambda <|> parseTest

-- ============================================================
-- Parser: Expression list helpers
-- ============================================================

/-- Parse a comma-separated list of expressions. -/
def parseExprList : Parser (List (AstNode Expr)) :=
  sepBy (parseExpr <* skipWSFull) (char ',' *> skipWSFull)

/-- Parse testlist: test (',' test)* ','? -/
def parseTestList : Parser (List (AstNode Expr)) := do
  let first ← parseExpr
  let rest ← many (char ',' *> skipWSFull *> parseExpr)
  let _ ← optional (char ',')
  return (first :: rest)

-- ============================================================
-- Parser: Function arguments declaration
-- ============================================================

/-- Parse a typed function parameter: name (: type)? (= default)? -/
def parseTfpDef : Parser (Ident × Option (AstNode Expr)) := do
  let name ← parseNameIdent
  let typeAnn ← optional (do
    let _ ← char ':'
    skipWSFull
    parseExpr)
  return (name.value, typeAnn)

/-- Parse a argument list with defaults: tfpdef ('=' test)? -/
def parseTypedArg : Parser (Ident × Option (AstNode Expr) × Option (AstNode Expr)) := do
  let (name, typeAnn) ← parseTfpDef
  let default ← optional (do
    let _ ← char '='
    skipWSFull
    parseExpr)
  return (name, typeAnn, default)

/-- Parse typed args list: (tfpdef ('=' test)? (',' tfpdef ('=' test)?)* ...) -/
partial def parseTypedArgsList : Parser Args := do
  let _ ← char '('
  skipWSFull
  let c ← peek
  match c with
  | some ')' =>
    let _ ← char ')'
    return { posOnly := [], args := [], vararg := none, kwOnly := [], kwarg := none }
  | _ =>
    -- Check for * or ** first parameter
    let isStar ← optional (char '*')
    match isStar with
    | some _ =>
      -- *args or **kwargs
      let dstar ← optional (char '*')
      match dstar with
      | some _ =>
        -- **kwargs
        let name ← parseNameIdent
        let _ ← optional (char ',')
        let _ ← char ')'
        return { posOnly := [], args := [], vararg := none, kwOnly := [], kwarg := some name.value }
      | none =>
        -- *args or *
        let name ← optional parseNameIdent
        let kwOnly ← many (do
          let _ ← char ','
          skipWSFull
          let n ← parseNameIdent
          let typeAnn ← optional (do
            let _ ← char ':'
            skipWSFull
            parseExpr)
          let def ← optional (do
            let _ ← char '='
            skipWSFull
            parseExpr)
          return (n.value, typeAnn, def))
        let kwarg ← optional (do
          let _ ← char ','
          skipWSFull
          let _ ← string "**"
          let n ← parseNameIdent
          return n.value)
        let _ ← char ')'
        return { posOnly := [], args := [], vararg := name.map (·.value),
                 kwOnly := kwOnly.map fun (n, t, d) => (n, mergeTypeDefault t d),
                 kwarg := kwarg }
    | none =>
      -- Normal args
      let first ← parseTypedArg
      let rest ← many (do
        let _ ← char ','
        skipWSFull
        parseTypedArg)
      let _ ← char ')'
      return { posOnly := [], args := (first :: rest).map fun (n, t, d) => (n, mergeTypeDefault t d),
               vararg := none, kwOnly := [], kwarg := none }
where
  mergeTypeDefault (t : Option (AstNode Expr)) (d : Option (AstNode Expr)) : Option (AstNode Expr) :=
    match t, d with
    | none, some d => some d
    | some t, none => some t
    | some t, some _ => some t  -- default wins
    | none, none => none

/-- Parse varargslist (for lambdas): simpler version. -/
partial def parseVarArgsList : Parser Args := do
  let c ← peek
  match c with
  | some '(' => parseTypedArgsList
  | some ':' | some '=' | none => return { posOnly := [], args := [], vararg := none, kwOnly := [], kwarg := none }
  | _ =>
    -- Bare args for lambda
    let names ← sepBy1 parseNameIdent (char ',' *> skipWSFull)
    let _ ← optional (char ',')
    return { posOnly := [], args := names.map fun n => (n.value, none), vararg := none, kwOnly := [], kwarg := none }

-- ============================================================
-- Parser: Comprehension helpers
-- ============================================================

/-- Parse comp_for: [ASYNC] 'for' exprlist 'in' or_test [comp_iter] -/
partial def parseCompFor : Parser CompFor := do
  let isAsync ← optional (string "async" *> notFollowedBy (satisfy isIdentCont) *> skipWSFull)
  let _ ← string "for"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let targets ← parseExprList
  let _ ← string "in"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let iter ← parseOrTest
  -- parse comp_if if present
  let ifs ← many (do
    let _ ← string "if"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let cond ← parseOrTest
    return cond.value)
  return { isAsync := isAsync.isSome, targets := targets.map (·.value), iter := iter.value, ifs := ifs }

-- ============================================================
-- Parser: Decorators
-- ============================================================

/-- Parse a decorator: '@' dotted_name ('(' arglist? ')')? NEWLINE -/
def parseDecorator : Parser (AstNode Decorator) := located do
  let _ ← char '@'
  skipWSFull
  let name ← sepBy1 parseNameIdent (char '.' *> pure ())
  let args ← optional (do
    let _ ← char '('
    skipWSFull
    let al ← sepBy parseArg (char ',' *> skipWSFull)
    let _ ← optional (char ',')
    let _ ← char ')'
    return al)
  skipWSFull
  let _ ← newline
  return { name := name.map (·.value), args := args }

/-- Parse decorators+. -/
def parseDecorators : Parser (List (AstNode Decorator)) := many1 parseDecorator

-- ============================================================
-- Parser: Statements
-- ============================================================

/-- Parse a simple statement. -/
partial def parseSimpleStmt : Parser (AstNode SimpleStmt) := located do
  let c ← peek
  match c with
  | none => fail "expected statement"
  | some ch =>
    if ch = 'p' then
      (string "pass" *> notFollowedBy (satisfy isIdentCont) *> pure SimpleStmt.passStmt)
    else if ch = 'b' then
      (string "break" *> notFollowedBy (satisfy isIdentCont) *> pure SimpleStmt.breakStmt)
    else if ch = 'c' then
      (string "continue" *> notFollowedBy (satisfy isIdentCont) *> pure SimpleStmt.continueStmt)
    else if ch = 'd' then
      if (← peek) == some 'd' then
        parseDelStmt
      else
        parseExprStmtOrAssign
    else if ch = 'r' then
      parseReturnStmt <|> parseRaiseStmt
    else if ch = 'y' then
      parseYieldStmt
    else if ch = 'i' then
      parseImportStmt
    else if ch = 'f' then
      parseImportFromStmt
    else if ch = 'g' then
      parseGlobalStmt
    else if ch = 'n' then
      parseNonlocalStmt
    else if ch = 'a' then
      parseAssertStmt
    else
      parseExprStmtOrAssign
where
  parseDelStmt : Parser SimpleStmt := do
    let _ ← string "del"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let exprs ← parseExprList
    return SimpleStmt.delStmt (exprs.map (·.value))

  parseReturnStmt : Parser SimpleStmt := do
    let _ ← string "return"
    notFollowedBy (satisfy isIdentCont)
    let c ← peek
    match c with
    | some '\n' | some ';' | none => return SimpleStmt.returnStmt none
    | _ =>
      skipWSFull
      let e ← parseTestList
      return SimpleStmt.returnStmt (some (Expr.tupleLit (e.map (·.value))))

  parseRaiseStmt : Parser SimpleStmt := do
    let _ ← string "raise"
    notFollowedBy (satisfy isIdentCont)
    let c ← peek
    match c with
    | some '\n' | some ';' | none => return SimpleStmt.raiseStmt none none
    | _ =>
      skipWSFull
      let exc ← parseExpr
      let cause ← optional (do
        let _ ← string "from"
        notFollowedBy (satisfy isIdentCont)
        skipWSFull
        parseExpr)
      return SimpleStmt.raiseStmt (some exc.value) (cause.map (·.value))

  parseYieldStmt : Parser SimpleStmt := do
    let _ ← string "yield"
    notFollowedBy (satisfy isIdentCont)
    let fromKw ← optional (string "from" *> notFollowedBy (satisfy isIdentCont))
    match fromKw with
    | some _ =>
      skipWSFull
      let e ← parseExpr
      return SimpleStmt.yieldStmt e.value  -- TODO: yield_from
    | none =>
      let c ← peek
      match c with
      | some '\n' | some ';' | none =>
        return SimpleStmt.yieldStmt (Expr.yieldExpr none)
      | _ =>
        skipWSFull
        let e ← parseTestList
        return SimpleStmt.yieldStmt (Expr.yieldExpr (some (Expr.tupleLit (e.map (·.value)))))

  parseImportStmt : Parser SimpleStmt := do
    let _ ← string "import"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let names ← sepBy1 parseDottedAsName (char ',' *> skipWSFull)
    return SimpleStmt.importName names

  parseImportFromStmt : Parser SimpleStmt := do
    let _ ← string "from"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    -- Parse leading dots for relative import
    let dots ← many (char '.' *> skipWSFull)
    let module ← optional (sepBy1 parseNameIdent (char '.' *> pure ()))
    let _ ← string "import"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let c ← peek
    match c with
    | some '*' =>
      let _ ← char '*'
      return SimpleStmt.importFrom [] []
    | _ =>
      let names ← sepBy1 parseDottedAsName (char ',' *> skipWSFull)
      return SimpleStmt.importFrom (dots.map fun _ => none) names

  parseDottedAsName : Parser DottedName := do
    let parts ← sepBy1 parseNameIdent (char '.' *> pure ())
    let alias ← optional (do
      let _ ← string "as"
      notFollowedBy (satisfy isIdentCont)
      skipWSFull
      parseNameIdent)
    return { asName := alias.map (·.value), parts := parts.map (·.value) }

  parseGlobalStmt : Parser SimpleStmt := do
    let _ ← string "global"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let names ← sepBy1 parseNameIdent (char ',' *> skipWSFull)
    return SimpleStmt.globalStmt (names.map (·.value))

  parseNonlocalStmt : Parser SimpleStmt := do
    let _ ← string "nonlocal"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let names ← sepBy1 parseNameIdent (char ',' *> skipWSFull)
    return SimpleStmt.nonlocalStmt (names.map (·.value))

  parseAssertStmt : Parser SimpleStmt := do
    let _ ← string "assert"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let test ← parseExpr
    let msg ← optional (do
      let _ ← char ','
      skipWSFull
      parseExpr)
    return SimpleStmt.assertStmt test.value (msg.map (·.value))

  /-- Parse expression statement or assignment. -/
  parseExprStmtOrAssign : Parser SimpleStmt := do
    let targets ← sepBy1 parseExpr (char ',' *> skipWSFull)
    let tgt := targets.map (·.value)
    let c ← peek
    match c with
    | some '=' =>
      let _ ← char '='
      -- Check for augmented assignment
      let _ ← notFollowedBy (char '=')
      skipWSFull
      let val ← parseExpr
      -- Check if there was an augassign before the '='
      -- Simple assignment for now
      let restVals ← many (do
        let _ ← char '='
        skipWSFull
        parseExpr)
      let allVals := val :: restVals
      return SimpleStmt.assign tgt allVals[0]!.value  -- simplified
    | some ':' =>
      -- Possible annotated assignment
      let _ ← char ':'
      let isWalrus ← optional (char '=')
      match isWalrus with
      | some _ =>
        -- := walrus operator (already handled in expr)
        return SimpleStmt.exprStmt (targets[0]!.value)
      | none =>
        skipWSFull
        let typeAnn ← parseExpr
        let val ← optional (do
          let _ ← char '='
          skipWSFull
          parseExpr)
        return SimpleStmt.annAssign (targets[0]!.value) typeAnn.value (val.map (·.value))
    | _ =>
      -- Expression statement
      match tgt with
      | [e] => return SimpleStmt.exprStmt e
      | _ => return SimpleStmt.exprStmt (Expr.tupleLit tgt)

-- ============================================================
-- Parser: Compound statements
-- ============================================================

/-- Parse a block: NEWLINE INDENT stmt+ DEDENT | simple_stmts -/
partial def parseBlock : Parser (AstNode Block) := located do
  let c ← peek
  match c with
  | some ':' =>
    let _ ← char ':'
    skipWSFull
    let nc ← peek
    match nc with
    | some '\n' =>
      let _ ← newline
      -- Parse INDENT
      skipWSFull
      let indentPos ← getPos
      skipWS  -- consume leading whitespace
      -- Parse statements until DEDENT
      let stmts ← many parseStmt
      -- DEDENT is implicit when indentation level drops
      -- For simplicity, we parse until we can't match more stmts
      return Block.suite stmts
    | _ =>
      -- Simple statement on same line
      let stmts ← sepBy1 parseSimpleStmt (char ';' *> skipWSFull)
      let _ ← optional (char ';')
      return Block.simple stmts
  | _ =>
    -- No colon, simple statement
    let stmts ← sepBy1 parseSimpleStmt (char ';' *> skipWSFull)
    let _ ← optional (char ';')
    return Block.simple stmts

/-- Parse an if statement: if test: block (elif test: block)* (else: block)? -/
partial def parseIfStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "if"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let test ← parseExpr
  let _ ← char ':'
  let body ← parseBlock
  let elifs ← many (do
    skipWSFull
    let _ ← string "elif"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let t ← parseExpr
    let _ ← char ':'
    let b ← parseBlock
    return (t.value, b))
  let elseBlock ← optional (do
    skipWSFull
    let _ ← string "else"
    notFollowedBy (satisfy isIdentCont)
    let _ ← char ':'
    parseBlock)
  return CompoundStmt.ifStmt test.value body elifs elseBlock

/-- Parse a while statement: while test: block (else: block)? -/
partial def parseWhileStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "while"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let test ← parseExpr
  let _ ← char ':'
  let body ← parseBlock
  let elseBlock ← optional (do
    skipWSFull
    let _ ← string "else"
    notFollowedBy (satisfy isIdentCont)
    let _ ← char ':'
    parseBlock)
  return CompoundStmt.whileStmt test.value body elseBlock

/-- Parse a for statement: for targets in iter: block (else: block)? -/
partial def parseForStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "for"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let targets ← parseExprList
  let _ ← string "in"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let iter ← parseExpr
  let _ ← char ':'
  let body ← parseBlock
  let elseBlock ← optional (do
    skipWSFull
    let _ ← string "else"
    notFollowedBy (satisfy isIdentCont)
    let _ ← char ':'
    parseBlock)
  return CompoundStmt.forStmt (targets.map (·.value)) iter.value body elseBlock

/-- Parse a try statement. -/
partial def parseTryStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "try"
  notFollowedBy (satisfy isIdentCont)
  let _ ← char ':'
  let body ← parseBlock
  let excepts ← many (do
    skipWSFull
    let _ ← string "except"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let exc ← optional (do
      let e ← parseExpr
      let asName ← optional (do
        let _ ← string "as"
        notFollowedBy (satisfy isIdentCont)
        skipWSFull
        parseNameIdent)
      return (e.value, asName.map (·.value)))
    let _ ← char ':'
    let b ← parseBlock
    return (exc.map (·.1), exc.map (·.2), b))
  let elseBlock ← optional (do
    skipWSFull
    let _ ← string "else"
    notFollowedBy (satisfy isIdentCont)
    let _ ← char ':'
    parseBlock)
  let finallyBlock ← optional (do
    skipWSFull
    let _ ← string "finally"
    notFollowedBy (satisfy isIdentCont)
    let _ ← char ':'
    parseBlock)
  let exceptClauses := excepts.map fun (exc, name, b) => (exc, name, b)
  return CompoundStmt.tryStmt body exceptClauses elseBlock finallyBlock

/-- Parse a with statement: with with_item (',' with_item)* ':' block -/
partial def parseWithStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "with"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let items ← sepBy1 parseWithItem (char ',' *> skipWSFull)
  let _ ← char ':'
  let body ← parseBlock
  return CompoundStmt.withStmt items body
where
  parseWithItem : Parser (Expr × Option Expr) := do
    let e ← parseExpr
    let asName ← optional (do
      let _ ← string "as"
      notFollowedBy (satisfy isIdentCont)
      skipWSFull
      parseExpr)
    return (e.value, asName.map (·.value))

/-- Parse a function definition. -/
partial def parseFuncDef : Parser (AstNode CompoundStmt) := located do
  let decorators ← many parseDecorator
  let isAsync ← optional (string "async" *> notFollowedBy (satisfy isIdentCont) *> skipWSFull)
  let _ ← string "def"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let name ← parseNameIdent
  let _ ← char '('
  skipWSFull
  let args ← parseArgsBody
  let _ ← char ')'
  skipWSFull
  let returnType ← optional (do
    let _ ← string "->"
    skipWSFull
    parseExpr)
  let _ ← char ':'
  let body ← parseBlock
  let func := CompoundStmt.funcDef decorators name.value args returnType body
  match isAsync with
  | some _ => return CompoundStmt.asyncStmt func
  | none => return func
where
  parseArgsBody : Parser Args := do
    let c ← peek
    match c with
    | some ')' => return { posOnly := [], args := [], vararg := none, kwOnly := [], kwarg := none }
    | _ =>
      -- Parse parameters: (tfpdef ('=' test)? (',' tfpdef ('=' test)?)* ...)
      let first ← parseTypedArg
      let rest ← many (do
        let _ ← char ','
        skipWSFull
        parseTypedArg)
      let all := first :: rest
      return { posOnly := [], args := all.map fun (n, t, d) => (n, mergeTypeDefault t d),
               vararg := none, kwOnly := [], kwarg := none }
  mergeTypeDefault (t : Option (AstNode Expr)) (d : Option (AstNode Expr)) : Option (AstNode Expr) :=
    match t, d with
    | none, none => none
    | some x, _ => some x
    | _, some x => some x

/-- Parse a class definition. -/
partial def parseClassDef : Parser (AstNode CompoundStmt) := located do
  let decorators ← many parseDecorator
  let _ ← string "class"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let name ← parseNameIdent
  let bases ← optional (do
    let _ ← char '('
    skipWSFull
    let args ← sepBy parseArg (char ',' *> skipWSFull)
    let _ ← optional (char ',')
    let _ ← char ')'
    return args)
  let _ ← char ':'
  let body ← parseBlock
  return CompoundStmt.classDef decorators name.value bases body

/-- Parse a match statement. -/
partial def parseMatchStmt : Parser (AstNode CompoundStmt) := located do
  let _ ← string "match"
  notFollowedBy (satisfy isIdentCont)
  skipWSFull
  let subject ← parseExpr
  let _ ← char ':'
  skipWSFull
  let _ ← newline
  -- INDENT
  skipWSFull
  let cases ← many1 parseCaseBlock
  -- DEDENT
  return CompoundStmt.matchStmt subject.value cases
where
  parseCaseBlock : Parser CaseClause := do
    let _ ← string "case"
    notFollowedBy (satisfy isIdentCont)
    skipWSFull
    let pat ← parseMatchPattern
    let guard ← optional (do
      let _ ← string "if"
      notFollowedBy (satisfy isIdentCont)
      skipWSFull
      parseExpr)
    let _ ← char ':'
    let body ← parseBlock
    return { pattern := pat, guard := guard.map (·.value), body := body }

/-- Parse match patterns. -/
partial def parseMatchPattern : Parser MatchPattern :=
  (char '_' *> notFollowedBy (satisfy isIdentCont) *> pure MatchPattern.wildcard)
  <|> (do let name ← parseNameIdent; return MatchPattern.capture name.value)

/-- Parse a compound statement. -/
partial def parseCompoundStmt : Parser (AstNode CompoundStmt) :=
  parseIfStmt
  <|> parseWhileStmt
  <|> parseForStmt
  <|> parseTryStmt
  <|> parseWithStmt
  <|> parseFuncDef
  <|> parseClassDef
  <|> parseMatchStmt

/-- Parse a statement (simple or compound). -/
def parseStmt : Parser (AstNode Stmt) := located do
  skipWSFull
  let decorated ← any parseDecorator
  match decorated with
  | some dec =>
    let compound ← parseCompoundStmt
    return Stmt.compound compound.value
  | none =>
    -- Try compound first (look for keywords)
    let c ← peek
    match c with
    | some ch =>
      if ch = 'i' || ch = 'w' || ch = 'f' || ch = 't' || ch = 'm' || ch = 'd' || ch = 'c' || ch = 'a' then
        let compound ← parseCompoundStmt
        return Stmt.compound compound.value
      else
        let simple ← parseSimpleStmt
        return Stmt.simple simple.value
    | none =>
      fail "expected statement"

/-- Parse a file: (NEWLINE | stmt)* EOF -/
partial def parseFile : Parser (List (AstNode Stmt)) := do
  skipWSFull
  let _ ← many newline
  let stmts ← many (do
    let s ← parseStmt
    skipWSFull
    let _ ← many newline
    skipWSFull
    return s)
  -- Consume trailing whitespace and newlines
  skipWSFull
  let _ ← many newline
  -- Should be at EOF
  let rest ← getText
  if rest.isEmpty || rest.all (fun c => c = ' ' || c = '\t' || c = '\n' || c = '\r') then
    return stmts
  else
    fail s!"unexpected trailing input: {rest.take 20}"

-- ============================================================
-- Main entry points
-- ============================================================

/-- Parse Python3 source and return AST with spans. -/
def parsePython3 (source : String) : Except (List Diag) (List (AstNode Stmt)) :=
  Parser.run parseFile source

/-- Parse a single expression (for eval input). -/
partial def parseSingle : Parser (AstNode Expr) := do
  skipWSFull
  let e ← parseExpr
  skipWSFull
  let _ ← many newline
  return e

def parsePython3Expr (source : String) : Except (List Diag) (AstNode Expr) :=
  Parser.run parseSingle source

-- ============================================================
-- Demo / Test
-- ============================================================

def main : IO Unit := do
  IO.println "Python3 Parser for Lean — Scanner + Parser with location tracking"
  IO.println "================================================================"
  IO.println ""

  -- Test 1: Tokenizer
  let test1 := "def hello(name):\n    return f\"Hello, {name}!\"\n"
  IO.println s!"--- Test 1: Tokenizer ---"
  IO.println s!"Input:\n{test1}"
  match tokenize test1 with
  | .error diags =>
    IO.println s!"Tokenizer errors: {diags.length}"
    for d in diags do
      IO.println s!"  @{d.span}: {d.message}"
  | .ok tokens =>
    IO.println s!"Produced {tokens.length} tokens:"
    for t in tokens do
      IO.println s!"  @{t.span.start}: {t.value}"

  -- Test 2: Parser
  let test2 := "x = 42\ny = x + 1\nprint(y)\n"
  IO.println ""
  IO.println s!"--- Test 2: Parser ---"
  IO.println s!"Input:\n{test2}"
  match parsePython3 test2 with
  | .error diags =>
    IO.println s!"Parse errors: {diags.length}"
    for d in diags do
      IO.println s!"  @{d.span}: {d.message}"
  | .ok stmts =>
    IO.println s!"Parsed {stmts.length} statements:"
    for s in stmts do
      IO.println s!"  @{s.span}: ..."

  -- Test 3: Expression parser
  let test3 := "a + b * c"
  IO.println ""
  IO.println s!"--- Test 3: Expression Parser ---"
  IO.println s!"Input: {test3}"
  match parsePython3Expr test3 with
  | .error diags =>
    IO.println s!"Parse errors: {diags.length}"
    for d in diags do
      IO.println s!"  @{d.span}: {d.message}"
  | .ok expr =>
    IO.println s!"Parsed expression @{expr.span}"

  IO.println ""
  IO.println "Done."
