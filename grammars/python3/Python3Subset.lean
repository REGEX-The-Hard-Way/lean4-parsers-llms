/-
Python3 Subset Parser for Lean — Scanner + Parser with location tracking.
Testable, self-contained.
-/

namespace LeanParser

structure SourcePos where
  line   : Nat
  column : Nat
  offset : Nat
deriving Repr, BEq, Inhabited

instance : ToString SourcePos where
  toString p := s!"{p.line+1}:{p.column+1}"

def startPos : SourcePos := { line := 0, column := 0, offset := 0 }

def SourcePos.advance (p : SourcePos) (c : Char) : SourcePos :=
  if c = '\n' then
    { line := p.line + 1, column := 0, offset := p.offset + 1 }
  else
    { line := p.line, column := p.column + 1, offset := p.offset + 1 }

def SourcePos.advanceString (p : SourcePos) (s : String) : SourcePos :=
  s.foldl (fun pos c => pos.advance c) p

structure Span where
  start : SourcePos
  stop  : SourcePos
deriving Repr, BEq, Inhabited

def Span.ofString (start : SourcePos) (s : String) : Span :=
  { start := start, stop := start.advanceString s }

structure Located (α : Type) where
  value : α
  span  : Span
deriving Repr, BEq, Inhabited

def Located.at (val : α) (span : Span) : Located α :=
  { value := val, span := span }

structure Diag where
  span    : Span
  message : String
deriving Repr, BEq

structure Input where
  text : String
  pos  : SourcePos
deriving Repr, BEq

def Input.ofString (s : String) : Input :=
  { text := s, pos := startPos }

def Input.isEOF (i : Input) : Bool :=
  i.text.isEmpty

def Input.peek (i : Input) : Option Char :=
  if i.text.isEmpty then none else some (i.text.get ⟨0⟩)

def Input.advance (i : Input) : Input :=
  if i.text.isEmpty then i
  else
    let c := i.text.get ⟨0⟩
    { text := (i.text.drop 1).toString, pos := i.pos.advance c }

inductive StepResult (α : Type) where
  | success : α → Input → StepResult α
  | failure : List Diag → StepResult α

def Parser (α : Type) : Type := Input → StepResult α

namespace Parser

def run (p : Parser α) (s : String) : Except (List Diag) α :=
  match p (Input.ofString s) with
  | .success val _ => .ok val
  | .failure diags => .error diags

instance : Monad Parser where
  pure a := fun i => .success a i
  bind p f := fun i =>
    match p i with
    | .success val rest => f val rest
    | .failure diags => .failure diags

instance : Alternative Parser where
  failure := fun i => .failure [{ span := Span.ofString i.pos i.text, message := "parse failure" }]
  orElse p q := fun i =>
    match p i with
    | .success val rest => .success val rest
    | .failure _ =>
      match q () i with
      | .success val rest => .success val rest
      | .failure diags => .failure diags

def fail (msg : String) : Parser α := fun i =>
  .failure [{ span := Span.ofString i.pos i.text, message := msg }]

def getPos : Parser SourcePos := fun i => .success i.pos i

def getSpan (start : SourcePos) : Parser Span := do
  let p ← getPos
  return { start := start, stop := p }

def located (p : Parser α) : Parser (Located α) := do
  let p0 ← getPos
  let val ← p
  let p1 ← getPos
  return Located.at val { start := p0, stop := p1 }

def peek : Parser (Option Char) := fun i => .success (i.peek) i

def satisfy (pred : Char → Bool) : Parser Char := fun i =>
  match i.peek with
  | none => .failure [{ span := Span.ofString i.pos "", message := "unexpected end of input" }]
  | some c =>
    if pred c then .success c i.advance
    else .failure [{ span := Span.ofString i.pos (toString c), message := s!"unexpected character '{c}'" }]

def char (c : Char) : Parser Char := satisfy (fun x => x = c)

partial def string (s : String) : Parser Unit :=
  match s.toList with
  | [] => pure ()
  | c :: cs => char c *> string (String.ofList cs)

partial def many {α : Type} (p : Parser α) : Parser (List α) :=
  (do let x ← p; let xs ← many p; return (x :: xs)) <|> pure []

def many1 {α : Type} (p : Parser α) : Parser (List α) := do
  let x ← p; let xs ← many p; return (x :: xs)

partial def takeWhile (pred : Char → Bool) : Parser String :=
  (do let c ← satisfy pred; let cs ← takeWhile pred; return (String.ofList (c :: cs.toList)))
  <|> pure ""

def takeWhile1 (pred : Char → Bool) : Parser String := do
  let c ← satisfy pred; let cs ← takeWhile pred; return (String.ofList (c :: cs.toList))

partial def sepBy {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  (do let x ← p; let xs ← many (sep *> p); return (x :: xs)) <|> pure []

def sepBy1 {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  let x ← p; let xs ← many (sep *> p); return (x :: xs)

def optional {α : Type} (p : Parser α) : Parser (Option α) :=
  (do let x ← p; return (some x)) <|> pure none

def notFollowedBy (p : Parser α) : Parser Unit := fun i =>
  match p i with
  | .success _ _ => .failure [{ span := Span.ofString i.pos i.text, message := "unexpected match" }]
  | .failure _ => .success () i

def newline : Parser Unit :=
  (char '\n' *> pure ()) <|> (char '\r' *> (char '\n' *> pure () <|> pure ()))

partial def skipWS : Parser Unit :=
  (char ' ' *> skipWS) <|> (char '\t' *> skipWS) <|> pure ()

partial def skipWSFull : Parser Unit :=
  (char ' ' *> skipWSFull) <|> (char '\t' *> skipWSFull)
  <|> (newline *> skipWSFull) <|> pure ()

end Parser
end LeanParser

open LeanParser
open LeanParser.Parser

-- ============================================================
-- Character classification
-- ============================================================

def isIdentStart (c : Char) : Bool := c.isAlpha ∨ c = '_'
def isIdentCont (c : Char) : Bool := c.isAlphanum ∨ c = '_'

-- ============================================================
-- Token type
-- ============================================================

inductive PyToken where
  | kwDef | kwIf | kwElse | kwWhile | kwFor | kwReturn
  | kwPass | kwBreak | kwContinue
  | kwAnd | kwOr | kwNot | kwIn
  | kwTrue | kwFalse | kwNone
  | name   : String → PyToken
  | intLit : String → PyToken
  | floatLit : String → PyToken
  | strLit : String → PyToken
  | op : String → PyToken
  | delim : String → PyToken
  | newline | indent | dedent | eof
  | comment : String → PyToken
deriving Repr, BEq, Inhabited

def PyToken.toString : PyToken → String
  | kwDef => "def"
  | kwIf => "if"
  | kwElse => "else"
  | kwWhile => "while"
  | kwFor => "for"
  | kwReturn => "return"
  | kwPass => "pass"
  | kwBreak => "break"
  | kwContinue => "continue"
  | kwAnd => "and"
  | kwOr => "or"
  | kwNot => "not"
  | kwIn => "in"
  | kwTrue => "True"
  | kwFalse => "False"
  | kwNone => "None"
  | name s => s
  | intLit s => s
  | floatLit s => s
  | strLit s => s
  | op s => s
  | delim s => s
  | newline => "\\n"
  | indent => "INDENT"
  | dedent => "DEDENT"
  | eof => "EOF"
  | comment s => s!"# {s}"

instance : ToString PyToken where toString := PyToken.toString

-- ============================================================
-- Keyword map
-- ============================================================

def keywordMap : List (String × PyToken) := [
  ("def", .kwDef), ("if", .kwIf), ("else", .kwElse),
  ("while", .kwWhile), ("for", .kwFor), ("return", .kwReturn),
  ("pass", .kwPass), ("break", .kwBreak), ("continue", .kwContinue),
  ("and", .kwAnd), ("or", .kwOr), ("not", .kwNot), ("in", .kwIn),
  ("True", .kwTrue), ("False", .kwFalse), ("None", .kwNone)
]

def lookupKeyword (s : String) : PyToken :=
  match keywordMap.lookup s with
  | some t => t
  | none => .name s

-- ============================================================
-- Scanner (Lexer)
-- ============================================================

def scanIdent : Parser PyToken := do
  let first ← satisfy isIdentStart
  let rest ← takeWhile isIdentCont
  return lookupKeyword (String.ofList (first :: rest.toList))

def scanInt : Parser PyToken := do
  let ds ← takeWhile1 (fun c => c.isDigit)
  return .intLit ds

def scanFloat : Parser PyToken := do
  let ip ← takeWhile (fun c => c.isDigit)
  let _ ← char '.'
  let fp ← takeWhile1 (fun c => c.isDigit)
  return .floatLit (ip ++ "." ++ fp)

def scanNumber : Parser PyToken := scanFloat <|> scanInt

def scanSQString : Parser String := do
  let _ ← char '\''
  let cs ← takeWhile (fun c => c ≠ '\'' ∧ c ≠ '\n')
  let _ ← char '\''
  return "'" ++ cs ++ "'"

def scanDQString : Parser String := do
  let _ ← char '"'
  let cs ← takeWhile (fun c => c ≠ '"' ∧ c ≠ '\n')
  let _ ← char '"'
  return "\"" ++ cs ++ "\""

def scanShortString : Parser String := scanSQString <|> scanDQString

def scanStr : Parser PyToken := do
  let ss ← many1 scanShortString
  return .strLit (String.join ss)

def scanOp : Parser PyToken := do
  let rec tryOps : List (String × PyToken) → Parser PyToken
    | [] => fail "unknown operator"
    | (s, t) :: rest => (string s *> pure t) <|> tryOps rest
  tryOps [
    ("**", .op "**"), ("//", .op "//"), ("<<", .op "<<"), (">>", .op ">>"),
    ("==", .op "=="), ("<=", .op "<="), (">=", .op ">="), ("!=", .op "!="),
    ("+=", .op "+="), ("-=", .op "-="), ("*=", .op "*="), ("/=", .op "/="),
    (":=", .op ":="), ("->", .op "->"),
    ("+", .op "+"), ("-", .op "-"), ("*", .op "*"), ("/", .op "/"),
    ("%", .op "%"), ("=", .op "="), ("<", .op "<"), (">", .op ">")
  ]

def scanDelim : Parser PyToken := do
  let c ← satisfy (fun x => "()[]{},:;.".contains x)
  return .delim (toString c)

def scanComment : Parser PyToken := do
  let _ ← char '#'
  let cs ← takeWhile (fun c => c ≠ '\n')
  return .comment cs

partial def scanToken : Parser PyToken := do
  let c ← peek
  match c with
  | none => return .eof
  | some ch =>
    if ch = '\n' || ch = '\r' then newline *> pure .newline
    else if ch = ' ' || ch = '\t' then skipWS *> scanToken
    else if ch = '#' then scanComment
    else if ch = '\'' || ch = '"' then scanStr
    else if ch.isDigit then scanNumber
    else if ch = '.' then
      (scanFloat <|> (char '.' *> pure (.delim ".")))
    else if isIdentStart ch then scanIdent
    else if "()[]{},:;".contains ch then scanDelim
    else scanOp

-- Simple tokenize: flat token stream (no INDENT/DEDENT for testing)
partial def tokenizeAll (acc : List (Located PyToken)) : Parser (List (Located PyToken)) := do
  let p ← getPos
  let tok ← scanToken
  let lt := Located.at tok (Span.ofString p "")
  match tok with
  | .eof => return List.reverse (lt :: acc)
  | .newline => tokenizeAll (lt :: acc)
  | .comment _ => tokenizeAll acc
  | _ => tokenizeAll (lt :: acc)

def tokenize (source : String) : Except (List Diag) (List (Located PyToken)) :=
  Parser.run (tokenizeAll []) source

-- ============================================================
-- AST Types (no mutual recursion with Block to avoid universe issues)
-- ============================================================

structure Ident where
  name : String
deriving Repr, BEq, Inhabited

inductive Expr where
  | int    : String → Expr
  | float  : String → Expr
  | str    : String → Expr
  | name   : Ident → Expr
  | trueLit | falseLit | noneLit
  | unary  : String → Expr → Expr
  | binop  : String → Expr → Expr → Expr
  | compare : Expr → List (String × Expr) → Expr
  | call   : Expr → List Expr → Expr
  | attr   : Expr → Ident → Expr
  | listLit : List Expr → Expr
  | ifExpr : Expr → Expr → Expr → Expr
deriving Repr, BEq, Inhabited

inductive Stmt where
  | expr        : Expr → Stmt
  | assign      : List Expr → Expr → Stmt
  | returnStmt  : Option Expr → Stmt
  | passStmt | breakStmt | continueStmt
  | ifStmt      : Expr → Stmt → Option Stmt → Stmt
  | whileStmt   : Expr → Stmt → Stmt
  | forStmt     : Expr → Expr → Stmt → Stmt
  | funcDef     : Ident → List Ident → Stmt → Stmt
deriving Repr, BEq, Inhabited

-- ============================================================
-- Parser
-- ============================================================

partial def skipJunk : Parser Unit := do
  let c ← peek
  match c with
  | none => pure ()
  | some ch =>
    if ch = ' ' || ch = '\t' then (skipWS *> skipJunk)
    else if ch = '\n' || ch = '\r' then (newline *> skipJunk)
    else if ch = '#' then (scanComment *> skipJunk)
    else pure ()

def parseName : Parser (Located Ident) := located do
  skipJunk
  let first ← satisfy isIdentStart
  let rest ← takeWhile isIdentCont
  return { name := String.ofList (first :: rest.toList) }

-- ============================================================
-- Expression parser
-- ============================================================

partial def parseAtom : Parser Expr := do
  skipJunk
  let c ← peek
  match c with
  | none => fail "expected expression"
  | some ch =>
    if ch.isDigit then
      let s ← takeWhile1 (fun c' => c'.isDigit ∨ c' = '.')
      if s.contains '.' then return Expr.float s else return Expr.int s
    else if ch = '\'' || ch = '"' then
      let s ← scanShortString
      return Expr.str s
    else if ch = '(' then
      let _ ← char '('; skipJunk
      let first ← parseExpr; skipJunk
      (do let _ ← char ')'; return first)
      <|> (do let _ ← char ','; skipJunk
              let rest ← sepBy parseExpr (char ',' *> skipJunk)
              skipJunk; let _ ← char ')'
              return Expr.call first rest)
    else if ch = '[' then
      let _ ← char '['; skipJunk
      let items ← sepBy parseExpr (char ',' *> skipJunk)
      skipJunk; let _ ← char ']'
      return Expr.listLit items
    else if isIdentStart ch then
      let nm ← parseName
      match nm.value.name with
      | "True" => return Expr.trueLit
      | "False" => return Expr.falseLit
      | "None" => return Expr.noneLit
      | _ => return Expr.name nm.value
    else fail s!"unexpected '{ch}'"

partial def parseTrailers (base : Expr) : Parser Expr := do
  skipJunk
  let c ← peek
  match c with
  | some '(' =>
    let _ ← char '('; skipJunk
    let args ← sepBy parseExpr (char ',' *> skipJunk)
    skipJunk; let _ ← char ')'
    parseTrailers (Expr.call base args)
  | some '.' =>
    let _ ← char '.'; skipJunk
    let nm ← parseName
    parseTrailers (Expr.attr base nm.value)
  | _ => return base

def parsePrimary : Parser Expr := do
  let atom ← parseAtom
  parseTrailers atom

partial def parseUnary : Parser Expr := do
  skipJunk
  (do let _ ← char '-'; let e ← parseUnary; return Expr.unary "-" e)
  <|> (do let _ ← char '+'; let e ← parseUnary; return Expr.unary "+" e)
  <|> (do let _ ← string "not"; skipJunk; let e ← parseUnary; return Expr.unary "not" e)
  <|> parsePrimary

partial def parseMul : Parser Expr := do
  let left ← parseUnary; skipJunk
  (do let _ ← char '*'; skipJunk; let r ← parseMul; return Expr.binop "*" left r)
  <|> (do let _ ← char '/'; skipJunk; let r ← parseMul; return Expr.binop "/" left r)
  <|> (do let _ ← char '%'; skipJunk; let r ← parseMul; return Expr.binop "%" left r)
  <|> return left

partial def parseAdd : Parser Expr := do
  let left ← parseMul; skipJunk
  (do let _ ← char '+'; skipJunk; let r ← parseAdd; return Expr.binop "+" left r)
  <|> (do let _ ← char '-'; skipJunk; let r ← parseAdd; return Expr.binop "-" left r)
  <|> return left

partial def parseCmp : Parser Expr := do
  let left ← parseAdd; skipJunk
  (do let op ← (string "<=" *> pure "<=") <|> (string ">=" *> pure ">=")
            <|> (string "==" *> pure "==") <|> (string "!=" *> pure "!=")
            <|> (char '<' *> pure "<") <|> (char '>' *> pure ">")
            <|> (string "in" *> notFollowedBy (satisfy isIdentCont) *> pure "in")
      skipJunk; let r ← parseAdd
      if op == "in" then return Expr.binop "in" left r
      else return Expr.compare left [(op, r)])
  <|> return left

partial def parseAnd : Parser Expr := do
  let left ← parseCmp; skipJunk
  (do let _ ← string "and"; skipJunk; let r ← parseAnd; return Expr.binop "and" left r)
  <|> return left

partial def parseOr : Parser Expr := do
  let left ← parseAnd; skipJunk
  (do let _ ← string "or"; skipJunk; let r ← parseOr; return Expr.binop "or" left r)
  <|> return left

partial def parseIfExpr : Parser Expr := do
  let body ← parseOr; skipJunk
  (do let _ ← string "if"; skipJunk
      let cond ← parseOr; skipJunk
      let _ ← string "else"; skipJunk
      let els ← parseIfExpr
      return Expr.ifExpr body cond els)
  <|> return body

def parseExpr : Parser Expr := parseIfExpr

def parseExprList : Parser (List Expr) :=
  sepBy parseExpr (char ',' *> skipJunk)

-- ============================================================
-- Statement parser
-- ============================================================

def parseSimpleStmt : Parser Stmt := do
  skipJunk
  (do let _ ← string "pass"; notFollowedBy (satisfy isIdentCont); return Stmt.passStmt)
  <|> (do let _ ← string "break"; notFollowedBy (satisfy isIdentCont); return Stmt.breakStmt)
  <|> (do let _ ← string "continue"; notFollowedBy (satisfy isIdentCont); return Stmt.continueStmt)
  <|> (do let _ ← string "return"; notFollowedBy (satisfy isIdentCont); skipJunk
          let c ← peek
          match c with
          | some '\n' | some ';' | none => return Stmt.returnStmt none
          | _ => do let e ← parseExpr; return Stmt.returnStmt (some e))
  <|> (do let targets ← sepBy1 parseExpr (char ',' *> skipJunk)
          skipJunk
          let c ← peek
          match c with
          | some '=' =>
            let _ ← char '='; notFollowedBy (char '='); skipJunk
            let val ← parseExpr
            return Stmt.assign targets val
          | _ => match targets with
            | [e] => return Stmt.expr e
            | es => return Stmt.expr (Expr.call (Expr.name { name := "tuple" }) es))

/-- Parse a statement suite (indented block after colon+newline). -/
partial def parseSuite : Parser (List Stmt) := do
  let _ ← char ':'
  skipJunk
  let c ← peek
  match c with
  | some '\n' =>
    let _ ← newline
    skipJunk
    many (parseStmt <* skipJunk)
  | _ =>
    -- Simple stmt on same line
    let s ← parseSimpleStmt
    return [s]

partial def parseIfStmt : Parser Stmt := do
  let _ ← string "if"; skipJunk
  let test ← parseExpr
  let body ← parseSuite
  skipJunk
  let elsePart ← optional (do
    let _ ← string "else"
    (do let _ ← char ':'; skipJunk
        let c ← peek
        match c with
        | some '\n' =>
          let _ ← newline; skipJunk
          many (parseStmt <* skipJunk)
        | _ => do let s ← parseSimpleStmt; return [s])
    <|> (do let s ← parseStmt; return [s]))
  match elsePart with
  | none => return Stmt.ifStmt test (Stmt.expr body.head!.expr) none
  | some stmts => return Stmt.ifStmt test (Stmt.expr body.head!.expr) (stmts.head?)

partial def parseWhileStmt : Parser Stmt := do
  let _ ← string "while"; skipJunk
  let test ← parseExpr
  let body ← parseSuite
  return Stmt.whileStmt test (body.headD Stmt.passStmt)

partial def parseForStmt : Parser Stmt := do
  let _ ← string "for"; skipJunk
  let target ← parseExpr; skipJunk
  let _ ← string "in"; skipJunk
  let iter ← parseExpr
  let body ← parseSuite
  return Stmt.forStmt target iter (body.headD Stmt.passStmt)

partial def parseFuncDef : Parser Stmt := do
  let _ ← string "def"; skipJunk
  let name ← parseName; skipJunk
  let _ ← char '('; skipJunk
  let params ← sepBy parseName (char ',' *> skipJunk)
  skipJunk; let _ ← char ')'
  let body ← parseSuite
  return Stmt.funcDef name.value (params.map (·.value)) (body.headD Stmt.passStmt)

partial def parseStmt : Parser Stmt := do
  skipJunk
  let c ← peek
  match c with
  | none => fail "expected statement"
  | some ch =>
    if ch = 'i' then parseIfStmt
    else if ch = 'w' then parseWhileStmt
    else if ch = 'f' then parseForStmt
    else if ch = 'd' then parseFuncDef
    else parseSimpleStmt

partial def parseFile : Parser (List Stmt) := do
  skipJunk
  let stmts ← many parseStmt
  skipJunk
  return stmts

def parsePython3 (source : String) : Except (List Diag) (List Stmt) :=
  Parser.run parseFile source

-- ============================================================
-- Demo / Test
-- ============================================================

def main : IO Unit := do
  IO.println "=== Python3 Subset Parser ==="
  IO.println ""

  -- Test 1: Tokenizer
  let src1 := "def hello(name):\n    return name\n"
  IO.println s!"--- Tokenizer ---"
  IO.println s!"Input:\n{src1}"
  match tokenize src1 with
  | .error ds =>
    for d in ds do IO.println s!"Error @{d.span}: {d.message}"
  | .ok toks =>
    IO.println s!"{toks.length} tokens:"
    for t in toks do
      IO.println s!"  @{t.span.start}: {t.value}"

  -- Test 2: Expression parser
  IO.println ""
  IO.println "--- Expression Parser ---"
  let src2 := "a + b * c"
  IO.println s!"Input: {src2}"
  match Parser.run parseExpr src2 with
  | .error ds =>
    for d in ds do IO.println s!"Error @{d.span}: {d.message}"
  | .ok e =>
    IO.println s!"Parsed OK: {e}"

  -- Test 3: Return statement
  IO.println ""
  IO.println "--- Statement Parser ---"
  let src3 := "def fib(n):\n    return n\n"
  IO.println s!"Input:\n{src3}"
  match parsePython3 src3 with
  | .error ds =>
    for d in ds do IO.println s!"Error @{d.span}: {d.message}"
  | .ok stmts =>
    IO.println s!"Parsed {stmts.length} statement(s)"
    for s in stmts do
      IO.println s!"  {s}"

  -- Test 4: If statement
  IO.println ""
  IO.println "--- If Statement ---"
  let src4 := "if x > 0:\n    return x\n"
  IO.println s!"Input:\n{src4}"
  match parsePython3 src4 with
  | .error ds =>
    for d in ds do IO.println s!"Error @{d.span}: {d.message}"
  | .ok stmts =>
    IO.println s!"Parsed {stmts.length} statement(s)"
    for s in stmts do
      IO.println s!"  {s}"

  IO.println ""
  IO.println "Done."
