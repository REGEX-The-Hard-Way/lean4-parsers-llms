/-
Minimal Python3 scanner + parser with location tracking.
Self-contained, based on JavaScriptParser.lean pattern.
-/

namespace LeanParser

structure SourcePos where
  line   : Nat
  column : Nat
  offset : Nat
deriving Repr, BEq, Inhabited, Nonempty

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
deriving Repr, BEq, Inhabited, Nonempty

def Span.ofString (start : SourcePos) (s : String) : Span :=
  { start := start, stop := start.advanceString s }

structure Diag where
  span    : Span
  message : String
deriving Repr, BEq, Nonempty

structure Input where
  text : String
  pos  : SourcePos
deriving Repr, BEq, Nonempty

def Input.ofString (s : String) : Input := { text := s, pos := startPos }
def Input.isEOF (i : Input) : Bool := i.text.isEmpty
def Input.peek (i : Input) : Option Char :=
  if i.text.isEmpty then none else some (i.text.get ⟨0⟩)
def Input.advance (i : Input) : Input :=
  if i.text.isEmpty then i else
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
    | .failure diags    => .failure diags

instance : Alternative Parser where
  failure := fun i => .failure [{
    span := Span.ofString i.pos i.text, message := "parse failure" }]
  orElse p q := fun i =>
    match p i with
    | .success val rest => .success val rest
    | .failure _ =>
      match q () i with
      | .success val rest => .success val rest
      | .failure diags2 => .failure diags2

def fail (msg : String) : Parser α := fun i =>
  .failure [{ span := Span.ofString i.pos i.text, message := msg }]

def getPos : Parser SourcePos := fun i => .success i.pos i
def getText : Parser String := fun i => .success i.text i
def peek : Parser (Option Char) := fun i => .success (i.peek) i

def located (p : Parser α) : Parser (Span × α) := do
  let p0 ← getPos
  let val ← p
  let p1 ← getPos
  return ({ start := p0, stop := p1 }, val)

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

def sepBy1 {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  let x ← p; let xs ← many (sep *> p); return (x :: xs)

partial def sepBy {α : Type} (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  (do let x ← p; let xs ← many (sep *> p); return (x :: xs)) <|> pure []

def optional {α : Type} (p : Parser α) : Parser (Option α) :=
  (do let x ← p; return (some x)) <|> pure none

def notFollowedBy (p : Parser α) : Parser Unit := fun i =>
  match p i with
  | .success _ _ => .failure [{ span := Span.ofString i.pos i.text, message := "unexpected match" }]
  | .failure _ => .success () i

partial def skipWS : Parser Unit :=
  (char ' ' *> skipWS) <|> (char '\t' *> skipWS) <|> pure ()

end Parser
end LeanParser

open LeanParser
open LeanParser.Parser

-- ============================================================
-- Python3 Token type
-- ============================================================

inductive PyToken where
  | kwDef | kwIf | kwElse | kwWhile | kwFor | kwReturn
  | kwPass | kwBreak | kwContinue
  | kwImport | kwFrom | kwClass
  | kwAnd | kwOr | kwNot | kwIn | kwIs
  | kwLambda | kwYield | kwGlobal
  | kwDel | kwRaise | kwTry | kwExcept | kwFinally | kwWith | kwAs
  | kwTrue | kwFalse | kwNone
  | name   : String → PyToken
  | intLit : String → PyToken
  | floatLit : String → PyToken
  | strLit : String → PyToken
  | op : String → PyToken
  | delim : String → PyToken
  | newline | indent | dedent | eof
  | comment : String → PyToken
deriving Repr, BEq, Nonempty

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
  | kwImport => "import"
  | kwFrom => "from"
  | kwClass => "class"
  | kwAnd => "and"
  | kwOr => "or"
  | kwNot => "not"
  | kwIn => "in"
  | kwIs => "is"
  | kwLambda => "lambda"
  | kwYield => "yield"
  | kwGlobal => "global"
  | kwDel => "del"
  | kwRaise => "raise"
  | kwTry => "try"
  | kwExcept => "except"
  | kwFinally => "finally"
  | kwWith => "with"
  | kwAs => "as"
  | kwTrue => "True"
  | kwFalse => "False"
  | kwNone => "None"
  | name s => s!"NAME({s})"
  | intLit s => s!"INT({s})"
  | floatLit s => s!"FLOAT({s})"
  | strLit s => s!"STR({s})"
  | op s => s!"OP({s})"
  | delim s => s!"DELIM({s})"
  | newline => "NEWLINE"
  | indent => "INDENT"
  | dedent => "DEDENT"
  | eof => "EOF"
  | comment s => s!"COMMENT({s})"

instance : ToString PyToken where toString := PyToken.toString

-- ============================================================
-- Character classification
-- ============================================================

def isIdentStart (c : Char) : Bool := c.isAlpha ∨ c = '_'
def isIdentCont (c : Char) : Bool := c.isAlphanum ∨ c = '_'

-- ============================================================
-- Keyword map
-- ============================================================

def keywordMap : List (String × PyToken) := [
  ("def", .kwDef), ("if", .kwIf), ("else", .kwElse),
  ("while", .kwWhile), ("for", .kwFor), ("return", .kwReturn),
  ("pass", .kwPass), ("break", .kwBreak), ("continue", .kwContinue),
  ("import", .kwImport), ("from", .kwFrom), ("class", .kwClass),
  ("and", .kwAnd), ("or", .kwOr), ("not", .kwNot), ("in", .kwIn), ("is", .kwIs),
  ("True", .kwTrue), ("False", .kwFalse), ("None", .kwNone),
  ("lambda", .kwLambda), ("yield", .kwYield), ("global", .kwGlobal),
  ("del", .kwDel), ("raise", .kwRaise), ("try", .kwTry),
  ("except", .kwExcept), ("finally", .kwFinally), ("with", .kwWith), ("as", .kwAs)
]

def lookupKeyword (s : String) : PyToken :=
  match keywordMap.lookup s with
  | some t => t
  | none => .name s

-- ============================================================
-- Scanner
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

-- String character scanner: handles escapes
partial def scanStringChar (quote : Char) : Parser Char :=
  (char '\\' *> (
    (char 'n' *> pure '\n') <|> (char 't' *> pure '\t')
    <|> (char 'r' *> pure '\r') <|> (char '\\' *> pure '\\')
    <|> (char '\'' *> pure '\'') <|> (char '"' *> pure '"')
    <|> (char 'x' *> do
          let d1 ← satisfy (fun c => c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F'))
          let d2 ← satisfy (fun c => c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F'))
          let v := (if d1.isDigit then d1.toNat - '0'.toNat else 0)
          pure (Char.ofNat v))
    <|> satisfy (fun _ => true)))  -- fallback: \X → X
  <|> satisfy (fun c => c ≠ quote ∧ c ≠ '\\' ∧ c ≠ '\n')

partial def scanStringBody (quote : Char) (acc : List Char) : Parser (List Char) :=
  (do let c ← scanStringChar quote; scanStringBody quote (c :: acc))
  <|> pure acc.reverse

def scanSQString : Parser String := do
  let _ ← char '\''
  let cs ← scanStringBody '\'' []
  let _ ← char '\''
  return String.ofList cs

def scanDQString : Parser String := do
  let _ ← char '"'
  let cs ← scanStringBody '"' []
  let _ ← char '"'
  return String.ofList cs

def scanShortString : Parser String := scanSQString <|> scanDQString

def scanStr : Parser PyToken := do
  let ss ← many1 scanShortString
  return .strLit (String.join ss)

def scanOp : Parser PyToken := do
  let rec tryOps : List (String × PyToken) → Parser PyToken
    | [] => fail "unknown operator"
    | (s, t) :: rest => (string s *> pure t) <|> tryOps rest
  tryOps [
    ("**", .op "**"), ("//", .op "//"),
    ("==", .op "=="), ("<=", .op "<="), (">=", .op ">="), ("!=", .op "!="),
    ("+=", .op "+="), ("-=", .op "-="), ("*=", .op "*="), ("/=", .op "/="),
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
    if ch = '\n' || ch = '\r' then
      (char '\n' *> pure .newline) <|> (char '\r' *> (char '\n' *> pure .newline <|> pure .newline))
    else if ch = ' ' || ch = '\t' then skipWS *> scanToken
    else if ch = '#' then scanComment
    else if ch = '\'' || ch = '"' then scanStr
    else if (ch = 'f' || ch = 'F' || ch = 'r' || ch = 'R' || ch = 'b' || ch = 'B') then
      let txt ← getText
      if txt.length > 1 then
        let c2 := txt.get ⟨1⟩
        if c2 = '"' || c2 = '\'' then
          let _ ← char ch; scanStr
        else if txt.length > 2 then
          let c3 := txt.get ⟨2⟩
          if c3 = '"' || c3 = '\'' then
            let _ ← char ch; let _ ← char c2; scanStr
          else
            scanIdent
        else
          scanIdent
      else
        scanIdent
    else if ch.isDigit then scanNumber
    else if ch = '.' then
      (scanFloat <|> (char '.' *> pure (.delim ".")))
    else if isIdentStart ch then scanIdent
    else if "()[]{},:;".contains ch then scanDelim
    else scanOp

-- ============================================================
-- Indentation tracking
-- ============================================================

/-- Count leading spaces on a line, treating tabs as 8 (Python standard). -/
def computeIndent (s : String) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    if i ≥ s.length then acc
    else
      let c := s.get ⟨i⟩
      if c = ' ' then go (i+1) (acc+1)
      else if c = '\t' then go (i+1) (acc+8 - (acc % 8))
      else acc
  go 0 0

/-- Indent tracking state. -/
structure IndentState where
  stack  : List Nat  -- indent levels, head = current
  atBOL  : Bool       -- at beginning of logical line?
  parens : Nat        -- nesting depth of ()[]{}
deriving Repr, BEq

def initIndent : IndentState := { stack := [0], atBOL := true, parens := 0 }

/-- Check if a token opens a bracketed context. -/
def opensParens : PyToken → Bool
  | .delim "(" | .delim "[" | .delim "{" => true
  | _ => false

/-- Check if a token closes a bracketed context. -/
def closesParens : PyToken → Bool
  | .delim ")" | .delim "]" | .delim "}" => true
  | _ => false

/-- Indent-aware tokenizer. Returns tokens with INDENT/DEDENT injected.
    Uses the input text directly to compute indentation levels. -/
partial def tokenizeIndentAux (st : IndentState) (acc : List (Span × PyToken))
    : Parser (List (Span × PyToken)) := do
  if st.atBOL && st.parens == 0 then
    -- At beginning of logical line: compute indent and emit INDENT/DEDENT
    let input ← getText
    let indent := computeIndent input
    match st.stack with
    | current :: _ =>
      if indent = current then
        -- Same indent level, just continue
        tokenizeIndentAux { st with atBOL := false } acc
      else if indent > current then
        -- INDENT: push new level
        let p ← getPos
        let indTok := (Span.ofString p "  ", .indent)
        tokenizeIndentAux { st with stack := indent :: st.stack, atBOL := false } (indTok :: acc)
      else
        -- DEDENT: pop until we match
        let pos ← getPos
        let rec popStack (s : List Nat) (target : Nat) (deds : List (Span × PyToken))
            : List Nat × List (Span × PyToken) :=
          match s with
          | top :: rest =>
            if top = target then (s, deds)
            else if top > target then
              popStack rest target ((Span.ofString pos "", .dedent) :: deds)
            else (s, deds)
          | [] => ([], deds)
        let (newStack, dedents) := popStack st.stack indent []
        let acc' := dedents ++ acc
        tokenizeIndentAux { st with stack := newStack, atBOL := false } acc'
    | [] =>
      tokenizeIndentAux { st with atBOL := false } acc
  else
    -- Not at BOL or inside parens: scan a normal token
    let (sp, tok) ← located scanToken
    match tok with
    | .eof =>
      -- Emit remaining DEDENTs, then EOF
      let rec emitDedents (s : List Nat) (deds : List (Span × PyToken)) : List (Span × PyToken) :=
        match s with
        | [_] => deds
        | _ :: rest =>
          let p := sp  -- use last position
          emitDedents rest ((Span.ofString p.start "", .dedent) :: deds)
        | [] => deds
      let dedents := emitDedents st.stack []
      return List.reverse ((sp, tok) :: dedents ++ acc)
    | .newline =>
      -- Update parens count
      let st' := { st with atBOL := true }
      tokenizeIndentAux st' ((sp, tok) :: acc)
    | .comment _ =>
      tokenizeIndentAux st acc  -- skip comments
    | t =>
      -- Track parens for implicit line continuation
      let st' :=
        if opensParens t then { st with parens := st.parens + 1 }
        else if closesParens t && st.parens > 0 then { st with parens := st.parens - 1 }
        else st
      tokenizeIndentAux st' ((sp, tok) :: acc)

-- Tokenize: produce list of located tokens
partial def tokenizeAux (acc : List (Span × PyToken)) : Parser (List (Span × PyToken)) :=
  tokenizeIndentAux initIndent acc

def tokenize (source : String) : Except (List Diag) (List (Span × PyToken)) :=
  Parser.run (tokenizeAux []) source

-- ============================================================
-- AST
-- ============================================================


inductive Expr where
  | int    : String → Expr
  | float  : String → Expr
  | str    : String → Expr
  | name   : String → Expr
  | trueLit | falseLit | noneLit
  | unary  : String → Expr → Expr
  | binop  : String → Expr → Expr → Expr
  | compare : Expr → List (String × Expr) → Expr
  | ifExpr : Expr → Expr → Expr → Expr
  | call   : Expr → List Expr → Expr
  | attr   : Expr → String → Expr
  | subscript : Expr → Expr → Expr
  | listLit : List Expr → Expr
  | tupleLit : List Expr → Expr
  | dictLit : List (Expr × Expr) → Expr
  | setLit  : List Expr → Expr
  | lambda  : List String → Expr → Expr
  | starred : Expr → Expr
  | yieldExpr : Option Expr → Expr
  | yieldFrom : Expr → Expr
deriving Repr, BEq, Inhabited, Nonempty

structure Decorator where
  name : List String
  args : Option (List Expr)
deriving Repr, BEq, Inhabited

inductive Stmt where
  | expr      : Expr → Stmt
  | assign    : List Expr → Expr → Stmt
  | augAssign : String → Expr → Expr → Stmt
  | annAssign : Expr → Expr → Option Expr → Stmt
  | returnStmt : Option Expr → Stmt
  | passStmt | breakStmt | continueStmt
  | ifStmt    : Expr → List Stmt → List (Expr × List Stmt) → Option (List Stmt) → Stmt
  | whileStmt : Expr → List Stmt → Option (List Stmt) → Stmt
  | forStmt   : Expr → Expr → List Stmt → Option (List Stmt) → Stmt
  | funcDef   : List Decorator → String → List String → List Stmt → Stmt
  | classDef  : List Decorator → String → List Stmt → Stmt
  | tryStmt   : List Stmt → List (Option Expr × Option String × List Stmt) → Option (List Stmt) → Option (List Stmt) → Stmt
  | withStmt  : List (Expr × Option Expr) → List Stmt → Stmt
  | importStmt : List (List String × Option String) → Stmt
  | fromImportStmt : String → List (String × Option String) → Stmt
  | raiseStmt : Option Expr → Option Expr → Stmt
  | assertStmt : Expr → Option Expr → Stmt
  | globalStmt : List String → Stmt
  | delStmt    : List Expr → Stmt
  | yieldStmt  : Expr → Stmt
  | decorated  : Stmt → Stmt
deriving Repr, BEq, Inhabited, Nonempty

instance : ToString Expr where toString e := toString (repr e)
instance : ToString Stmt where toString s := toString (repr s)

-- ============================================================
-- Expression parser
-- ============================================================

partial def skipJunk : Parser Unit := do
  let c ← peek
  match c with
  | none => pure ()
  | some ch =>
    if ch = ' ' || ch = '\t' then (skipWS *> skipJunk)
    else if ch = '\n' || ch = '\r' then
      (char '\n' *> pure () <|> char '\r' *> (char '\n' *> pure () <|> pure ())) *> skipJunk
    else if ch = '#' then (scanComment *> skipJunk)
    else pure ()

-- Expression parsers in a mutual block for forward references

mutual
  partial def parseAtom : Parser Expr := do
    skipJunk
    let c ← peek
    match c with
    | none => fail "expected expression"
    | some ch =>
      if ch.isDigit then
        let s ← takeWhile1 (fun c' => c'.isDigit ∨ c' = '.')
        if s.contains '.' then return Expr.float s else return Expr.int s
      else if ch = 'f' then
        -- f-string: f"..." or f'...'
        let _ ← char 'f'
        let c2 ← peek
        match c2 with
        | some '"' => parseFString '"'
        | some '\'' => parseFString '\''
        | _ =>
          -- not an f-string, put back 'f' and parse as identifier
          let first := 'f'
          let rest ← takeWhile isIdentCont
          let name := String.ofList (first :: rest.toList)
          match name with
          | "True" => return Expr.trueLit
          | "False" => return Expr.falseLit
          | "None" => return Expr.noneLit
          | "lambda" => parseLambda
          | _ => return Expr.name name
      else if ch = '\'' || ch = '"' then
        let s ← scanShortString
        return Expr.str s
      else if ch = '(' then
        let _ ← char '('; skipJunk
        let first ← parseExpr; skipJunk
        let c' ← peek
        match c' with
        | some ')' => let _ ← char ')'; return first
        | some ',' =>
          let _ ← char ','; skipJunk
          let rest ← sepBy (do skipJunk; parseExpr) (char ',' *> skipJunk)
          skipJunk; let _ ← Parser.optional (char ','); let _ ← char ')'
          return Expr.tupleLit (first :: rest)
        | _ => let _ ← char ')'; return first
      else if ch = '[' then
        let _ ← char '['; skipJunk
        let c' ← peek
        match c' with
        | some ']' => let _ ← char ']'; return Expr.listLit []
        | _ =>
          let items ← sepBy (do skipJunk; parseExpr) (char ',' *> skipJunk)
          skipJunk; let _ ← Parser.optional (char ','); let _ ← char ']'
          return Expr.listLit items
      else if ch = '{' then
        let _ ← char '{'; skipJunk
        let c'' ← peek
        match c'' with
        | some '}' => let _ ← char '}'; return Expr.dictLit []
        | _ =>
          let first ← parseExpr; skipJunk
          let c''' ← peek
          match c''' with
          | some ':' =>
            let _ ← char ':'; skipJunk; let val ← parseExpr; skipJunk
            let rest ← many (do
              let _ ← char ','; skipJunk; let k ← parseExpr; skipJunk
              let _ ← char ':'; skipJunk; let v ← parseExpr; skipJunk
              return (k, v))
            skipJunk; let _ ← Parser.optional (char ','); let _ ← char '}'
            return Expr.dictLit ((first, val) :: rest)
          | _ =>
            let rest ← sepBy (do skipJunk; parseExpr) (char ',' *> skipJunk)
            skipJunk; let _ ← Parser.optional (char ','); let _ ← char '}'
            return Expr.setLit (first :: rest)
      else if ch = '*' then
        let _ ← char '*'; skipJunk; let e ← parseExpr; return Expr.starred e
      else if isIdentStart ch then
        let first ← satisfy isIdentStart
        let rest ← takeWhile isIdentCont
        let name := String.ofList (first :: rest.toList)
        match name with
        | "True" => return Expr.trueLit
        | "False" => return Expr.falseLit
        | "None" => return Expr.noneLit
        | "lambda" => parseLambda
        | _ => return Expr.name name
      else fail s!"unexpected '{ch}'"

  partial def parseLambda : Parser Expr := do
    skipJunk
    let params ← sepBy (do let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
                           return String.ofList (f :: r.toList))
                       (char ',' *> skipJunk)
    skipJunk; let _ ← Parser.optional (char ','); let _ ← char ':'; skipJunk
    let body ← parseExpr
    return Expr.lambda params body

  -- Parse f-string: f"hello {name} world"
  partial def parseFString (quote : Char) : Parser Expr := do
    let _ ← char quote
    let rec go (acc : List Expr) : Parser (List Expr) := do
      -- Scan text until { or closing quote
      let txt ← takeWhile (fun c => c ≠ quote ∧ c ≠ '{' ∧ c ≠ '}' ∧ c ≠ '\n')
      let acc' := if txt.isEmpty then acc else Expr.str txt :: acc
      let c ← peek
      match c with
      | some ch =>
        if ch = quote then
          -- End of string
          let _ ← char quote
          let parts := acc'.reverse
          match parts with
          | [] => return acc'.reverse
          | [p] => return acc'.reverse
          | _ => return acc'.reverse
        else if ch = '{' then
          let _ ← char '{'
          let c2 ← peek
          match c2 with
          | some '{' =>
            -- Escaped {{ → literal {
            let _ ← char '{'
            go (Expr.str "{" :: acc')
          | _ =>
            -- Expression interpolation
            let e ← parseExpr; skipJunk
            let _ ← char '}'
            go (e :: acc')
        else if ch = '}' then
          let _ ← char '}'
          let c2 ← peek
          match c2 with
          | some '}' =>
            -- Escaped }} → literal }
            let _ ← char '}'
            go (Expr.str "}" :: acc')
          | _ => fail "unmatched } in f-string"
        else
          go acc'
      | none => fail "unterminated f-string"
    let parts ← go []
    match parts.reverse with
    | [] => return Expr.str ""
    | [e] => return e
    | es => return Expr.tupleLit es

  partial def parseTrailers (base : Expr) : Parser Expr := do
    skipJunk
    let c ← peek
    match c with
    | some '(' =>
      let _ ← char '('; skipJunk
      let c' ← peek
      match c' with
      | some ')' => let _ ← char ')'; parseTrailers (Expr.call base [])
      | _ =>
        let first ← parseExpr; skipJunk
        let rest ← sepBy (do skipJunk; parseExpr) (char ',' *> skipJunk)
        skipJunk; let _ ← Parser.optional (char ','); let _ ← char ')'
        parseTrailers (Expr.call base (first :: rest))
    | some '[' =>
      let _ ← char '['; skipJunk
      let start ← Parser.optional parseExpr; skipJunk
      let c1 ← peek
      match c1 with
      | some ':' =>
        let _ ← char ':'; skipJunk
        let stop ← Parser.optional parseExpr; skipJunk
        let c2 ← peek
        match c2 with
        | some ':' =>
          let _ ← char ':'; skipJunk; let step ← Parser.optional parseExpr; skipJunk; let _ ← char ']'
          parseTrailers (Expr.subscript base (Expr.tupleLit (
            (match start with | some s => [s] | none => []) ++
            (match stop with | some s => [s] | none => []) ++
            (match step with | some s => [s] | none => []))))
        | _ =>
          let _ ← char ']'
          parseTrailers (Expr.subscript base (Expr.tupleLit (
            (match start with | some s => [s] | none => []) ++
            (match stop with | some s => [s] | none => []))))
      | _ =>
        match start with
        | some idx => let _ ← char ']'; parseTrailers (Expr.subscript base idx)
        | none => let _ ← char ']'; parseTrailers (Expr.subscript base (Expr.tupleLit []))
    | some '.' =>
      let _ ← char '.'; skipJunk
      let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
      parseTrailers (Expr.attr base (String.ofList (f :: r.toList)))
    | _ => return base

  partial def parsePrimary : Parser Expr := do
    let atom ← parseAtom
    parseTrailers atom

  partial def parseUnary : Parser Expr := do
    skipJunk
    (do let _ ← char '-'; let e ← parseUnary; return Expr.unary "-" e)
    <|> (do let _ ← char '+'; let e ← parseUnary; return Expr.unary "+" e)
    <|> (do let _ ← char '~'; let e ← parseUnary; return Expr.unary "~" e)
    <|> (do let _ ← string "not"; skipJunk; let e ← parseUnary; return Expr.unary "not" e)
    <|> parsePrimary

  partial def parsePower : Parser Expr := do
    let left ← parseUnary; skipJunk
    (do let _ ← string "**"; skipJunk; let r ← parsePower; return Expr.binop "**" left r)
    <|> return left

  partial def parseMul : Parser Expr := do
    let left ← parsePower; skipJunk
    (do let _ ← char '*'; skipJunk; let r ← parseMul; return Expr.binop "*" left r)
    <|> (do let _ ← char '/'; skipJunk; let r ← parseMul; return Expr.binop "/" left r)
    <|> (do let _ ← char '%'; skipJunk; let r ← parseMul; return Expr.binop "%" left r)
    <|> (do let _ ← string "//"; skipJunk; let r ← parseMul; return Expr.binop "//" left r)
    <|> return left

  partial def parseAdd : Parser Expr := do
    let left ← parseMul; skipJunk
    (do let _ ← char '+'; skipJunk; let r ← parseAdd; return Expr.binop "+" left r)
    <|> (do let _ ← char '-'; skipJunk; let r ← parseAdd; return Expr.binop "-" left r)
    <|> return left

  partial def parseShift : Parser Expr := do
    let left ← parseAdd; skipJunk
    (do let _ ← string "<<"; skipJunk; let r ← parseShift; return Expr.binop "<<" left r)
    <|> (do let _ ← string ">>"; skipJunk; let r ← parseShift; return Expr.binop ">>" left r)
    <|> return left

  partial def parseBitAnd : Parser Expr := do
    let left ← parseShift; skipJunk
    (do let _ ← char '&'; skipJunk; let r ← parseBitAnd; return Expr.binop "&" left r)
    <|> return left

  partial def parseBitXor : Parser Expr := do
    let left ← parseBitAnd; skipJunk
    (do let _ ← char '^'; skipJunk; let r ← parseBitXor; return Expr.binop "^" left r)
    <|> return left

  partial def parseBitOr : Parser Expr := do
    let left ← parseBitXor; skipJunk
    (do let _ ← char '|'; skipJunk; let r ← parseBitOr; return Expr.binop "|" left r)
    <|> return left

  partial def parseCmp : Parser Expr := do
    let left ← parseBitOr; skipJunk
    let rec cmpOp : Parser String :=
      (string "<=" *> pure "<=") <|> (string ">=" *> pure ">=")
      <|> (string "==" *> pure "==") <|> (string "!=" *> pure "!=")
      <|> (char '<' *> pure "<") <|> (char '>' *> pure ">")
      <|> (string "in" *> notFollowedBy (satisfy isIdentCont) *> pure "in")
      <|> (string "is" *> notFollowedBy (satisfy isIdentCont) *>
           ((string "not" *> notFollowedBy (satisfy isIdentCont) *> pure "is not")
            <|> pure "is"))
    -- Collect comparison chain: a < b == c > d
    let rec collect (acc : List (String × Expr)) : Parser (List (String × Expr)) :=
      (do let op ← cmpOp; skipJunk; let r ← parseBitOr; skipJunk
          collect ((op, r) :: acc))
      <|> pure acc.reverse
    let comps ← collect []
    match comps with
    | [] => return left
    | _  => return Expr.compare left comps

  partial def parseAnd : Parser Expr := do
    let left ← parseCmp; skipJunk
    (do let _ ← string "and"; notFollowedBy (satisfy isIdentCont); skipJunk
        let r ← parseAnd; return Expr.binop "and" left r)
    <|> return left

  partial def parseOr : Parser Expr := do
    let left ← parseAnd; skipJunk
    (do let _ ← string "or"; notFollowedBy (satisfy isIdentCont); skipJunk
        let r ← parseOr; return Expr.binop "or" left r)
    <|> return left

  partial def parseIfExpr : Parser Expr := do
    let body ← parseOr; skipJunk
    -- Walrus operator := (binds looser than comparison, tighter than comma)
    (do let _ ← string ":="; skipJunk; let val ← parseIfExpr
        return Expr.binop ":=" body val)
    <|> (do let _ ← string "if"; notFollowedBy (satisfy isIdentCont); skipJunk
            let cond ← parseOr; skipJunk
            let _ ← string "else"; notFollowedBy (satisfy isIdentCont); skipJunk
            let els ← parseIfExpr
            return Expr.ifExpr body cond els)
    <|> return body

  partial def parseExpr : Parser Expr := parseIfExpr



end
-- ============================================================
-- Statement parser
-- ============================================================

partial def parseSimpleStmt : Parser Stmt := do
  skipJunk
  (do let _ ← string "pass"; notFollowedBy (satisfy isIdentCont); return Stmt.passStmt)
  <|> (do let _ ← string "break"; notFollowedBy (satisfy isIdentCont); return Stmt.breakStmt)
  <|> (do let _ ← string "continue"; notFollowedBy (satisfy isIdentCont); return Stmt.continueStmt)
  <|> (do let _ ← string "return"; notFollowedBy (satisfy isIdentCont); skipJunk
          let c ← peek
          match c with
          | some '\n' | some ';' | none => return Stmt.returnStmt none
          | _ => do let e ← parseExpr; return Stmt.returnStmt (some e))
  <|> (do let _ ← string "yield"; notFollowedBy (satisfy isIdentCont); skipJunk
          let c ← peek
          match c with
          | some '\n' | some ';' | none => return Stmt.yieldStmt (Expr.yieldExpr none)
          | _ => do
            let e ← parseExpr
            return Stmt.yieldStmt (Expr.yieldExpr (some e)))
  <|> (do let _ ← string "raise"; notFollowedBy (satisfy isIdentCont); skipJunk
          let e ← Parser.optional parseExpr; skipJunk
          let fromExc ← Parser.optional (do let _ ← string "from"; skipJunk; parseExpr)
          return Stmt.raiseStmt e fromExc)
  <|> (do let _ ← string "assert"; notFollowedBy (satisfy isIdentCont); skipJunk
          let test ← parseExpr
          let msg ← Parser.optional (char ',' *> skipJunk *> parseExpr)
          return Stmt.assertStmt test msg)
  <|> (do let _ ← string "global"; notFollowedBy (satisfy isIdentCont); skipJunk
          let names ← sepBy1 (do let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
                                 return String.ofList (f :: r.toList))
                             (char ',' *> skipJunk)
          return Stmt.globalStmt names)
  <|> (do let _ ← string "del"; notFollowedBy (satisfy isIdentCont); skipJunk
          let targets ← sepBy1 parseExpr (char ',' *> skipJunk)
          return Stmt.delStmt targets)
  <|> (do -- expression, assignment, or augmented assignment
          let first ← parseExpr; skipJunk
          let c ← peek
          match c with
          | some '=' =>
            let _ ← char '='
            let c' ← peek
            if c' == some '=' then fail "use = not =="
            skipJunk
            let val ← parseExpr
            -- Check for multi-assign: x = y = z = value
            let extras ← many (do skipJunk; char '=' *> notFollowedBy (char '=') *> skipJunk *> parseExpr)
            match extras with
            | [] => return Stmt.assign [first] val
            | _  => return Stmt.assign (first :: val :: extras.dropLast) extras.getLast!
          | some ':' =>
            let _ ← char ':'
            let c'' ← peek
            if c'' == some '=' then
              -- walrus operator := (already handled in expr)
              return Stmt.expr first
            skipJunk
            let ty ← parseExpr
            let val ← Parser.optional (char '=' *> skipJunk *> parseExpr)
            return Stmt.annAssign first ty val
          | some '+' =>
            let _ ← char '+'; let _ ← char '='; skipJunk; let val ← parseExpr
            return Stmt.augAssign "+" first val
          | some '-' =>
            let _ ← char '-'; let _ ← char '='; skipJunk; let val ← parseExpr
            return Stmt.augAssign "-" first val
          | some '*' =>
            let _ ← char '*'; let _ ← char '='; skipJunk; let val ← parseExpr
            return Stmt.augAssign "*" first val
          | some '/' =>
            let _ ← char '/'; let _ ← char '='; skipJunk; let val ← parseExpr
            return Stmt.augAssign "/" first val
          | some '%' =>
            let _ ← char '%'; let _ ← char '='; skipJunk; let val ← parseExpr
            return Stmt.augAssign "%" first val
          | _ => return Stmt.expr first)

-- ============================================================
-- Indent-aware block parsing
-- ============================================================

/-- Get the indentation level of the current position in the input.
    Consumes the leading whitespace. -/
def getLineIndent : Parser Nat := do
  let txt ← getText
  return computeIndent txt

/-- Skip to the beginning of the next logical line (past newlines and blank lines). -/
partial def skipToNextLine : Parser Unit := do
  let c ← peek
  match c with
  | none => pure ()
  | some ch =>
    if ch = '\n' || ch = '\r' then
      (char '\n' *> pure ()) <|> (char '\r' *> (char '\n' *> pure () <|> pure ()))
    else if ch = ' ' || ch = '\t' then (skipWS *> skipToNextLine)
    else pure ()  -- already at content

mutual
/-- Parse a block after a colon: either a simple statement on the same line,
    or NEWLINE followed by an indented suite of statements. -/
partial def parseBlock (baseIndent : Nat) : Parser (List Stmt) := do
  let _ ← char ':'
  skipWS  -- skip spaces after colon
  let c ← peek
  match c with
  | some '\n' | some '\r' =>
    -- Multi-line block: consume newline, then parse indented statements
    (char '\n' *> pure ()) <|> (char '\r' *> (char '\n' *> pure () <|> pure ()))
    -- Get indent BEFORE consuming whitespace
    let bodyIndent ← getLineIndent
    if bodyIndent <= baseIndent then
      fail s!"expected indented block (got indent {bodyIndent}, need > {baseIndent})"
    parseIndentedStmts bodyIndent
  | _ =>
    -- Single-line block: parse a simple statement
    let s ← parseSimpleStmt
    return [s]

/-- Parse statements at the given indent level. Stops when indent drops below level. -/
partial def parseIndentedStmts (level : Nat) : Parser (List Stmt) := do
  let indent ← getLineIndent
  if indent < level then
    return []  -- dedent: end of block
  else if indent = level then
    let s ← parseStmt
    skipJunk
    let rest ← parseIndentedStmts level
    return (s :: rest)
  else
    fail s!"unexpected additional indent (got {indent}, expected {level})"

partial def parseStmt : Parser Stmt := do
  -- Compute indent BEFORE consuming whitespace
  let baseIndent ← getLineIndent
  skipJunk
  let c ← peek
  match c with
  | none => fail "expected statement"
  | some ch =>
    if ch = 'i' then
      (do let _ ← string "import"; notFollowedBy (satisfy isIdentCont); skipJunk
          -- Parse dotted name with optional 'as' alias
          let parseDotted : Parser (List String × Option String) := do
            let first ← satisfy isIdentStart
            let rest ← takeWhile isIdentCont
            let base := String.ofList (first :: rest.toList)
            let parts ← many (char '.' *> do
              let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
              return (String.ofList (f :: r.toList)))
            let full := base :: parts
            skipJunk
            let alias ← Parser.optional (do
              let _ ← string "as"; notFollowedBy (satisfy isIdentCont); skipJunk
              let a ← satisfy isIdentStart; let ar ← takeWhile isIdentCont
              return (String.ofList (a :: ar.toList)))
            return (full, alias)
          let modules ← sepBy1 parseDotted (char ',' *> skipJunk)
          return Stmt.importStmt modules)
      <|> (do let _ ← string "if"; notFollowedBy (satisfy isIdentCont); skipJunk
              let test ← parseExpr
              let body ← parseBlock baseIndent
              skipJunk
              let elifs ← many (do
                let indent ← getLineIndent
                if indent != baseIndent then fail "elif not at same indent"
                let _ ← string "elif"; notFollowedBy (satisfy isIdentCont); skipJunk
                let t ← parseExpr
                let b ← parseBlock baseIndent
                skipJunk
                return (t, b))
              let elseBody ← (do
                let indent ← getLineIndent
                if indent == baseIndent then
                  (do let _ ← string "else"; notFollowedBy (satisfy isIdentCont)
                      let b ← parseBlock baseIndent
                      return (some b))
                  <|> pure none
                else pure none)
              return Stmt.ifStmt test body elifs elseBody)
    else if ch = 'w' then
      (do let _ ← string "while"; notFollowedBy (satisfy isIdentCont); skipJunk
          let test ← parseExpr
          let body ← parseBlock baseIndent
          skipJunk
          let elseBody ← Parser.optional (do
            let indent ← getLineIndent
            if indent != baseIndent then fail "else not at same indent"
            let _ ← string "else"
            parseBlock baseIndent)
          return Stmt.whileStmt test body elseBody)
      <|> (do let _ ← string "with"; notFollowedBy (satisfy isIdentCont); skipJunk
              let items ← sepBy1 (do
                let e ← parseExpr; skipJunk
                let asName ← Parser.optional (do
                  let _ ← string "as"; skipJunk; parseExpr)
                return (e, asName))
                (char ',' *> skipJunk)
              let _ ← char ':'; skipJunk
              let body ← parseIndentedStmts (baseIndent + 4)
              return Stmt.withStmt items body)
    else if ch = 'f' then
      (do let _ ← string "for"; notFollowedBy (satisfy isIdentCont); skipJunk
          let target ← parsePrimary; skipJunk
          let _ ← string "in"; skipJunk
          let iter ← parseExpr
          let body ← parseBlock baseIndent
          skipJunk
          let elseBody ← Parser.optional (do
            let indent ← getLineIndent
            if indent != baseIndent then fail "else not at same indent"
            let _ ← string "else"
            parseBlock baseIndent)
          return Stmt.forStmt target iter body elseBody)
      <|> (do let _ ← string "from"; notFollowedBy (satisfy isIdentCont); skipJunk
              return Stmt.importStmt [])
      <|> parseSimpleStmt
    else if ch = 'd' then
      (do let _ ← string "def"; notFollowedBy (satisfy isIdentCont); skipJunk
          let first ← satisfy isIdentStart
          let rest ← takeWhile isIdentCont
          let name := String.ofList (first :: rest.toList); skipJunk
          let _ ← char '('; skipJunk
          let ps ← many (do let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont; skipJunk;
                            let _ ← Parser.optional (char ',' *> skipJunk);
                            return (String.ofList (f :: r.toList)))
          skipJunk; let _ ← char ')'
          let body ← parseBlock baseIndent
          return Stmt.funcDef [] name ps body)
      <|> (do let _ ← string "del"; notFollowedBy (satisfy isIdentCont); skipJunk
              let targets ← sepBy1 parseExpr (char ',' *> skipJunk)
              return Stmt.delStmt targets)
      <|> parseSimpleStmt
    else if ch = 'c' then
      (do let _ ← string "class"; notFollowedBy (satisfy isIdentCont); skipJunk
          let first ← satisfy isIdentStart
          let rest ← takeWhile isIdentCont
          let name := String.ofList (first :: rest.toList); skipJunk
          let _ ← Parser.optional (do let _ ← char '('; skipJunk; let _ ← parseExpr; skipJunk; let _ ← char ')')
          let body ← parseBlock baseIndent
          return Stmt.classDef [] name body)
    else if ch = '@' then
      -- Decorator: @name(args)? NEWLINE
      (do let _ ← char '@'; skipJunk
          let parts ← sepBy1 (do let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
                                 return (String.ofList (f :: r.toList)))
                             (char '.' *> pure ())
          skipJunk
          let args ← Parser.optional (do
            let _ ← char '('; skipJunk
            let as ← sepBy parseExpr (char ',' *> skipJunk)
            skipJunk; let _ ← char ')'; return as)
          -- Consume newline
          skipJunk
          -- Parse the decorated def/class
          let st ← parseStmt
          return Stmt.decorated st)
    else if ch = 't' then
      (do let _ ← string "try"; notFollowedBy (satisfy isIdentCont)
          let _ ← char ':'; skipJunk
          let body ← parseIndentedStmts (baseIndent + 4)
          skipJunk
          let excepts ← many (do
            let _ ← string "except"; notFollowedBy (satisfy isIdentCont); skipJunk
            let exc ← Parser.optional parseExpr; skipJunk
            let asName ← Parser.optional (do
              let _ ← string "as"; skipJunk
              let f ← satisfy isIdentStart; let r ← takeWhile isIdentCont
              return (String.ofList (f :: r.toList)))
            let _ ← char ':'; skipJunk
            let b ← parseIndentedStmts (baseIndent + 4)
            skipJunk
            return (exc, asName, b))
          let elseBody ← Parser.optional (do
            let _ ← string "else"; let _ ← char ':'; skipJunk
            parseIndentedStmts (baseIndent + 4))
          let finallyBody ← Parser.optional (do
            let _ ← string "finally"; let _ ← char ':'; skipJunk
            parseIndentedStmts (baseIndent + 4))
          return Stmt.tryStmt body excepts elseBody finallyBody)
    else if ch = 'e' then do
      -- Check for elif/else without consuming
      let txt ← getText
      if txt.startsWith "elif" && (txt.length < 4 || !isIdentCont (txt.get ⟨4⟩)) then
        fail "elif outside if"
      else if txt.startsWith "else" && (txt.length < 4 || !isIdentCont (txt.get ⟨4⟩)) then
        fail "else outside if"
      else
        parseSimpleStmt
    else parseSimpleStmt

end
partial def parseFile : Parser (List Stmt) := do
  skipJunk
  many parseStmt

partial def parseFileLocated : Parser (List (Span × Stmt)) := do
  skipJunk
  many (located parseStmt)

def parsePython3 (source : String) : Except (List Diag) (List (Span × Stmt)) :=
  Parser.run parseFileLocated source


-- ============================================================
-- File-backed CLI
-- ============================================================

def printTokens (toks : List (Span × PyToken)) : IO Unit :=
  for (sp, tok) in toks do
    IO.println s!"  @{sp.start}: {tok}"

partial def printStmt (depth : Nat) (s : Stmt) : IO Unit := do
  let ind := String.join (List.replicate depth "  ")
  match s with
  | .expr e          => IO.println s!"{ind}Expr: {e}"
  | .assign [n] v    => IO.println s!"{ind}Assign: {n} = {v}"
  | .assign ns v     => IO.println s!"{ind}Assign: {ns} = {v}"
  | .augAssign op t v => IO.println s!"{ind}AugAssign: {t} {op}= {v}"
  | .annAssign n t v => IO.println s!"{ind}AnnAssign: {n} : {t} = {v}"
  | .returnStmt none => IO.println s!"{ind}Return"
  | .returnStmt (some e) => IO.println s!"{ind}Return {e}"
  | .yieldStmt e     => IO.println s!"{ind}Yield {e}"
  | .passStmt        => IO.println s!"{ind}Pass"
  | .breakStmt       => IO.println s!"{ind}Break"
  | .continueStmt    => IO.println s!"{ind}Continue"
  | .decorated s'    => printStmt depth s'
  | .ifStmt test body elifs elseBody => do
      IO.println s!"{ind}If {test}:"
      for s' in body do printStmt (depth+1) s'
      for (cond, b) in elifs do
        IO.println s!"{ind}Elif {cond}:"
        for s' in b do printStmt (depth+1) s'
      match elseBody with
      | none => pure ()
      | some b => IO.println s!"{ind}Else:"; for s' in b do printStmt (depth+1) s'
  | .whileStmt test body elseBody => do
      IO.println s!"{ind}While {test}:"
      for s' in body do printStmt (depth+1) s'
      match elseBody with
      | none => pure ()
      | some b => IO.println s!"{ind}Else:"; for s' in b do printStmt (depth+1) s'
  | .forStmt tgt iter body elseBody => do
      IO.println s!"{ind}For {tgt} in {iter}:"
      for s' in body do printStmt (depth+1) s'
      match elseBody with
      | none => pure ()
      | some b => IO.println s!"{ind}Else:"; for s' in b do printStmt (depth+1) s'
  | .funcDef decs name params body => do
      for d in decs do
        IO.println s!"{ind}@{String.intercalate "." d.name}"
      IO.println s!"{ind}Def {name}({String.intercalate ", " params}):"
      for s' in body do printStmt (depth+1) s'
  | .classDef decs name body => do
      for d in decs do
        IO.println s!"{ind}@{String.intercalate "." d.name}"
      IO.println s!"{ind}Class {name}:"
      for s' in body do printStmt (depth+1) s'
  | .withStmt items body => do
      IO.println s!"{ind}With:"
      for s' in body do printStmt (depth+1) s'
  | .tryStmt body excepts elseBody finallyBody => do
      IO.println s!"{ind}Try:"
      for s' in body do printStmt (depth+1) s'
      for (exc, name, b) in excepts do
        IO.println s!"{ind}Except {exc} as {name}:"
        for s' in b do printStmt (depth+1) s'
      match elseBody with
      | none => pure ()
      | some b => IO.println s!"{ind}Else:"; for s' in b do printStmt (depth+1) s'
      match finallyBody with
      | none => pure ()
      | some b => IO.println s!"{ind}Finally:"; for s' in b do printStmt (depth+1) s'
  | .importStmt modules => IO.println s!"{ind}Import {modules}"
  | .fromImportStmt mod names => IO.println s!"{ind}From {mod} import {names}"
  | .raiseStmt e fromExc => IO.println s!"{ind}Raise {e} from {fromExc}"
  | .assertStmt test msg => IO.println s!"{ind}Assert {test}, {msg}"
  | .globalStmt names => IO.println s!"{ind}Global {names}"
  | .delStmt targets => IO.println s!"{ind}Del {targets}"

def printStmtLocated (depth : Nat) (loc : Span × Stmt) : IO Unit := do
  let (sp, s) := loc
  IO.println s!"  @{sp.start}-{sp.stop}"
  printStmt depth s

def main : IO Unit := do
  match ← IO.getEnv "PYFILE" with
  | none =>
    IO.println "Usage: PYFILE=<file.py> lean --run Py3.lean"
    IO.Process.exit 1
  | some path =>
    let source ← IO.FS.readFile path
    IO.println s!"=== Py3 Parser === {path} ==="
    IO.println ""
    match tokenize source with
    | .error ds =>
      IO.println "TOKENIZER ERRORS:"
      for d in ds do IO.println s!"  @{d.span.start}: {d.message}"
    | .ok toks =>
      IO.println s!"--- Tokens ({toks.length}) ---"
      printTokens toks
    match parsePython3 source with
    | .error ds =>
      IO.println ""
      IO.println "PARSER ERRORS:"
      for d in ds do IO.println s!"  @{d.span.start}: {d.message}"
    | .ok stmts =>
      IO.println ""
      IO.println s!"--- AST ({stmts.length} statement(s)) ---"
      for s in stmts do
        printStmtLocated 0 s
