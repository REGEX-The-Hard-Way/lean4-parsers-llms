/-
LaTeX parser for sound1.tex — extracts document structure, compiles to C.
-/

-- ============================================================
-- Core parser type
-- ============================================================

inductive MyResult (α : Type) where
  | ok    : α → List Char → MyResult α
  | error : Nat → String → MyResult α
deriving Repr, Nonempty

def MyParser (α : Type) : Type := List Char → MyResult α

instance : Nonempty (MyParser α) := ⟨fun _ => MyResult.error 0 ""⟩

def MyParser.run (p : MyParser α) (s : String) : Except String α :=
  match p s.toList with
  | .ok val _     => .ok val
  | .error pos msg => .error s!"offset {pos}: {msg}"

instance : Monad MyParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok val rest => f val rest
    | .error n m   => .error n m

instance : Alternative MyParser where
  failure := fun s => .error 0 ""
  orElse p q := fun s =>
    match p s with
    | .ok val rest => .ok val rest
    | .error n _   => q () s

-- ============================================================
-- Basic combinators
-- ============================================================

def ch (c : Char) : MyParser Char := fun s =>
  match s with
  | []      => .error 0 "unexpected EOF"
  | x :: xs => if x = c then .ok c xs else .error 0 s!"expected '{c}'"

partial def many {α : Type} (p : MyParser α) : MyParser (List α) :=
  go []
where
  go (acc : List α) : MyParser (List α) :=
    (do let x ← p; go (x :: acc)) <|> pure acc.reverse

def many1 {α : Type} (p : MyParser α) : MyParser (List α) := do
  let x ← p
  let xs ← many p
  return (x :: xs)

def satisfy (pred : Char → Bool) : MyParser Char := fun s =>
  match s with
  | []      => .error 0 "unexpected EOF"
  | x :: xs => if pred x then .ok x xs else .error 0 "char did not match"

def fail (msg : String) : MyParser α := fun _ => .error 0 msg

def getInput : MyParser (List Char) := fun s => .ok s s

/-- Match a specific string literal. -/
partial def matchStr (s : String) : MyParser Unit :=
  match s.toList with
  | [] => pure ()
  | c :: cs => ch c *> matchStr (String.ofList cs)

/-- Parse a non-special text run. -/
def textRun : MyParser String :=
  many1 (satisfy (fun c =>
    c ≠ '\\' && c ≠ '{' && c ≠ '}' && c ≠ '$' && c ≠ '%' && c ≠ '\n'))
  <&> String.ofList

/-- Skip whitespace on current line. -/
partial def sp : MyParser Unit :=
  (ch ' ' *> sp) <|> (ch '\t' *> sp) <|> pure ()

/-- Parse a balanced braced group { ... }. -/
partial def braced : MyParser String := do
  let _ ← ch '{'
  let chars ← many bracedChar
  let _ ← ch '}'
  return String.ofList chars
where
  bracedChar : MyParser Char :=
    (ch '\\' *> (ch '{' *> pure '{' <|> ch '}' *> pure '}' <|> ch '\\' *> pure '\\' <|> anyChar))
    <|> satisfy (fun c => c ≠ '{' && c ≠ '}' && c ≠ '\\')
  anyChar : MyParser Char := satisfy (fun _ => true)

def bracedArgs : MyParser (List String) :=
  many braced

-- ============================================================
-- LaTeX AST
-- ============================================================

inductive LtxCmd where
  | section    : String → LtxCmd
  | title      : String → LtxCmd
  | author     : String → LtxCmd
  | abstract   : String → LtxCmd
  | label      : String → LtxCmd
  | ref        : String → LtxCmd
  | cite       : String → LtxCmd
  | equation   : String → LtxCmd
  | other      : String → List String → LtxCmd
deriving Repr, BEq

inductive LtxElem where
  | cmd     : LtxCmd → LtxElem
  | txt     : String → LtxElem
  | math    : String → LtxElem
  | display : String → LtxElem
  | envB    : String → LtxElem
  | envE    : String → LtxElem
  | cmnt    : String → LtxElem
deriving Repr, BEq

structure LtxDoc where
  preamble : List LtxElem
  body     : List LtxElem
deriving Repr

-- ============================================================
-- LaTeX parsers
-- ============================================================

/-- Parse a LaTeX command name. -/
def cmdName : MyParser String := do
  let _ ← ch '\\'
  let letters ← many1 (satisfy (fun c =>
    ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ c = '@'))
  return String.ofList letters

/-- Parse any LaTeX command: \name[opt]{arg1}{arg2}... -/
partial def anyCmd : MyParser LtxCmd := do
  let _ ← ch '\\'
  let name ← many1 (satisfy (fun c =>
    ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ c = '@' ∨ c = '*'))
  let nameStr := String.ofList name
  -- Skip optional arguments in square brackets
  let _ ← many optArg
  let args ← bracedArgs
  match nameStr with
  | "section"  => match args with | [s] => return .section s  | _ => return .other nameStr args
  | "title"    => match args with | [s] => return .title s    | _ => return .other nameStr args
  | "author"   => match args with | [s] => return .author s   | _ => return .other nameStr args
  | "label"    => match args with | [s] => return .label s    | _ => return .other nameStr args
  | "ref"      => match args with | [s] => return .ref s      | _ => return .other nameStr args
  | "cite"     => match args with | [s] => return .cite s     | _ => return .other nameStr args
  | _          => return .other nameStr args
where
  optArg : MyParser Unit :=
    (ch '[' *> many (satisfy (fun c => c ≠ ']')) <* ch ']') *> pure ()

/-- Parse inline math $ ... $. -/
def inlineMath : MyParser String := do
  let _ ← ch '$'
  let content ← many (satisfy (fun c => c ≠ '$'))
  let _ ← ch '$'
  return String.ofList content

/-- Parse display math \[ ... \] or $$ ... $$. -/
def displayMath : MyParser String :=
  (matchStr "\\[" *> many (satisfy (fun _ => true)) <* matchStr "\\]") <&> String.ofList
  <|> (matchStr "$$" *> many (satisfy (fun _ => true)) <* matchStr "$$") <&> String.ofList

/-- Parse a LaTeX comment % to end of line. -/
def ltxComment : MyParser String := do
  let _ ← ch '%'
  let content ← many (satisfy (fun c => c ≠ '\n'))
  return String.ofList content

/-- Parse \begin{name}. -/
def envBegin : MyParser String :=
  (matchStr "\\begin{" *> many (satisfy (fun c => c ≠ '}')) <* ch '}') <&> String.ofList

/-- Parse \end{name}. -/
def envEnd : MyParser String :=
  (matchStr "\\end{" *> many (satisfy (fun c => c ≠ '}')) <* ch '}') <&> String.ofList

/-- Parse one LaTeX element. Environments checked before commands to prevent
`\begin`/`\end` from being greedily matched as regular commands. -/
partial def oneElem : MyParser LtxElem :=
  (do let n ← envBegin; return LtxElem.envB n)
  <|> (do let n ← envEnd; return LtxElem.envE n)
  <|> (do let c ← anyCmd; return LtxElem.cmd c)
  <|> (do let m ← displayMath; return LtxElem.display m)
  <|> (do let m ← inlineMath; return LtxElem.math m)
  <|> (do let c ← ltxComment; return LtxElem.cmnt c)
  <|> (do let t ← textRun; return LtxElem.txt t)
  <|> (do let _ ← ch '\n'; return LtxElem.txt "\n")
  <|> (do let _ ← satisfy (fun _ => true); return LtxElem.txt "")

/-- Parse the full LaTeX document as a flat list, then split on \begin{document}. -/
partial def ltxDoc : MyParser LtxDoc := do
  let allElems ← many oneElem
  -- Split into preamble and body based on \begin{document} marker
  let (pre, rest1) := breakOnEnvB allElems "document"
  let (body, _)     := breakOnEnvE rest1 "document"
  return { preamble := pre, body := body }
where
  breakOnEnvB : List LtxElem → String → List LtxElem × List LtxElem
    | [], _ => ([], [])
    | (LtxElem.envB n) :: rest, name =>
      if n = name then ([], rest) else
        let (pre, post) := breakOnEnvB rest name
        (LtxElem.envB n :: pre, post)
    | x :: rest, name =>
      let (pre, post) := breakOnEnvB rest name
      (x :: pre, post)
  breakOnEnvE : List LtxElem → String → List LtxElem × List LtxElem
    | [], _ => ([], [])
    | (LtxElem.envE n) :: rest, name =>
      if n = name then ([], rest) else
        let (pre, post) := breakOnEnvE rest name
        (LtxElem.envE n :: pre, post)
    | x :: rest, name =>
      let (pre, post) := breakOnEnvE rest name
      (x :: pre, post)

-- ============================================================
-- Analysis helpers (must come before main)
-- ============================================================

def elemToString : LtxElem → String
  | LtxElem.txt s     => s
  | LtxElem.math s    => "$" ++ s ++ "$"
  | LtxElem.display s => "\\[" ++ s ++ "\\]"
  | LtxElem.cmd _     => ""
  | LtxElem.envB _    => ""
  | LtxElem.envE _    => ""
  | LtxElem.cmnt _    => ""

def extractSections (body : List LtxElem) : List String :=
  body.filterMap fun e =>
    match e with
    | LtxElem.cmd (LtxCmd.section s) => some s
    | _ => none

def extractLabels (body : List LtxElem) : List String :=
  body.filterMap fun e =>
    match e with
    | LtxElem.cmd (LtxCmd.label s) => some s
    | _ => none

/-- Remove duplicates from a list. -/
partial def dedup (xs : List String) : List String :=
  match xs with
  | [] => []
  | x :: rest => x :: dedup (rest.filter (fun y => y ≠ x))

def extractCitations (body : List LtxElem) : List String :=
  let allCites := body.filterMap fun e =>
    match e with
    | LtxElem.cmd (LtxCmd.cite s) => some s
    | _ => none
  dedup allCites

def extractTitle (doc : LtxDoc) : Option String :=
  let fromPre := doc.preamble.filterMap fun e =>
    match e with | LtxElem.cmd (LtxCmd.title s) => some s | _ => none
  let fromBody := doc.body.filterMap fun e =>
    match e with | LtxElem.cmd (LtxCmd.title s) => some s | _ => none
  (fromPre ++ fromBody).head?

def extractAuthors (doc : LtxDoc) : List String :=
  let fromPre := doc.preamble.filterMap (fun e =>
    match e with | LtxElem.cmd (LtxCmd.author s) => some s | _ => none)
  let fromBody := doc.body.filterMap (fun e =>
    match e with | LtxElem.cmd (LtxCmd.author s) => some s | _ => none)
  fromPre ++ fromBody

def countElem (body : List LtxElem) (f : LtxElem → Bool) : Nat :=
  body.filter f |>.length

def isDisplayEq : LtxElem → Bool
  | LtxElem.display _ => true
  | _ => false

/-- Count equation environments: \begin{equation} ... \end{equation} and \[...\]. -/
partial def countDisplayEqs : List LtxElem → Nat
  | [] => 0
  | LtxElem.envB "equation" :: rest => 1 + countDisplayEqs (skipToEnvE "equation" rest)
  | LtxElem.display _ :: rest => 1 + countDisplayEqs rest
  | _ :: rest => countDisplayEqs rest
where
  skipToEnvE (name : String) : List LtxElem → List LtxElem
    | [] => []
    | LtxElem.envE n :: rest => if n = name then rest else skipToEnvE name rest
    | _ :: rest => skipToEnvE name rest

def isCmd : LtxElem → Bool
  | LtxElem.cmd _ => true
  | _ => false

def isMath : LtxElem → Bool
  | LtxElem.math _ => true
  | _ => false

def isDisplayElem : LtxElem → Bool
  | LtxElem.display _ => true
  | _ => false

def isEnvB : LtxElem → Bool
  | LtxElem.envB _ => true
  | _ => false

-- ============================================================
-- Main
-- ============================================================

def readFile (path : String) : IO String := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
  handle.readToEnd

def main : IO Unit := do
  IO.println "LaTeX Parser — compiled from Lean to C"
  IO.println "======================================="
  IO.println ""

  -- Quick self-test
  let test1 := "\\title{Speed of sound}"
  match MyParser.run (many oneElem) test1 with
  | .ok elems => IO.println s!"Self-test OK: {elems.length} elements"
  | .error err => IO.println s!"Self-test FAIL: {err}"
  IO.println ""

  let content ← readFile "sound1.tex"
  IO.println s!"File size: {content.length} chars"
  IO.println ""

  match MyParser.run ltxDoc content with
  | .error err =>
    IO.println s!"Parse error: {err}"
  | .ok doc =>
    IO.println "=== DOCUMENT ANALYSIS ==="
    -- Title
    match extractTitle doc with
    | some t => IO.println s!"Title: {t}"
    | none   => IO.println "Title: (not found)"
    IO.println ""
    -- Authors
    let authors := extractAuthors doc
    IO.println s!"Authors ({authors.length}):"
    for a in authors do
      IO.println s!"  • {a}"
    IO.println ""
    -- Sections
    let sections := extractSections doc.body
    IO.println s!"Sections ({sections.length}):"
    for s in sections do
      IO.println s!"  § {s}"
    IO.println ""
    -- Citations
    let cites := extractCitations doc.body
    IO.println s!"Unique citations ({cites.length}):"
    for c in cites do
      IO.println s!"  [{c}]"
    IO.println ""
    -- Equations
    let eqns := countDisplayEqs doc.body
    IO.println s!"Display equations: {eqns}"
    IO.println ""
    let total := doc.preamble.length + doc.body.length
    let cmds := countElem (doc.preamble ++ doc.body) isCmd
    let maths := countElem (doc.preamble ++ doc.body) isMath
    let disps := countElem (doc.preamble ++ doc.body) isDisplayElem
    IO.println s!"Elements: {total} total ({doc.preamble.length} preamble, {doc.body.length} body)"
    IO.println s!"  Commands: {cmds}, Math: {maths}, Display: {disps}"

