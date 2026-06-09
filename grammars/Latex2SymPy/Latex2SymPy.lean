/-
LaTeX Math -> SymPy Translator Grammar v2
==========================================
Lean4 grammar for parsing LaTeX math-mode expressions
and translating them into SymPy (Python symbolic math) code.

Features:
  • Fractions, powers, subscripts, roots, Greek, functions
  • Implicit multiplication: 2x, a b, m c^{2}
  • \left...\right, \sum, \int, \prod, \lim with limits
  • File processing mode: lean --run Latex2SymPy.lean file.tex

Usage: lean --run Latex2SymPy.lean [file.tex]
-/

namespace Latex2SymPy

inductive Expr where
  | num    : String → Expr
  | var    : String → Expr
  | binop  : String → Expr → Expr → Expr
  | unary  : String → Expr → Expr
  | frac   : Expr → Expr → Expr
  | sup    : Expr → Expr → Expr
  | sub    : Expr → Expr → Expr
  | sqrt   : Expr → Expr
  | nroot  : Expr → Expr → Expr
  | func   : String → Expr → Expr
  | bigop  : String → Expr → Expr → Expr → Expr
  | parens : Expr → Expr
  | matrix : List (List Expr) → Expr
  | cases  : List (Expr × Expr) → Expr
  | sympy  : String → Expr
deriving Repr, BEq, Inhabited

structure Input where
  text : String
  pos  : Nat

def Input.ofString (s : String) : Input := { text := s, pos := 0 }

def Input.peek (i : Input) : Option Char :=
  if i.pos < i.text.length then
    some (i.text.toList.getD i.pos ' ')
  else none

def Input.advance (i : Input) : Input := { i with pos := i.pos + 1 }

inductive R (α : Type) where
  | ok : α → Input → R α
  | err : String → R α

def P (α : Type) : Type := Input → R α

instance : Monad P where
  pure a := fun i => .ok a i
  bind p f := fun i => match p i with | .ok a r => f a r | .err m => .err m

instance : Alternative P where
  failure := fun _ => .err "fail"
  orElse p q := fun i => match p i with | .ok a r => .ok a r | .err _ => q () i

def P.run (p : P α) (s : String) : Except String α :=
  match p (Input.ofString s) with
  | .ok a _ => .ok a
  | .err m => .error m

def satisfy (pred : Char → Bool) : P Char := fun i =>
  match i.peek with
  | none => .err "EOF"
  | some c => if pred c then .ok c i.advance else .err s!"unexpected '{c}'"

def ch (c : Char) : P Char := satisfy (fun x => x = c)

partial def many {α : Type} (p : P α) : P (List α) :=
  (do let x ← p; let xs ← many p; return (x :: xs)) <|> pure []

partial def takeWhile (pred : Char → Bool) : P String :=
  (do let c ← satisfy pred; let cs ← takeWhile pred; return (String.ofList (c :: cs.toList))) <|> pure ""

def takeWhile1 (pred : Char → Bool) : P String := do
  let c ← satisfy pred; let cs ← takeWhile pred; return (String.ofList (c :: cs.toList))

partial def skipWS : P Unit := (ch ' ' <|> ch '\t') *> skipWS <|> pure ()
def P.fail (msg : String) : P α := fun _ => .err msg

def isAlpha (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isAlphaNum (c : Char) : Bool := isAlpha c ∨ isDigit c

def peekChar : P Char := fun i => match i.peek with | some c => .ok c i | none => .ok '?' i
def scanCmd : P String := do
  let _ ← ch '\\'; let first ← satisfy isAlpha
  let rest ← takeWhile (fun c => isAlpha c ∨ c = '*')
  return String.ofList (first :: rest.toList)

def tryPeekCmd : P String := fun i =>
  match i.peek with
  | some '\\' => match scanCmd i with
    | .ok s _ => .ok s i
    | .err _ => .err "not"
  | _ => .err "not"

def greekMap : List (String × String) := [
  ("alpha","alpha"),("beta","beta"),("gamma","gamma"),("delta","delta"),
  ("epsilon","epsilon"),("zeta","zeta"),("eta","eta"),("theta","theta"),
  ("iota","iota"),("kappa","kappa"),("lambda","lambda"),("mu","mu"),
  ("nu","nu"),("xi","xi"),("omicron","omicron"),("pi","pi"),
  ("rho","rho"),("sigma","sigma"),("tau","tau"),("upsilon","upsilon"),
  ("phi","phi"),("chi","chi"),("psi","psi"),("omega","omega"),
  ("Gamma","Gamma"),("Delta","Delta"),("Theta","Theta"),
  ("Lambda","Lambda"),("Xi","Xi"),("Pi","Pi"),("Sigma","Sigma"),
  ("Upsilon","Upsilon"),("Phi","Phi"),("Psi","Psi"),("Omega","Omega")]

def funcMap : List (String × String) := [
  ("sin","sp.sin"),("cos","sp.cos"),("tan","sp.tan"),("csc","sp.csc"),
  ("sec","sp.sec"),("cot","sp.cot"),("arcsin","sp.asin"),("arccos","sp.acos"),
  ("arctan","sp.atan"),("sinh","sp.sinh"),("cosh","sp.cosh"),("tanh","sp.tanh"),
  ("log","sp.log"),("ln","sp.log"),("exp","sp.exp"),("abs","sp.Abs"),
  ("max","sp.Max"),("min","sp.Min")]

def specialMap : List (String × String) := [
  ("infty","sp.oo"),("partial","sp.Derivative"),("hbar","sp.hbar"),
  ("emptyset","sp.EmptySet"),("nabla","sp.Symbol('nabla')"),
  ("cdot","MUL"),("times","MUL"),("pm","PLUSMINUS"),("mp","MINUSPLUS"),
  ("leq","LEQ"),("ge","GEQ"),("le","LEQ"),("geq","GEQ"),("neq","NEQ"),
  ("ne","NEQ"),("approx","APPROX"),("equiv","sp.Symbol('equiv')"),
  ("propto","sp.Symbol('propto')"),("dots","sp.Symbol('...')"),
  ("cdots","sp.Symbol('...')"),("oplus","sp.Symbol('oplus')"),
  ("otimes","sp.Symbol('otimes')"),("odot","sp.Symbol('odot')"),
  ("Im","sp.im"),("Re","sp.re")]

-- ============================================================
-- Mutually recursive parser
-- ============================================================

mutual

  partial def parseExpr : P Expr := do
    skipWS
    let left ← parseAdd
    skipWS
    let c ← peekChar
    match c with
    | '=' =>
      let _ ← ch '='
      skipWS
      let r ← parseAdd
      return Expr.binop "==" left r
    | '<' =>
      let _ ← ch '<'
      let c' ← peekChar
      if c' == '=' then
        let _ ← ch '='
        skipWS
        let r ← parseAdd
        return Expr.binop "<=" left r
      else
        skipWS
        let r ← parseAdd
        return Expr.binop "<" left r
    | '>' =>
      let _ ← ch '>'
      let c' ← peekChar
      if c' == '=' then
        let _ ← ch '='
        skipWS
        let r ← parseAdd
        return Expr.binop ">=" left r
      else
        skipWS
        let r ← parseAdd
        return Expr.binop ">" left r
    | '\\' =>
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | "leq" => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop "<=" left r
      | "le"  => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop "<=" left r
      | "geq" => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop ">=" left r
      | "ge"  => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop ">=" left r
      | "neq" => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop "!=" left r
      | "ne"  => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop "!=" left r
      | "approx" => let _ ← scanCmd; skipWS; let r ← parseAdd; return Expr.binop "sp.Eq" left r
      | _ => return left
    | _ =>
      if c == '(' || c == '[' || c == '{' || c == '|' || c == '\\' || isAlpha c || isDigit c then
        let right ← parseAdd
        return Expr.binop "*" left right
      else return left

  partial def parseAdd : P Expr := do
    skipWS
    let left ← parseMul
    skipWS
    let c ← peekChar
    match c with
    | '+' =>
      let _ ← ch '+'
      skipWS
      let r ← parseAdd
      return Expr.binop "+" left r
    | '-' =>
      let _ ← ch '-'
      skipWS
      let r ← parseAdd
      return Expr.binop "-" left r
    | _ => return left

  partial def parseMul : P Expr := do
    skipWS
    let left ← parseUnary
    skipWS
    let c ← peekChar
    match c with
    | '*' =>
      let _ ← ch '*'
      skipWS
      let r ← parseUnary
      parseMulRest (Expr.binop "*" left r)
    | '\\' =>
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some "cdot" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "times" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "ast" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "star" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | none => return left
      | some cmd =>
        if cmd == "leq" || cmd == "le" || cmd == "geq" || cmd == "ge" ||
           cmd == "neq" || cmd == "ne" || cmd == "approx" ||
           cmd == "end" || cmd == "begin" || cmd == "right" || cmd == "left" then
          return left
        else
        let r ← parseUnary
        parseMulRest (Expr.binop "*" left r)
    | _ =>
      if isAlpha c || isDigit c || c == '(' || c == '[' || c == '{' || c == '|' || c == '\\' then
        let r ← parseUnary
        parseMulRest (Expr.binop "*" left r)
      else return left

  partial def parseMulRest (left : Expr) : P Expr := do
    skipWS
    let c ← peekChar
    match c with
    | '*' =>
      let _ ← ch '*'
      skipWS
      let r ← parseUnary
      parseMulRest (Expr.binop "*" left r)
    | '\\' =>
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some "cdot" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "times" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "ast" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "star" => let _ ← scanCmd; skipWS; let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
      | some "end" => return left
      | some "begin" => return left
      | some "left" => return left
      | some "right" => return left
      | some "leq" | some "le" | some "geq" | some "ge" | some "neq" | some "ne" | some "approx" => return left
      | none => return left
      | some _ => let r ← parseUnary; parseMulRest (Expr.binop "*" left r)
    | _ =>
      if isAlpha c || isDigit c || c == '(' || c == '[' || c == '{' || c == '|' || c == '\\' then
        let r ← parseUnary
        parseMulRest (Expr.binop "*" left r)
      else return left

  partial def parseUnary : P Expr := do
    skipWS
    let c ← peekChar
    match c with
    | '-' =>
      let _ ← ch '-'
      skipWS
      let e ← parseUnary
      return Expr.unary "-" e
    | '+' =>
      let _ ← ch '+'
      skipWS
      parseUnary
    | _ => parsePower

  partial def parsePower : P Expr := do
    skipWS
    let base ← parseAtom
    skipWS
    parseScripts base
  where
    parseScripts (node : Expr) : P Expr := do
      skipWS
      let c ← peekChar
      match c with
      | '^' =>
        let _ ← ch '^'
        skipWS
        let exp ← parseArg
        parseScripts (Expr.sup node exp)
      | '_' =>
        let _ ← ch '_'
        skipWS
        let sub ← parseArg
        parseScripts (Expr.sub node sub)
      | _ => return node

  partial def parseArg : P Expr := do
    skipWS
    let c ← peekChar
    match c with
    | '{' =>
      let _ ← ch '{'
      let e ← parseExpr
      let _ ← ch '}'
      return e
    | '\\' => parseCmd
    | _ =>
      if isDigit c then
        let intPart ← takeWhile1 isDigit
        let c'' ← peekChar
        if c'' == '.' then
          let _ ← ch '.'
          let fracPart ← takeWhile1 isDigit
          return Expr.num (intPart ++ "." ++ fracPart)
        else return Expr.num intPart
      else if isAlpha c then
        let _ ← ch c
        return Expr.var (String.ofList [c])
      else return Expr.var (String.ofList [c])
  partial def parseAtom : P Expr := do
    skipWS
    let c ← peekChar
    if isDigit c then
      let intPart ← takeWhile1 isDigit
      let c' ← peekChar
      if c' == '.' then
        let _ ← ch '.'
        let fracPart ← takeWhile1 isDigit
        return Expr.num (intPart ++ "." ++ fracPart)
      else return Expr.num intPart
    match c with
    | '(' =>
      let _ ← ch '('
      let e ← parseExpr
      let _ ← ch ')'
      return Expr.parens e
    | '[' =>
      let _ ← ch '['
      let e ← parseExpr
      let _ ← ch ']'
      return Expr.parens e
    | '{' =>
      let _ ← ch '{'
      let e ← parseExpr
      let _ ← ch '}'
      return e
    | '|' =>
      let _ ← ch '|'
      let e ← parseExpr
      let _ ← ch '|'
      return Expr.func "sp.Abs" e
    | '\\' =>
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some _ => parseCmd
      | none => parseCmd
    | _ =>
      if isAlpha c then
        let name ← takeWhile1 isAlphaNum
        return Expr.var name
      else if c == '\'' then
        let _ ← ch '\''
        return Expr.var "prime"
      else P.fail s!"unexpected '{c}'"

  partial def parseCmd : P Expr := do
    skipWS
    let c ← peekChar
    if c ≠ '\\' then return Expr.var ""
    -- Handle spacing commands: \, \; \: \! \  (backslash-space)
    let _ ← ch '\\'
    let c2 ← peekChar
    if c2 == ',' || c2 == ';' || c2 == ':' || c2 == '!' || c2 == ' ' then do
      let _ ← ch c2
      skipWS
      parseAtom
    else
    -- Restore position for scanCmd (it expects \\ to still be there)
    -- Since we consumed \\, we'll use a variant: read the command name directly
    let first ← satisfy isAlpha
    let rest ← takeWhile (fun x => isAlpha x ∨ x = '*')
    let name := String.ofList (first :: rest.toList)
    skipWS
    match name with
    | "frac" => do let num ← parseCmdArg; let den ← parseCmdArg; return Expr.frac num den
    | "dfrac" => do let num ← parseCmdArg; let den ← parseCmdArg; return Expr.frac num den
    | "tfrac" => do let num ← parseCmdArg; let den ← parseCmdArg; return Expr.frac num den
    | "cfrac" => do let num ← parseCmdArg; let den ← parseCmdArg; return Expr.frac num den
    | "binom" => do let n ← parseCmdArg; let k ← parseCmdArg; return Expr.func "sp.binomial" (Expr.parens (Expr.binop "," n k))
    | "mathbb" => parseStyled "mathbb"
    | "mathcal" => parseStyled "mathcal"
    | "mathfrak" => parseStyled "mathfrak"
    | "mathit" => parseStyled "mathit"
    | "mathbf" => parseStyled "mathbf"
    | "mathsf" => parseStyled "mathsf"
    | "mathtt" => parseStyled "mathtt"
    | "textrm" => parseStyled "textrm"
    | "textbf" => parseStyled "textbf"
    | "textit" => parseStyled "textit"
    | "textsf" => parseStyled "textsf"
    | "texttt" => parseStyled "texttt"
    | "mathrm" => parseStyled "mathrm"
    | "operatorname" => parseCmdArg
    | "sqrt" =>
      let c' ← peekChar
      if c' == '[' then
        let _ ← ch '['
        let nContent ← takeWhile (fun x => x ≠ ']')
        let _ ← ch ']'
        let rad ← parseCmdArg
        match P.run parseExpr nContent with
        | .ok nExpr => return Expr.nroot nExpr rad
        | .error _ => return Expr.nroot (Expr.var nContent) rad
      else do let rad ← parseCmdArg; return Expr.sqrt rad
    | "left" => parseLeftRight
    | "begin" => parseBeginEnv
    | "end" => return Expr.var ""
    | "right" => return Expr.var ""
    | "right." => return Expr.var ""
    | "left." => return Expr.var ""
    | "int" => parseBigOp "sp.Integral" "x"
    | "intop" => parseBigOp "sp.Integral" "x"
    | "sum" => parseBigOp "sp.Sum" "n"
    | "prod" => parseBigOp "sp.Product" "n"
    | "lim" => parseBigOp "sp.Limit" "x"
    | "text" => parseCmdArg
    | _ =>
      match funcMap.lookup name with
      | some spName => parseFunc spName
      | none =>
        match greekMap.lookup name with
        | some gName =>
          if gName == "pi" then return Expr.sympy "sp.pi"
          else return Expr.sympy s!"sp.Symbol('{gName}')"
        | none =>
          match specialMap.lookup name with
          | some spVal => return (specValToExpr spVal)
          | none => return Expr.sympy s!"sp.Symbol('\\{name}')"
  where
    parseLeftRight : P Expr := do
      skipWS
      let c1 ← peekChar
      let _ ←
        if c1 == '(' || c1 == ')' || c1 == '[' || c1 == ']' || c1 == '{' || c1 == '}' || c1 == '|' || c1 == '.' then
          ch c1 *> pure ()
        else if c1 == '\\' then scanCmd *> pure ()
        else pure ()
      let inner ← parseExpr
      skipWS
      let c2 ← peekChar
      let _ ←
        if c2 == '\\' then do
          let cmd2 ← scanCmd
          if cmd2 == "right" then do
            skipWS
            let c3 ← peekChar
            if c3 == '(' || c3 == ')' || c3 == '[' || c3 == ']' || c3 == '{' || c3 == '}' || c3 == '|' || c3 == '.' then
              ch c3 *> pure ()
            else if c3 == '\\' then scanCmd *> pure ()
            else pure ()
          else pure ()
        else pure ()
      return Expr.parens inner

    parseBigOp (fnName _varName : String) : P Expr := do
      let lower ← parseBigLimit
      let upper ← parseBigLimitUpper
      skipWS
      let body ← parseExpr
      return Expr.bigop fnName (lower.getD (Expr.num "0")) (upper.getD (Expr.num "1")) body

    parseBigLimit : P (Option Expr) := do
      skipWS
      let c ← peekChar
      match c with
      | '_' =>
        let _ ← ch '_'
        skipWS
        let c' ← peekChar
        if c' == '{' then do
          let _ ← ch '{'
          let e ← parseExpr
          let _ ← ch '}'
          return some e
        else do let e ← parseAtom; return some e
      | _ => return none

    parseBigLimitUpper : P (Option Expr) := do
      skipWS
      let c ← peekChar
      match c with
      | '^' =>
        let _ ← ch '^'
        skipWS
        let c' ← peekChar
        if c' == '{' then do
          let _ ← ch '{'
          let e ← parseExpr
          let _ ← ch '}'
          return some e
        else do let e ← parseAtom; return some e
      | _ => return none

    parseStyled (style : String) : P Expr := do
      let arg ← parseCmdArg
      -- Extract the argument as a plain string (skip SymPy wrapping)
      let argStr := match arg with
        | Expr.var s => s
        | Expr.sympy s => s
        | _ => "x"
      -- Map common math styles to Unicode
      let styled := match style with
        | "mathbb" =>
          match argStr with
          | "R" => "ℝ" | "N" => "ℕ" | "Z" => "ℤ"
          | "Q" => "ℚ" | "C" => "ℂ" | "P" => "ℙ"
          | "A" => "𝔸" | "B" => "ℬ" | "F" => "𝔽"
          | "H" => "ℍ" | _ => argStr
        | "mathcal" =>
          match argStr with
          | "A" => "𝒜" | "B" => "ℬ" | "C" => "𝒞"
          | "D" => "𝒟" | "E" => "𝒠" | "F" => "ℱ"
          | "G" => "𝒢" | "H" => "ℋ" | "I" => "ℐ"
          | "J" => "𝒥" | "K" => "𝒦" | "L" => "ℒ"
          | "M" => "ℳ" | "N" => "𝒩" | "O" => "𝒪"
          | "P" => "𝒫" | "Q" => "𝒬" | "R" => "ℛ"
          | "S" => "𝒮" | "T" => "𝒯" | "U" => "𝒰"
          | "V" => "𝒱" | "W" => "𝒲" | "X" => "𝒳"
          | "Y" => "𝒴" | "Z" => "𝒵"
          | _ => argStr
        | _ => argStr
      return Expr.sympy s!"sp.Symbol('{styled}')"

    parseFunc (spName : String) : P Expr := do
      let c1 ← peekChar
      if c1 == '^' then
        let _ ← ch '^'; skipWS; let exp ← parseArg
        let arg ← parseCmdArg
        return Expr.sup (Expr.func spName arg) exp
      else if c1 == '_' then
        let _ ← ch '_'; skipWS; let sub ← parseArg
        let arg ← parseCmdArg
        return Expr.sub (Expr.func spName arg) sub
      else
        let arg ← parseCmdArg
        return Expr.func spName arg

    specValToExpr (spVal : String) : Expr :=
      if spVal == "sp.oo" then Expr.sympy "sp.oo"
      else if spVal == "MUL" then Expr.sympy "*"
      else if spVal == "LEQ" then Expr.sympy "<="
      else if spVal == "GEQ" then Expr.sympy ">="
      else if spVal == "NEQ" then Expr.sympy "!="
      else if spVal == "APPROX" then Expr.sympy "sp.Eq"
      else if spVal == "PLUSMINUS" then Expr.sympy "pm"
      else if spVal == "MINUSPLUS" then Expr.sympy "mp"
      else Expr.sympy spVal

  partial def parseBeginEnv : P Expr := do
    skipWS
    let c ← peekChar
    if c == '{' then
      let _ ← ch '{'
      let envName ← takeWhile (fun x => x ≠ '}')
      let _ ← ch '}'
      skipWS
      if envName == "pmatrix" || envName == "bmatrix" || envName == "Bmatrix" ||
         envName == "vmatrix" || envName == "Vmatrix" || envName == "matrix" then
        parseMatrixContent envName
      else if envName == "cases" then
        parseCasesContent
      else
        P.fail ("unknown environment: " ++ envName)
    else
      P.fail "expected {name}"

  partial def parseMatrixContent (envName : String) : P Expr := do
    let rows ← parseMatrixRows envName []
    return Expr.matrix rows

  partial def parseMatrixRow (envName : String) (acc : List Expr) : P (List Expr) := do
    skipWS
    let cell ← parseExpr
    let acc' := cell :: acc
    skipWS
    let c ← peekChar
    if c == '&' then
      let _ ← ch '&'
      parseMatrixRow envName acc'
    else if c == '\\' then
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some "end" => return acc'.reverse
      | _ =>
        let _ ← ch '\\'
        let c2 ← peekChar
        if c2 == '\\' then let _ ← ch '\\'
        return acc'.reverse
    else
      return acc'.reverse

  partial def parseMatrixRows (envName : String) (acc : List (List Expr)) : P (List (List Expr)) := do
    skipWS
    let c ← peekChar
    if c == '\\' then
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some "end" =>
        let _ ← scanCmd
        skipWS
        let c2 ← peekChar
        if c2 == '{' then
          let _ ← ch '{'
          let closeName ← takeWhile (fun x => x ≠ '}')
          let _ ← ch '}'
          if closeName == envName then
            return acc.reverse
          else
            P.fail ("expected end{" ++ envName ++ "}, got end{" ++ closeName ++ "}")
        else
          P.fail "expected { after end"
      | _ =>
        let _ ← ch '\\'
        let c2 ← peekChar
        if c2 == '\\' then let _ ← ch '\\'
        let row ← parseMatrixRow envName []
        parseMatrixRows envName (row :: acc)
    else
      let row ← parseMatrixRow envName []
      parseMatrixRows envName (row :: acc)
  partial def parseCasesContent : P Expr := do
    let pairs ← parseCaseRows []
    return Expr.cases pairs

  partial def parseCaseRow (acc : List (Expr × Expr)) : P (List (Expr × Expr)) := do
    skipWS
    let expr ← parseExpr
    skipWS
    let c ← peekChar
    if c == '&' then
      let _ ← ch '&'
      skipWS
      let cond ← parseExpr
      skipWS
      return ((expr, cond) :: acc)
    else
      P.fail "expected & in cases"

  partial def parseCaseRows (acc : List (Expr × Expr)) : P (List (Expr × Expr)) := do
    skipWS
    let c ← peekChar
    if c == '\\' then
      let cmdOpt ← optional tryPeekCmd
      match cmdOpt with
      | some "end" =>
        let _ ← scanCmd
        skipWS
        let c2 ← peekChar
        if c2 == '{' then
          let _ ← ch '{'
          let closeName ← takeWhile (fun x => x ≠ '}')
          let _ ← ch '}'
          if closeName == "cases" then return acc.reverse
          else P.fail ("expected end{cases}, got end{" ++ closeName ++ "}")
        else
          P.fail "expected { after end"
      | _ =>
        let _ ← ch '\\'
        let c2 ← peekChar
        if c2 == '\\' then let _ ← ch '\\'
        let pair ← parseCaseRow acc
        parseCaseRows pair
    else
      let pair ← parseCaseRow acc
      parseCaseRows pair

  partial def parseCmdArg : P Expr := do
    skipWS
    let c ← peekChar
    match c with
    | '{' => do let _ ← ch '{'; let e ← parseExpr; let _ ← ch '}'; return e
    | '\\' => parseCmd
    | _ => parseAtom

end

-- ============================================================
-- SymPy code generator
-- ============================================================

partial def toSymPy (e : Expr) : String :=
  match e with
  | Expr.num s => s
  | Expr.var s =>
    let c0 := s.toList.headD ' '
    if s.length == 1 && isAlpha c0 then s
    else s!"sp.Symbol('{s}')"
  | Expr.binop op l r =>
    let ls := toSymPy l; let rs := toSymPy r
    if op == "==" then s!"sp.Eq({ls}, {rs})"
    else if op == "sp.Eq" then s!"sp.Eq({ls}, {rs})"
    else s!"({ls} {op} {rs})"
  | Expr.unary op e => s!"({op}{toSymPy e})"
  | Expr.frac n d => s!"({toSymPy n} / {toSymPy d})"
  | Expr.sup b e => s!"({toSymPy b}**{toSymPy e})"
  | Expr.sub b i => s!"sp.Symbol('{toSymPy b}_{toSymPy i}')"
  | Expr.sqrt a => s!"sp.sqrt({toSymPy a})"
  | Expr.nroot n a => s!"({toSymPy a}**(1/({toSymPy n})))"
  | Expr.func f a => s!"{f}({toSymPy a})"
  | Expr.bigop op lo hi body =>
    let o := toSymPy lo
    let h := toSymPy hi
    let b := toSymPy body
    s!"{op}({b}, (x, {o}, {h}))"
  | Expr.parens e => s!"({toSymPy e})"
  | Expr.matrix rows =>
    let rowStrs := rows.map fun row =>
      "[" ++ String.intercalate ", " (row.map toSymPy) ++ "]"
    "sp.Matrix([" ++ String.intercalate ", " rowStrs ++ "])"
  | Expr.cases pairs =>
    let pairStrs := pairs.map fun (e, cnd) =>
      "(" ++ toSymPy e ++ ", " ++ toSymPy cnd ++ ")"
    "sp.Piecewise([" ++ String.intercalate ", " pairStrs ++ "])"
  | Expr.sympy s => s

-- ============================================================
-- LaTeX file extractor
-- ============================================================

partial def extractMath (chars : List Char) (inMath : Bool) (acc : List Char) (results : List String) : List String :=
  match chars with
  | '$' :: '$' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | '$' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | '\\' :: '(' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | '\\' :: ')' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | '\\' :: '[' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | '\\' :: ']' :: rest =>
    if inMath then
      let content := String.ofList (acc.reverse)
      extractMath rest false [] (content :: results)
    else
      extractMath rest true [] results
  | c :: rest =>
    if inMath then
      extractMath rest inMath (c :: acc) results
    else
      extractMath rest inMath acc results
  | [] => results.reverse

def processFile (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let mathExprs := extractMath contents.toList false [] []
  IO.println s!"Found {mathExprs.length} math expression(s) in {path}
"
  for expr in mathExprs do
    -- Strip newlines from multiline display math
    let clean := expr.replace "\n" ""
    if clean.length > 0 then
      IO.println s!"--- MATH: {clean}"
      match P.run parseExpr clean with
      | .error msg => IO.println s!"  PARSE ERROR: {msg}"
      | .ok ast => IO.println s!"  SymPy: {toSymPy ast}"
      IO.println ""



partial def pretty (depth : Nat) (e : Expr) : String :=
  let ind := String.join (List.replicate depth "  ")
  match e with
  | Expr.num s => s!"{ind}Num({s})"
  | Expr.var s => s!"{ind}Var({s})"
  | Expr.binop op l r => s!"{ind}BinOp({op})\n{pretty (depth+1) l}\n{pretty (depth+1) r}"
  | Expr.unary op e => s!"{ind}Unary({op})\n{pretty (depth+1) e}"
  | Expr.frac n d => s!"{ind}Frac\n{pretty (depth+1) n}\n{pretty (depth+1) d}"
  | Expr.sup b e => s!"{ind}Sup\n{pretty (depth+1) b}\n{pretty (depth+1) e}"
  | Expr.sub b i => s!"{ind}Sub\n{pretty (depth+1) b}\n{pretty (depth+1) i}"
  | Expr.sqrt a => s!"{ind}Sqrt\n{pretty (depth+1) a}"
  | Expr.nroot n a => s!"{ind}NRoot\n{pretty (depth+1) n}\n{pretty (depth+1) a}"
  | Expr.func f a => s!"{ind}Func({f})\n{pretty (depth+1) a}"
  | Expr.bigop op lo hi body =>
    s!"{ind}BigOp({op})\n{pretty (depth+1) lo}\n{pretty (depth+1) hi}\n{pretty (depth+1) body}"
  | Expr.parens e => s!"{ind}Parens\n{pretty (depth+1) e}"
  | Expr.matrix rows =>
    let rowStrs := rows.map fun row =>
      String.intercalate ", " (row.map fun e => toSymPy e)
    s!"{ind}Matrix[" ++ String.intercalate ", " rowStrs ++ "]"
  | Expr.cases pairs =>
    let pairStrs := pairs.map fun (e, cnd) =>
      s!"{toSymPy e} : {toSymPy cnd}"
    s!"{ind}Case\n" ++ String.intercalate "\n" (pairStrs.map fun s => ind ++ "  " ++ s)
  | Expr.sympy s => s!"{ind}SymPy({s})"
instance : ToString Expr where toString e := pretty 0 e

-- ============================================================
-- Tests and CLI
-- ============================================================

def runTest (label input : String) : IO Unit := do
  let bar := String.join (List.replicate 50 "=")
  IO.println s!"\n{bar}"
  IO.println s!"TEST: {label}"
  IO.println s!"Input:  {input}"
  match P.run parseExpr input with
  | .error msg => IO.println s!"  PARSE ERROR: {msg}"
  | .ok ast =>
    IO.println s!"  AST: {ast}"
    IO.println s!"  SymPy: {toSymPy ast}"
  IO.println bar

def main (args : List String) : IO Unit := do
  IO.println "Latex2SymPy v2: LaTeX Math -> SymPy Translator"
  IO.println ""

  if args.length > 0 then
    processFile (args.headD "")
  else
    runTest "Addition" "a + b"
    runTest "Multiplication" "a * b"
    runTest "Mixed + *" "a + b * c"
    runTest "Parens" "(a + b) * c"
    runTest "Implicit mul" "2x + 3y"
    runTest "Einstein" "E = m c^{2}"
    runTest "Pythagorean" "a^2 + b^2 = c^2"
    runTest "Fraction" "\\frac{a}{b}"
    runTest "Nested frac" "\\frac{a+b}{c+d}"
    runTest "Power" "x^{n+1}"
    runTest "Subscript" "x_{i}^{2}"
    runTest "Square root" "\\sqrt{x}"
    runTest "Nth root" "\\sqrt[3]{x}"
    runTest "Greek" "\\alpha + \\pi"
    runTest "Sine" "\\sin x"
    runTest "Log" "\\log x"
    runTest "Equality" "x = y"
    runTest "Inequality" "a \\leq b"
    runTest "Infinity" "\\infty"
    runTest "Sum" "\\sum_{i=0}^{n} i^{2}"
    runTest "Integral" "\\int_a^b x dx"
    runTest "vu/c formula" "\\frac{v_u}{c} = \\alpha \\left(\\frac{m_e}{2m_p}\\right)^{\\frac{1}{2}}"



  IO.println "
Done!"

end Latex2SymPy
open Latex2SymPy
def main (args : List String) : IO Unit := Latex2SymPy.main args

