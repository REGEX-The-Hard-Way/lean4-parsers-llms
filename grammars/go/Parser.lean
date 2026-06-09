import LeanParser
import Lexer

open LeanParser
open PM
open GoLexer

namespace GoParser

structure SourcePos where
  offset : Nat
  line   : Nat
  column : Nat
deriving BEq, Inhabited

def offsetToLineCol (source : String) (off : Nat) : Nat × Nat :=
  let cs := source.toList
  let rec go (chars : List Char) (l : Nat) (c : Nat) (pos : Nat) (tgt : Nat) : Nat × Nat :=
    match chars with
    | [] => (l, c)
    | h :: rest =>
      if pos >= tgt then (l, c)
      else if h == '\n' then go rest (l+1) 1 (pos+1) tgt
      else go rest l (c+1) (pos+1) tgt
  go cs 1 1 0 off

def pos : PM SourcePos := fun ts =>
  let rec byteOff (ls : List Nat) (i : Nat) (acc : Nat) : Nat :=
    match ls with
    | [] => acc
    | _ :: rest => if i == 0 then acc else byteOff rest (i-1) (acc + ls.headD 0)
  let off := byteOff ts.lengths ts.idx 0
  let (line, col) := offsetToLineCol ts.source off
  .ok { offset := off, line := line, column := col } ts

def matchKind (expected : String) : PM String := do
  let kind ← peek
  if kind == expected then let text ← peekText; next; return text
  else let p ← pos; fail s!"expected {expected}, got {kind} at L{p.line}:C{p.column}"

partial def skipEOS : PM Unit := do
  let kind ← peek
  if kind == "EOS" then let _ ← matchKind "EOS"; skipEOS else pure ()

def advance : PM Unit := fun ts => .ok () ts.next

-- Skip tokens until we find a { at depth 0, then consume it
partial def skipToBrace : PM Unit := do
  let rec go (depth : Nat) : PM Unit := do
    let k ← peek
    if k == "{" then
      if depth == 0 then let _ ← advance; pure ()
      else let _ ← advance; go (depth+1)
    else if k == "}" && depth > 0 then let _ ← advance; go (depth-1)
    else let _ ← advance; go depth
  go 0

partial def fastSkipDepth (target : String) (depth : Nat) : PM Unit := do
  let k ← peek
  if k == target && depth == 0 then pure ()
  else if k == "{" then let _ ← advance; fastSkipDepth target (depth+1)
  else if k == "}" && depth > 0 then let _ ← advance; fastSkipDepth target (depth-1)
  else let _ ← advance; fastSkipDepth target depth

partial def fastSkip (target : String) : PM Unit := fastSkipDepth target 0

-- Skip a type: identifiers, pointers, arrays, slices, maps, chans, funcs, parens
partial def skipType : PM Unit := do
  let k ← peek
  match k with
  | "*" => let _ ← advance; skipType
  | "[" =>
    let _ ← advance
    let k2 ← peek
    if k2 == "]" then let _ ← advance; skipType
    else let _ ← fastSkipDepth "]" 0; let _ ← advance; skipType
  | "MAP" =>
    let _ ← advance; let _ ← matchKind "["
    skipType; let _ ← matchKind "]"; skipType
  | "CHAN" => let _ ← advance; skipType
  | "<-" => let _ ← advance; skipType
  | "FUNC" =>
    let _ ← advance
    let kp ← peek
    if kp == "(" then
      let _ ← matchKind "("
      let _ ← fastSkipDepth ")" 0
      let _ ← matchKind ")"
    skipType
  | "STRUCT" =>
    let _ ← advance
    let ks ← peek
    if ks == "{" then
      let _ ← matchKind "{"
      let _ ← fastSkipDepth "}" 0
      let _ ← matchKind "}"
  | "INTERFACE" =>
    let _ ← advance
    let ki ← peek
    if ki == "{" then
      let _ ← matchKind "{"
      let _ ← fastSkipDepth "}" 0
      let _ ← matchKind "}"
  | "(" =>
    let _ ← matchKind "("
    let _ ← fastSkipDepth ")" 0
    let _ ← matchKind ")"
    skipType
  | "IDENTIFIER" => let _ ← advance; skipType
  | "." => let _ ← advance; skipType
  | _ => pure ()

-- Skip the rest of a declaration (type + value)
partial def skipDeclRest : PM Unit := do
  let k ← peek
  if k == "=" || k == ":=" then
    let _ ← advance; let _ ← fastSkipDepth "EOS" 0; let _ ← skipEOS
  else if k == "IDENTIFIER" || k == "*" || k == "[" || k == "MAP" || k == "CHAN"
       || k == "<-" || k == "FUNC" || k == "STRUCT" || k == "INTERFACE" || k == "(" then
    skipType
    let k2 ← peek
    if k2 == "=" then let _ ← advance; let _ ← fastSkipDepth "EOS" 0; let _ ← skipEOS
    else let _ ← skipEOS
  else
    let _ ← skipEOS

inductive Node where
  | file    : SourcePos → String → List Node → List Node → Node
  | import_ : SourcePos → Option String → String → Node
  | func    : SourcePos → String → List String → Node → Node
  | method  : SourcePos → String → List String → Node → Node
  | var_    : SourcePos → List String → String → Node → Node
  | const_  : SourcePos → String → Node → Node
  | type_   : SourcePos → String → Node
  | body    : SourcePos → SourcePos → List Node → Node
  | ifStmt  : SourcePos → Node → Node → Option Node → Node
  | forStmt : SourcePos → Node → Node → Node
  | return_ : SourcePos → Node
  | exprStmt : SourcePos → Node
  | select  : SourcePos → Node
  | call    : SourcePos → String → List String → Node
  | lit     : SourcePos → String → Node
  | ident   : SourcePos → String → Node

instance : Nonempty (PM α) := ⟨fun _ => .err "nonempty"⟩

mutual
partial def parseStmt : PM Node := do
  let p ← pos; let kind ← peek
  match kind with
  | "RETURN" =>
    let _ ← matchKind "RETURN"
    let rec skipRest (depth : Nat) : PM Unit := do
      let k ← peek
      if k == "EOS" then pure ()
      else if k == "{" then let _ ← advance; skipRest (depth+1)
      else if k == "}" then
        if depth == 0 then pure ()
        else let _ ← advance; skipRest (depth-1)
      else let _ ← advance; skipRest depth
    let _ ← skipRest 0; return (Node.return_ p)
  | "IF" =>
    let _ ← matchKind "IF"
    -- Skip init/condition until {
    skipToBrace
    let b ← parseBody
    let elseB ← (do let _ ← matchKind "ELSE"; let bb ← parseBody; return (some bb)) <|> pure none
    return (Node.ifStmt p (Node.lit p "if") b elseB)
  | "FOR" =>
    let _ ← matchKind "FOR"; let _ ← fastSkip "{"; let b ← parseBody
    return (Node.forStmt p (Node.lit p "for") b)
  | "SELECT" =>
    let _ ← matchKind "SELECT"; let _ ← fastSkip "{"; let _ ← matchKind "{"
    let rec skipSelCases (_ : Unit) : PM Unit := do
      let k ← peek; if k == "}" then let _ ← matchKind "}"; pure ()
      else let _ ← fastSkip ":"; let _ ← matchKind ":"; let _ ← parseBody; skipSelCases ()
    let _ ← skipSelCases (); return (Node.select p)
  | "SWITCH" =>
    let _ ← matchKind "SWITCH"
    -- Optional expression before {
    let ks ← peek
    if ks != "{" then let _ ← fastSkip "{"
    let _ ← matchKind "{"
    let rec skipSwitchCases (_ : Unit) : PM Unit := do
      let k ← peek
      if k == "}" then let _ ← matchKind "}"; pure ()
      else let _ ← fastSkip ":"; let _ ← matchKind ":"; let _ ← parseBody; skipSwitchCases ()
    let _ ← skipSwitchCases (); return (Node.exprStmt p)
  | "{" => let _ ← parseBody; return (Node.body p p [])
  | "DEFER" => let _ ← matchKind "DEFER"; let _ ← fastSkipDepth "EOS" 0; return (Node.exprStmt p)
  | "GO" => let _ ← matchKind "GO"; let _ ← fastSkipDepth "EOS" 0; return (Node.exprStmt p)
  | "IDENTIFIER" =>
    let name ← matchKind "IDENTIFIER"
    let k2 ← peek
    if k2 == ":=" then
      let _ ← matchKind ":="
      -- Skip expression(s) after :=
      let _ ← fastSkipDepth "EOS" 0
      return (Node.ident p name)
    else if k2 == "." then
      let _ ← matchKind "."; let f ← matchKind "IDENTIFIER"
      let k3 ← peek
      if k3 == "(" then let _ ← matchKind "("; let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      return (Node.call p s!"{name}.{f}" [])
    else if k2 == "(" then
      let _ ← matchKind "("; let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      return (Node.call p name [])
    else return (Node.ident p name)
  | _ => let _ ← advance; return (Node.exprStmt p)

partial def parseBody : PM Node := do
  let lb ← pos; let _ ← matchKind "{"
  let mut stmts : List Node := []
  let mut done := false
  while !done do
    let k ← peek
    if k == "}" then let _ ← matchKind "}"; done := true
    else let s ← parseStmt; let _ ← skipEOS; stmts := stmts ++ [s]
  -- Consume extra closing braces from nested literals
  let mut extra := true
  while extra do
    let k ← peek
    if k == "}" then let _ ← matchKind "}"; pure ()
    else extra := false
  let rb ← pos; return (Node.body lb rb stmts)
end

partial def parseTopDecl : PM Node := do
  let p ← pos; let kind ← peek
  match kind with
  | "FUNC" =>
    let _ ← matchKind "FUNC"; let k ← peek
    if k == "(" then
      let _ ← matchKind "("; let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      let name ← matchKind "IDENTIFIER"
      let kg ← peek
      if kg == "[" then let _ ← fastSkipDepth "]" 0; let _ ← matchKind "]"
      let _ ← matchKind "("; let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      skipType
      let kb ← peek
      let body ← if kb == "{" then parseBody else pure (Node.body p p [])
      let _ ← skipEOS
      return (Node.method p name [] body)
    else
      let name ← matchKind "IDENTIFIER"
      let kg ← peek
      if kg == "[" then let _ ← fastSkipDepth "]" 0; let _ ← matchKind "]"
      let _ ← matchKind "("; let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      skipType
      let kb ← peek
      let body ← if kb == "{" then parseBody else pure (Node.body p p [])
      let _ ← skipEOS
      return (Node.func p name [] body)
  | "VAR" =>
    let _ ← matchKind "VAR"
    let k2 ← peek
    if k2 == "(" then
      let _ ← matchKind "("
      let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      let _ ← skipEOS
    else skipDeclRest
    return (Node.var_ p [] "?" (Node.lit p "?"))
  | "CONST" =>
    let _ ← matchKind "CONST"
    let k2 ← peek
    if k2 == "(" then
      let _ ← matchKind "("
      let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      let _ ← skipEOS
    else skipDeclRest
    return (Node.const_ p "?" (Node.lit p "?"))
  | "TYPE" =>
    let _ ← matchKind "TYPE"
    let k2 ← peek
    if k2 == "(" then
      let _ ← matchKind "("
      let _ ← fastSkipDepth ")" 0; let _ ← matchKind ")"
      let _ ← skipEOS
    else
      let _ ← matchKind "IDENTIFIER"
      skipDeclRest
    return (Node.type_ p "?")
  | _ => fail s!"unexpected decl: {kind}"

def parseFile : PM Node := do
  let p0 ← pos
  -- Package clause is optional
  let mut pkg := ""
  let kp ← peek
  if kp == "PACKAGE" then
    let _ ← matchKind "PACKAGE"; pkg ← matchKind "IDENTIFIER"; let _ ← skipEOS
  -- Imports
  let mut imports : List Node := []
  let mut impDone := false
  while !impDone do
    let k ← peek
    if k == "IMPORT" then
      let _ ← matchKind "IMPORT"; let k2 ← peek
      if k2 == "(" then
        let _ ← matchKind "("
        let mut specDone := false
        while !specDone do
          let _ ← skipEOS; let k3 ← peek
          if k3 == ")" then let _ ← matchKind ")"; specDone := true
          else
            -- Handle dot/underscore/alias imports
            let alias ← if k3 == "." || k3 == "IDENTIFIER" then
              let a ← matchKind k3; pure (some a)
            else pure none
            let path ← matchKind "STRING"
            imports := imports ++ [Node.import_ p0 alias path]
            let _ ← skipEOS
        let _ ← skipEOS
      else
        -- Single import with optional alias (. IDENTIFIER)
        let k3 ← peek
        let alias ← if k3 == "." || k3 == "IDENTIFIER" then
          let a ← matchKind k3; pure (some a)
        else pure none
        let path ← matchKind "STRING"; imports := imports ++ [Node.import_ p0 alias path]; let _ ← skipEOS
    else impDone := true
  -- Declarations
  let mut decls : List Node := []
  let mut declDone := false
  while !declDone do
    let k ← peek
    if k == "EOF" then declDone := true
    else let d ← parseTopDecl; decls := decls ++ [d]
  let _ ← matchKind "EOF"; return (Node.file p0 pkg imports decls)

def parse (input : String) : Except String Node :=
  let pairs := GoLexer.tokenizeWithLengths input
  let tokens  := pairs.map (fun (t, _, _) => t)
  let kinds   := pairs.map (fun (_, k, _) => k)
  let lengths := pairs.map (fun (_, _, l) => l)
  match parseFile (TokenStream.ofLists tokens kinds lengths input) with
  | .ok val _ => .ok val
  | .err msg => .error msg

end GoParser
