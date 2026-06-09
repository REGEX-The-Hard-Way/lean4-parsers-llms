/-
XML Parser — Parses XML token stream into an element tree.
Grammar: grammars-v4/xml/XMLParser.g4
-/
import LeanParser
import Lexer

open LeanParser
open PM
open XmlLexer

namespace XmlParser

-- ============================================================
-- AST
-- ============================================================

/-- An XML attribute. -/
structure Attribute where
  name  : String
  value : String
deriving Repr, BEq

/-- An XML node: element or text. -/
inductive XmlNode where
  | element : String → List Attribute → List XmlNode → XmlNode
  | text    : String → XmlNode
  | comment : String → XmlNode
  | cdata   : String → XmlNode
deriving Repr, BEq

/-- An XML document. -/
structure XmlDoc where
  root : Option XmlNode
deriving Repr, BEq

partial def XmlNode.toString : XmlNode → String
  | .element name attrs children =>
    let attrsStr := String.intercalate " " (attrs.map fun a => s!"{a.name}=\"{a.value}\"")
    let openTag := if attrsStr.isEmpty then s!"<{name}>" else s!"<{name} {attrsStr}>"
    let childrenStr := String.intercalate "" (children.map XmlNode.toString)
    s!"{openTag}{childrenStr}</{name}>"
  | .text s => s
  | .comment s => s!"<!--{s}-->"
  | .cdata s => s!"<![CDATA[{s}]]>"

instance : ToString XmlNode where toString := XmlNode.toString

-- ============================================================
-- Parser
-- ============================================================

instance : Nonempty (PM α) := ⟨fun _ => .err "nonempty"⟩

def matchKind (expected : String) : PM String := do
  let kind ← peek
  if kind == expected then let text ← peekText; next; return text
  else fail s!"expected {expected}, got {kind}"

def matchKindText (expected : String) : PM String := do
  let kind ← peek
  if kind == expected then let text ← peekText; next; return text
  else fail s!"expected {expected}, got {kind}"

/-- Skip whitespace tokens (SEA_WS). -/
partial def skipWS : PM Unit := do
  let kind ← peek
  match kind with
  | "SEA_WS" => do let _ ← next; skipWS
  | _ => pure ()

/-- Parse an attribute: Name = STRING -/
def parseAttribute : PM Attribute := do
  let name ← matchKindText "NAME"
  let _ ← matchKind "="
  let value ← matchKindText "STRING"
  return { name := name, value := value }

/-- Parse zero or more attributes. -/
partial def parseAttributes : PM (List Attribute) := do
  let kind ← peek
  match kind with
  | "NAME" => do
    let attr ← parseAttribute
    let rest ← parseAttributes
    return (attr :: rest)
  | _ => return []

mutual

/-- Parse an element: Name attrs> content </Name> or Name attrs/>
    Caller MUST have consumed the leading OPEN. -/
partial def parseElement : PM XmlNode := do
  let name ← matchKindText "NAME"
  let attrs ← parseAttributes
  let kind ← peek
  match kind with
  | "SELFCLOSE" =>
    let _ ← matchKind "SELFCLOSE"
    return XmlNode.element name attrs []
  | "CLOSE" =>
    let _ ← matchKind "CLOSE"
    let children ← parseContent
    -- Expect closing tag: </Name>
    let _ ← matchKind "OPEN"
    let _ ← matchKind "/"
    let closeName ← matchKindText "NAME"
    let _ ← matchKind "CLOSE"
    return XmlNode.element name attrs children
  | _ => fail s!"expected > or /> after attrs, got {kind}"

/-- Parse content: (chardata | element | reference | CDATA | PI | COMMENT)* -/
partial def parseContent : PM (List XmlNode) := do
  let mut nodes : List XmlNode := []
  let mut done := false
  while !done do
    let kind ← peek
    match kind with
    | "TEXT" =>
      let text ← matchKindText "TEXT"
      nodes := nodes ++ [XmlNode.text text]
    | "SEA_WS" =>
      let text ← matchKindText "SEA_WS"
      nodes := nodes ++ [XmlNode.text text]
    | "COMMENT" =>
      let text ← matchKindText "COMMENT"
      nodes := nodes ++ [XmlNode.comment text]
    | "CDATA" =>
      let text ← matchKindText "CDATA"
      nodes := nodes ++ [XmlNode.cdata text]
    | "ENTITYREF" =>
      let text ← matchKindText "ENTITYREF"
      -- Resolve common entities
      let resolved :=
        match text with
        | "&amp;" => "&"
        | "&lt;" => "<"
        | "&gt;" => ">"
        | "&apos;" => "'"
        | "&quot;" => "\""
        | _ => text
      nodes := nodes ++ [XmlNode.text resolved]
    | "CHARREF" =>
      let _ ← matchKind "CHARREF"
      -- Simplify: treat as text
      nodes := nodes ++ [XmlNode.text "(charref)"]
    | "PI" =>
      let _ ← matchKind "PI"
      -- Skip processing instructions in content
      pure ()
    | "OPEN" =>
      -- Use peek2 to check if this is </ (closing) or <Name (new element)
      let k2 ← peek2
      if k2 == "/" then
        -- Closing tag: </Name> — end of content, leave OPEN unconsumed
        done := true
      else
        let _ ← matchKind "OPEN"  -- consume OPEN
        let elem ← parseElement
        nodes := nodes ++ [elem]
    | _ => done := true
  return nodes

end

/-- Parse an XML document: prolog? misc* element misc* EOF -/
def parseDocument : PM XmlDoc := do
  -- Skip optional prolog <?xml ... ?>
  skipWS
  let kind ← peek
  if kind == "XMLDECL" then
    let _ ← matchKind "XMLDECL"
    -- Skip everything until SPECIAL_CLOSE
    let mut done := false
    while !done do
      let k ← peek
      match k with
      | "SPECIALCLOSE" => let _ ← matchKind "SPECIALCLOSE"; done := true
      | _ => let _ ← next; pure ()
    skipWS
  -- Skip misc (comments, PIs, whitespace)
  let mut miscDone := false
  while !miscDone do
    let k ← peek
    match k with
    | "COMMENT" => let _ ← matchKind "COMMENT"; skipWS
    | "PI"      => let _ ← matchKind "PI"; skipWS
    | "SEA_WS"  => let _ ← matchKind "SEA_WS"; skipWS
    | "TEXT"    =>
      -- Skip whitespace-only text between top-level elements
      let t ← peekText
      if t.all (fun c => c == ' ' ∨ c == '\t' ∨ c == '\n' ∨ c == '\r') then
        let _ ← matchKind "TEXT"; skipWS
      else miscDone := true
    | _         => miscDone := true
  -- Parse root element
  let k ← peek
  match k with
  | "OPEN" =>
    let _ ← matchKind "OPEN"  -- consume the OPEN
    let root ← parseElement
    -- Trailing misc: skip whitespace text
    let mut trailDone := false
    while !trailDone do
      let k ← peek
      match k with
      | "SEA_WS" => let _ ← matchKind "SEA_WS"; pure ()
      | "TEXT"   =>
        let t ← peekText
        if t.all (fun c => c == ' ' ∨ c == '\t' ∨ c == '\n' ∨ c == '\r') then
          let _ ← matchKind "TEXT"; pure ()
        else trailDone := true
      | "COMMENT" => let _ ← matchKind "COMMENT"; pure ()
      | _ => trailDone := true
    let _ ← matchKind "EOF"
    return { root := some root }
  | "EOF" =>
    let _ ← matchKind "EOF"
    return { root := none }
  | _ =>
    fail s!"expected element or EOF, got {k}"

def parse (input : String) : Except String XmlDoc :=
  let pairs := XmlLexer.tokenize input
  let tokens := pairs.map Prod.fst
  let kinds := pairs.map Prod.snd
  let ts := TokenStream.ofLists tokens kinds
  match parseDocument ts with
  | .ok val _ => .ok val
  | .err msg => .error msg

end XmlParser
