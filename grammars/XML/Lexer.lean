import LeanParser

open LeanParser

namespace XmlLexer

inductive XmlToken where
  | openTag | closeTag | selfClose | slash | equals
  | xmlDeclOpen | specialClose
  | name      : String → XmlToken
  | stringLit : String → XmlToken
  | text      : String → XmlToken
  | comment   : String → XmlToken
  | cdata     : String → XmlToken
  | entityRef : String → XmlToken
  | charRef   : String → XmlToken
  | pi        : String → XmlToken
  | seaWs     : String → XmlToken
  | eof
deriving Repr, BEq

def XmlToken.toKind : XmlToken → String
  | .openTag => "OPEN" | .closeTag => "CLOSE" | .selfClose => "SELFCLOSE"
  | .slash => "/" | .equals => "="
  | .xmlDeclOpen => "XMLDECL" | .specialClose => "SPECIALCLOSE"
  | .name _ => "NAME" | .stringLit _ => "STRING"
  | .text _ => "TEXT" | .comment _ => "COMMENT" | .cdata _ => "CDATA"
  | .entityRef _ => "ENTITYREF" | .charRef _ => "CHARREF"
  | .pi _ => "PI" | .seaWs _ => "SEA_WS" | .eof => "EOF"

def XmlToken.toText : XmlToken → String
  | .openTag => "<" | .closeTag => ">" | .selfClose => "/>"
  | .slash => "/" | .equals => "="
  | .xmlDeclOpen => "<?xml" | .specialClose => "?>"
  | .name s => s | .stringLit s => s | .text s => s
  | .comment s => s | .cdata s => s
  | .entityRef s => s | .charRef s => s | .pi s => s
  | .seaWs s => s | .eof => ""

def isWs (c : Char) : Bool := c == ' ' ∨ c == '\t' ∨ c == '\r' ∨ c == '\n'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isNameStartChar (c : Char) : Bool :=
  c == ':' ∨ c == '_' ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
def isNameChar (c : Char) : Bool :=
  isNameStartChar c ∨ c == '-' ∨ c == '.' ∨ isDigit c

-- Read a quoted string
def readString (quote : Char) (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | c :: r => if c == quote then (r, acc) else go (c :: acc) r
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read until a specific delimiter
partial def readUntil (delim : List Char) (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | _ =>
      if cs'.length >= delim.length then
        let rec startsWith (haystack needle : List Char) : Bool :=
          match needle, haystack with
          | [], _ => true
          | _, [] => false
          | n :: ns, h :: hs => n == h && startsWith hs ns
        if startsWith cs' delim then (List.drop delim.length cs', acc)
        else match cs' with
        | c :: r => go (c :: acc) r
        | [] => (cs', acc)
      else match cs' with
      | c :: r => go (c :: acc) r
      | [] => (cs', acc)
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

-- Read an XML name
def readName (cs : List Char) : List Char × String :=
  match cs with
  | [] => (cs, "")
  | c :: _ =>
    if isNameStartChar c then
      let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
        match cs' with
        | [] => (cs', acc)
        | d :: r => if isNameChar d then go (d :: acc) r else (cs', acc)
      let (rest, chars) := go [] cs
      (rest, String.ofList chars.reverse)
    else (cs, "")

-- Read text content (until < or &)
def readText (cs : List Char) : List Char × String :=
  let rec go (acc : List Char) (cs' : List Char) : List Char × List Char :=
    match cs' with
    | [] => (cs', acc)
    | '<' :: _ => (cs', acc)
    | '&' :: _ => (cs', acc)
    | c :: r => go (c :: acc) r
  let (rest, chars) := go [] cs
  (rest, String.ofList chars.reverse)

mutual

partial def goDefault (cs : List Char) (acc : List XmlToken) : List XmlToken :=
  match cs with
  | [] => (.eof :: acc).reverse
  | '<' :: '!' :: '-' :: '-' :: rest =>
    let (rest', text) := readUntil ('-' :: '-' :: '>' :: []) rest
    goDefault rest' (.comment ("<!--" ++ text ++ "-->") :: acc)
  | '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: rest =>
    let (rest', text) := readUntil (']' :: ']' :: '>' :: []) rest
    goDefault rest' (.cdata ("<![CDATA[" ++ text ++ "]]>") :: acc)
  | '<' :: '!' :: dtdRest =>
    -- DTD: skip until >
    let rec skipDtd (cs' : List Char) : List Char :=
      match cs' with
      | [] => cs'
      | '>' :: r => r
      | _ :: r => skipDtd r
    let rest' := skipDtd dtdRest
    goDefault rest' acc
  | '<' :: '?' :: 'x' :: 'm' :: 'l' :: rest =>
    goInside rest (.xmlDeclOpen :: acc)
  | '<' :: '?' :: rest =>
    goProcInstr rest acc
  | '<' :: rest =>
    goInside rest (.openTag :: acc)
  | '&' :: '#' :: rest =>
    -- Char ref: &#...; or &#x...;
    let (rest', text) := readUntil (';' :: []) rest
    let refText := "&#" ++ text ++ ";"
    goDefault rest' (.charRef refText :: acc)
  | '&' :: rest =>
    -- Entity ref: &name;
    let (rest', text) := readUntil (';' :: []) rest
    let refText := "&" ++ text ++ ";"
    goDefault rest' (.entityRef refText :: acc)
  | c :: rest =>
    let (rest', text) := readText (c :: rest)
    if text.isEmpty then goDefault rest' acc
    else goDefault rest' (.text text :: acc)

partial def goInside (cs : List Char) (acc : List XmlToken) : List XmlToken :=
  match cs with
  | [] => (.eof :: acc).reverse
  | '/' :: '>' :: rest => goDefault rest (.selfClose :: acc)
  | '?' :: '>' :: rest => goDefault rest (.specialClose :: acc)
  | '>' :: rest => goDefault rest (.closeTag :: acc)
  | '/' :: rest => goInside rest (.slash :: acc)
  | '=' :: rest => goInside rest (.equals :: acc)
  | c :: rest =>
    if isWs c then
      let rec skipWs (cs' : List Char) : List Char :=
        match cs' with
        | d :: r => if isWs d then skipWs r else cs'
        | [] => cs'
      goInside (skipWs rest) acc
    else if c == '"' then
      let (rest', s) := readString '"' rest
      goInside rest' (.stringLit s :: acc)
    else if c == '\'' then
      let (rest', s) := readString '\'' rest
      goInside rest' (.stringLit s :: acc)
    else if isNameStartChar c then
      let (rest', name) := readName (c :: rest)
      goInside rest' (.name name :: acc)
    else goInside rest acc

partial def goProcInstr (cs : List Char) (acc : List XmlToken) : List XmlToken :=
  match cs with
  | [] => (.eof :: acc).reverse
  | '?' :: '>' :: rest => goDefault rest (.specialClose :: acc)
  | _ :: rest =>
    -- Accumulate until ?>
    let rec readPI (cs' : List Char) : List Char × List Char :=
      match cs' with
      | [] => (cs', [])
      | '?' :: '>' :: r => (r, [])
      | c :: r =>
        let (rest', chars) := readPI r
        (rest', c :: chars)
    let (rest', chars) := readPI cs
    let piText := String.ofList chars.reverse
    goDefault rest' (.pi piText :: acc)

end

def lex (s : String) : List XmlToken :=
  goDefault s.toList []

def tokenize (s : String) : List (String × String) :=
  let tokens := lex s
  tokens.map (fun t => (t.toText, t.toKind))

end XmlLexer
