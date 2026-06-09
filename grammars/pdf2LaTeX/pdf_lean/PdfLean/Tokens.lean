/-
  PdfLean.Tokens
  --------------
  PDF token type and tokenizer.  §7.3.* of ISO 32000-1.

  The tokenizer produces a single token at a time so we can speculatively
  read ahead (e.g. detecting `N G R` indirect references).
-/
import PdfLean.Bytes
import PdfLean.Lex

namespace PdfLean
open PdfLean.Lex

inductive Token where
  | bool      (b : Bool)
  | null
  | int       (n : Int)
  | real      (s : String)            -- store the textual form; parse later
  | litStr    (bs : ByteArray)
  | hexStr    (bs : ByteArray)
  | name      (bs : ByteArray)        -- decoded (no leading /)
  | arrOpen | arrClose
  | dictOpen | dictClose              -- << >>
  | kw        (s : String)            -- e.g. obj, endobj, R, stream, …
  | eof

instance : Inhabited Token := ⟨Token.eof⟩

namespace Token

def repr : Token → String
  | bool true   => "TRUE"
  | bool false  => "FALSE"
  | null        => "NULL"
  | int n       => s!"INT({n})"
  | real s      => s!"REAL({s})"
  | litStr bs   => s!"LITSTR({bs.size}B)"
  | hexStr bs   => s!"HEXSTR({bs.size}B)"
  | name bs     => s!"NAME(/{String.fromUTF8! bs})"
  | arrOpen     => "["
  | arrClose    => "]"
  | dictOpen    => "<<"
  | dictClose   => ">>"
  | kw s        => s!"KW({s})"
  | eof         => "EOF"

instance : ToString Token := ⟨repr⟩
instance : Repr Token := ⟨fun t _ => repr t⟩

end Token

/-- Read a PDF integer or real number starting at the cursor.
    Returns `(token, newReader)`. -/
def readNumber (r : Reader) : Token × Reader := Id.run do
  let start := r.pos
  let mut r := r
  let mut sawDot := false
  -- optional sign
  match r.peek? with
  | some 0x2B | some 0x2D => r := r.advance 1
  | _ => pure ()
  -- digits and dot
  while ! r.atEOF do
    match r.peek? with
    | some 0x2E =>
        if sawDot then break
        sawDot := true
        r := r.advance 1
    | some b =>
        if isDigit b then r := r.advance 1
        else break
    | none => break
  let bs := r.data.extract start r.pos
  let s := String.fromUTF8! bs
  if sawDot then
    return (Token.real s, r)
  else
    -- parse Int
    let n : Int := match s.toInt? with
      | some n => n
      | none   => 0
    return (Token.int n, r)

/-- Read a literal string `( … )`.  Cursor is at `(`. -/
def readLiteralString (r : Reader) : Token × Reader := Id.run do
  let mut r := r.advance 1  -- skip leading '('
  let mut buf : ByteArray := ByteArray.empty
  let mut depth : Nat := 1
  while ! r.atEOF do
    match r.peek? with
    | none => break
    | some b =>
      if b = 0x28 then
        depth := depth + 1
        buf := buf.push b
        r := r.advance 1
      else if b = 0x29 then
        depth := depth - 1
        if depth = 0 then
          r := r.advance 1
          break
        buf := buf.push b
        r := r.advance 1
      else if b = 0x5C then
        -- backslash escape
        r := r.advance 1
        match r.peek? with
        | none => break
        | some c =>
          if c = 0x6E then
            buf := buf.push 0x0A; r := r.advance 1
          else if c = 0x72 then
            buf := buf.push 0x0D; r := r.advance 1
          else if c = 0x74 then
            buf := buf.push 0x09; r := r.advance 1
          else if c = 0x62 then
            buf := buf.push 0x08; r := r.advance 1
          else if c = 0x66 then
            buf := buf.push 0x0C; r := r.advance 1
          else if c = 0x28 then
            buf := buf.push 0x28; r := r.advance 1
          else if c = 0x29 then
            buf := buf.push 0x29; r := r.advance 1
          else if c = 0x5C then
            buf := buf.push 0x5C; r := r.advance 1
          else if c = 0x0A then
            r := r.advance 1                 -- line continuation
          else if c = 0x0D then
            r := r.advance 1
            match r.peek? with
            | some 0x0A => r := r.advance 1
            | _ => pure ()
          else if isOctal c then
            -- 1–3 octal digits
            let mut n : Nat := octVal c
            r := r.advance 1
            match r.peek? with
            | some d2 =>
              if isOctal d2 then
                n := n * 8 + octVal d2
                r := r.advance 1
                match r.peek? with
                | some d3 =>
                  if isOctal d3 then
                    n := n * 8 + octVal d3
                    r := r.advance 1
                | _ => pure ()
            | _ => pure ()
            buf := buf.push (UInt8.ofNat (n % 256))
          else
            -- unknown escape: drop the backslash, keep the char
            buf := buf.push c; r := r.advance 1
      else if b = 0x0D then
        -- bare CR or CRLF inside string -> LF
        buf := buf.push 0x0A
        r := r.advance 1
        match r.peek? with
        | some 0x0A => r := r.advance 1
        | _ => pure ()
      else
        buf := buf.push b
        r := r.advance 1
  return (Token.litStr buf, r)

/-- Read a hexadecimal string `< … >`.  Cursor is at `<`.
    Whitespace is ignored; an odd nibble count gets a trailing 0. -/
def readHexString (r : Reader) : Token × Reader := Id.run do
  let mut r := r.advance 1
  let mut buf : ByteArray := ByteArray.empty
  let mut nibAcc : Nat := 0
  let mut haveHigh : Bool := false
  while ! r.atEOF do
    match r.peek? with
    | none => break
    | some b =>
      if b = 0x3E then
        r := r.advance 1
        if haveHigh then
          buf := buf.push (UInt8.ofNat (nibAcc * 16))
        break
      else if isWhite b then
        r := r.advance 1
      else if isHex b then
        let v := hexVal b
        if haveHigh then
          buf := buf.push (UInt8.ofNat (nibAcc * 16 + v))
          haveHigh := false
        else
          nibAcc := v
          haveHigh := true
        r := r.advance 1
      else
        -- invalid hex char; skip
        r := r.advance 1
  return (Token.hexStr buf, r)

/-- Read a name `/…`.  Cursor is at `/`. -/
def readName (r : Reader) : Token × Reader := Id.run do
  let mut r := r.advance 1
  let mut buf : ByteArray := ByteArray.empty
  while ! r.atEOF do
    match r.peek? with
    | none => break
    | some b =>
      if isRegular b then
        if b = 0x23 then
          -- #xx escape
          let h1 := r.peekAt? 1
          let h2 := r.peekAt? 2
          match h1, h2 with
          | some a, some b2 =>
            if isHex a && isHex b2 then
              buf := buf.push (UInt8.ofNat (hexVal a * 16 + hexVal b2))
              r := r.advance 3
            else
              buf := buf.push b
              r := r.advance 1
          | _, _ =>
            buf := buf.push b
            r := r.advance 1
        else
          buf := buf.push b
          r := r.advance 1
      else
        break
  return (Token.name buf, r)

/-- Read a keyword (longest run of regular characters). -/
def readKeyword (r : Reader) : Token × Reader := Id.run do
  let start := r.pos
  let mut r := r
  while ! r.atEOF do
    match r.peek? with
    | some b => if isRegular b then r := r.advance 1 else break
    | none => break
  let bs := r.data.extract start r.pos
  let s := String.fromUTF8! bs
  match s with
  | "true"  => return (Token.bool true, r)
  | "false" => return (Token.bool false, r)
  | "null"  => return (Token.null, r)
  | _       => return (Token.kw s, r)

/-- Skip whitespace and produce the next token. -/
def nextToken (r : Reader) : Token × Reader := Id.run do
  let r := skipWS r
  if r.atEOF then return (Token.eof, r)
  match r.peek? with
  | none => return (Token.eof, r)
  | some b =>
    if b = 0x28 then
      return readLiteralString r
    else if b = 0x3C then
      match r.peekAt? 1 with
      | some 0x3C => return (Token.dictOpen, r.advance 2)
      | _         => return readHexString r
    else if b = 0x3E then
      match r.peekAt? 1 with
      | some 0x3E => return (Token.dictClose, r.advance 2)
      | _         => return (Token.kw ">", r.advance 1)   -- spec: stray >
    else if b = 0x5B then return (Token.arrOpen, r.advance 1)
    else if b = 0x5D then return (Token.arrClose, r.advance 1)
    else if b = 0x2F then return readName r
    else if b = 0x2B || b = 0x2D || b = 0x2E || isDigit b then
      return readNumber r
    else
      return readKeyword r

end PdfLean
