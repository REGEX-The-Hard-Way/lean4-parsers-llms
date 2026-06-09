/-
  PdfLean.CMap
  ------------
  Parser for the small PostScript-flavoured language used in PDF
  /ToUnicode CMap streams (§9.10.3).

  Supports `bfchar` and `bfrange` blocks (covers ~99% of real PDFs).
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import Std.Data.HashMap

namespace PdfLean
open PdfLean.Lex
open Std (HashMap)

/-- A CMap: glyph identifier (treated as a `Nat`) → UTF-8 byte string. -/
structure CMap where
  codeBytes : Nat := 1
  table     : HashMap Nat ByteArray := {}

instance : Inhabited CMap := ⟨{}⟩

def CMap.empty : CMap := { codeBytes := 1, table := {} }

def CMap.lookup? (m : CMap) (code : Nat) : Option ByteArray :=
  m.table[code]?

/-- Parse a hex string body into `(value, byteWidth)`. -/
def parseHexCode (bs : ByteArray) : Nat × Nat := Id.run do
  let mut v : Nat := 0
  let mut digits : Nat := 0
  for i in [0:bs.size] do
    let b := bs[i]!
    if Lex.isHex b then
      v := v * 16 + Lex.hexVal b
      digits := digits + 1
  return (v, (digits + 1) / 2)

/-- Encode a Unicode codepoint as UTF-8 bytes. -/
def utf8Bytes (cp : Nat) : ByteArray :=
  if cp < 0x80 then ByteArray.empty.push (UInt8.ofNat cp)
  else if cp < 0x800 then
    ByteArray.empty
      |>.push (UInt8.ofNat (0xC0 ||| (cp >>> 6)))
      |>.push (UInt8.ofNat (0x80 ||| (cp &&& 0x3F)))
  else if cp < 0x10000 then
    ByteArray.empty
      |>.push (UInt8.ofNat (0xE0 ||| (cp >>> 12)))
      |>.push (UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)))
      |>.push (UInt8.ofNat (0x80 ||| (cp &&& 0x3F)))
  else
    ByteArray.empty
      |>.push (UInt8.ofNat (0xF0 ||| (cp >>> 18)))
      |>.push (UInt8.ofNat (0x80 ||| ((cp >>> 12) &&& 0x3F)))
      |>.push (UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)))
      |>.push (UInt8.ofNat (0x80 ||| (cp &&& 0x3F)))

/-- Decode a CMap destination hex string into UTF-8 bytes.  Each 4-hex-
    digit chunk is a Unicode BMP code; surrogate pairs combine. -/
def decodeDest (bs : ByteArray) : ByteArray := Id.run do
  let mut digits : Array Nat := #[]
  for i in [0:bs.size] do
    let b := bs[i]!
    if Lex.isHex b then digits := digits.push (Lex.hexVal b)
  let mut codes : Array Nat := #[]
  let mut i := 0
  while i + 3 < digits.size do
    let v := digits[i]! * 4096 + digits[i+1]! * 256
           + digits[i+2]! * 16   + digits[i+3]!
    codes := codes.push v
    i := i + 4
  let mut out : ByteArray := ByteArray.empty
  let mut j := 0
  while j < codes.size do
    let c := codes[j]!
    if c ≥ 0xD800 ∧ c ≤ 0xDBFF ∧ j + 1 < codes.size then
      let low := codes[j+1]!
      if low ≥ 0xDC00 ∧ low ≤ 0xDFFF then
        let cp := 0x10000 + ((c - 0xD800) * 0x400) + (low - 0xDC00)
        out := out ++ utf8Bytes cp
        j := j + 2
      else
        out := out ++ utf8Bytes c; j := j + 1
    else
      out := out ++ utf8Bytes c; j := j + 1
  return out

/-- Parse the body of a `beginbfchar … endbfchar` block.
    Cursor is just after `beginbfchar`. -/
partial def parseBfChar (r : Reader) (m : CMap) : CMap × Reader := Id.run do
  let mut r := r
  let mut m := m
  while ! r.atEOF do
    let (t1, r1) := nextToken r
    match t1 with
    | Token.kw "endbfchar" => return (m, r1)
    | Token.hexStr src =>
        let (sCode, _) := parseHexCode src
        let (t2, r2) := nextToken r1
        match t2 with
        | Token.hexStr dst =>
            let dec := decodeDest dst
            m := { m with table := m.table.insert sCode dec }
            r := r2
        | _ => r := r2
    | Token.eof => return (m, r1)
    | _ => return (m, r)
  return (m, r)

/-- Parse a `beginbfrange … endbfrange` block. -/
partial def parseBfRange (r : Reader) (m : CMap) : CMap × Reader := Id.run do
  let mut r := r
  let mut m := m
  while ! r.atEOF do
    let (t1, r1) := nextToken r
    match t1 with
    | Token.kw "endbfrange" => return (m, r1)
    | Token.hexStr lo =>
        let (loCode, _) := parseHexCode lo
        let (t2, r2) := nextToken r1
        match t2 with
        | Token.hexStr hi =>
            let (hiCode, _) := parseHexCode hi
            let (t3, r3) := nextToken r2
            match t3 with
            | Token.hexStr dst =>
                -- Compute integer value of dst
                let mut digits : Array Nat := #[]
                for i in [0:dst.size] do
                  let b := dst[i]!
                  if Lex.isHex b then digits := digits.push (Lex.hexVal b)
                let mut dstVal : Nat := 0
                for d in digits do dstVal := dstVal * 16 + d
                let count := if hiCode ≥ loCode then hiCode - loCode + 1 else 1
                for k in [0:count] do
                  let bs := utf8Bytes (dstVal + k)
                  m := { m with table := m.table.insert (loCode + k) bs }
                r := r3
            | Token.arrOpen =>
                let mut rr := r3
                let mut idx : Nat := 0
                let mut done := false
                while ! done && ! rr.atEOF do
                  let (tx, rx) := nextToken rr
                  match tx with
                  | Token.arrClose => rr := rx; done := true
                  | Token.hexStr d =>
                      let dec := decodeDest d
                      m := { m with table := m.table.insert (loCode + idx) dec }
                      idx := idx + 1
                      rr := rx
                  | Token.eof => done := true
                  | _ => rr := rx
                r := rr
            | _ => r := r3
        | _ => r := r2
    | Token.eof => return (m, r1)
    | _ => return (m, r)
  return (m, r)

/-- Parse a complete /ToUnicode CMap stream. -/
partial def parseCMap (raw : ByteArray) : CMap := Id.run do
  let mut r : Reader := Reader.mk' raw
  let mut m : CMap := CMap.empty
  let mut maxWidth : Nat := 1
  while ! r.atEOF do
    let r' := skipWS r
    if r'.atEOF then break
    let (tok, rn) := nextToken r'
    match tok with
    | Token.kw "beginbfchar"  => let (m', rn') := parseBfChar  rn m
                                 m := m'; r := rn'
    | Token.kw "beginbfrange" => let (m', rn') := parseBfRange rn m
                                 m := m'; r := rn'
    | Token.kw "endcmap" => break
    | Token.eof => break
    | Token.hexStr bs =>
        let (_, w) := parseHexCode bs
        if w > maxWidth then maxWidth := w
        r := rn
    | _ => r := rn
  return { m with codeBytes := maxWidth }

/-- Apply a CMap to one source code; falls back to ASCII byte for codes
    < 0x80 in single-byte CMaps so fonts without ToUnicode still produce
    something legible. -/
def CMap.applyCode (m : CMap) (code : Nat) : ByteArray :=
  match m.table[code]? with
  | some bs => bs
  | none    =>
      if m.codeBytes ≤ 1 ∧ code < 0x80 then
        ByteArray.empty.push (UInt8.ofNat code)
      else ByteArray.empty

/-- Apply a CMap to a sequence of operand bytes; codes are read in
    chunks of `m.codeBytes`. -/
def CMap.applyBytes (m : CMap) (bs : ByteArray) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let w := if m.codeBytes = 0 then 1 else m.codeBytes
  let mut i : Nat := 0
  while i + w ≤ bs.size do
    let mut code : Nat := 0
    for k in [0:w] do
      code := code * 256 + (bs[i + k]!).toNat
    out := out ++ m.applyCode code
    i := i + w
  return out

end PdfLean
