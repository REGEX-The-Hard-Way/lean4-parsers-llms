/-
  PdfLean.Stream
  --------------
  Indirect-object parsing including stream extraction.
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import PdfLean.Object

namespace PdfLean
open PdfLean.Lex

/-- Parse a stream body once we've seen the dictionary and the keyword
    `stream`.  `r` is positioned just after `stream`.  Returns the raw bytes
    and a reader past `endstream`.

    `lengthHint` is the value of /Length from the dict if it is a literal
    integer; otherwise `none` (in which case we scan for `endstream`). -/
def parseStreamBody (r : Reader) (lengthHint : Option Nat) :
    Except ParseError (ByteArray × Reader) := do
  -- §7.3.8.1: the keyword `stream` is followed by EOL (CRLF or LF, NOT bare CR).
  let r := match r.peek? with
    | some 0x0D =>
        match r.peekAt? 1 with
        | some 0x0A => r.advance 2
        | _         => r.advance 1     -- forgiving
    | some 0x0A => r.advance 1
    | _ => r
  match lengthHint with
  | some n =>
      let (raw, r') := r.take n
      -- Skip optional EOL then expect "endstream"
      let r' := Lex.skipWS r'
      let (t, r'') := nextToken r'
      match t with
      | Token.kw "endstream" => Except.ok (raw, r'')
      | _ =>
          -- Try a forward scan as fallback
          match r.find? "endstream".toUTF8 r.pos with
          | some off =>
              -- Trim trailing EOL before the keyword
              let mut endRaw := off
              if endRaw > 0 ∧ r.data.get! (endRaw - 1) = 0x0A then endRaw := endRaw - 1
              if endRaw > 0 ∧ r.data.get! (endRaw - 1) = 0x0D then endRaw := endRaw - 1
              let raw := r.data.extract r.pos endRaw
              let after := off + "endstream".toUTF8.size
              Except.ok (raw, { r with pos := after })
          | none => Except.error { pos := r.pos, msg := "unterminated stream" }
  | none =>
      match r.find? "endstream".toUTF8 r.pos with
      | some off =>
          let mut endRaw := off
          if endRaw > 0 ∧ r.data.get! (endRaw - 1) = 0x0A then endRaw := endRaw - 1
          if endRaw > 0 ∧ r.data.get! (endRaw - 1) = 0x0D then endRaw := endRaw - 1
          let raw := r.data.extract r.pos endRaw
          let after := off + "endstream".toUTF8.size
          Except.ok (raw, { r with pos := after })
      | none => Except.error { pos := r.pos, msg := "unterminated stream (no length)" }

/-- The body of an indirect object: either a plain object, or a dict
    followed by a `stream … endstream` block. -/
def parseIndirectBody (r : Reader) : Except ParseError (PDFObject × Reader) := do
  let (val, r') ← parseObject r
  -- If the value is a dictionary, check whether `stream` follows.
  match val with
  | PDFObject.dict d =>
      let r'' := Lex.skipWS r'
      if r''.lookingAtStr "stream" then
        let r3 := r''.advance "stream".toUTF8.size
        let lenHint :=
          match d.find? "Length".toUTF8 with
          | some (PDFObject.int n) => if n ≥ 0 then some n.toNat else none
          | _ => none
        let (raw, r4) ← parseStreamBody r3 lenHint
        return (PDFObject.stream d raw, r4)
      else
        return (val, r')
  | _ => return (val, r')

/-- Parse a single `N G obj … endobj` definition starting at the cursor.
    Returns `((objNum, gen), object, reader-after-endobj)`. -/
def parseIndirectObject (r : Reader) :
    Except ParseError ((Nat × Nat) × PDFObject × Reader) := do
  let (t1, r1) := nextToken r
  let (t2, r2) := nextToken r1
  let (t3, r3) := nextToken r2
  match t1, t2, t3 with
  | Token.int o, Token.int g, Token.kw "obj" =>
      if o < 0 ∨ g < 0 then
        Except.error { pos := r.pos, msg := "negative obj id" }
      else
        let (val, r4) ← parseIndirectBody r3
        let r5 := Lex.skipWS r4
        let (t4, r6) := nextToken r5
        match t4 with
        | Token.kw "endobj" => Except.ok ((o.toNat, g.toNat), val, r6)
        | _ => Except.error { pos := r5.pos, msg := s!"expected endobj, got {t4}" }
  | _, _, _ => Except.error { pos := r.pos, msg := "expected 'N G obj'" }

end PdfLean
