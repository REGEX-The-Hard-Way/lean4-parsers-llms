/-
  PdfLean.Lex
  -----------
  Character-class predicates and whitespace/comment skipping.
  Matches §7.2 of ISO 32000-1:2008.
-/
import PdfLean.Bytes

namespace PdfLean.Lex
open PdfLean

/-- §7.2.2 white-space characters: NUL HT LF FF CR SP. -/
@[inline] def isWhite (b : UInt8) : Bool :=
  b = 0 || b = 9 || b = 10 || b = 12 || b = 13 || b = 32

/-- §7.2.2 delimiter characters. -/
@[inline] def isDelim (b : UInt8) : Bool :=
  b = 0x28 || b = 0x29 || b = 0x3C || b = 0x3E ||
  b = 0x5B || b = 0x5D || b = 0x7B || b = 0x7D ||
  b = 0x2F || b = 0x25

@[inline] def isRegular (b : UInt8) : Bool :=
  ! isWhite b && ! isDelim b

@[inline] def isDigit (b : UInt8) : Bool := b ≥ 0x30 && b ≤ 0x39
@[inline] def isOctal (b : UInt8) : Bool := b ≥ 0x30 && b ≤ 0x37
@[inline] def isHex   (b : UInt8) : Bool :=
  (b ≥ 0x30 && b ≤ 0x39) || (b ≥ 0x41 && b ≤ 0x46) || (b ≥ 0x61 && b ≤ 0x66)

@[inline] def hexVal (b : UInt8) : Nat :=
  if b ≤ 0x39 then (b - 0x30).toNat
  else if b ≤ 0x46 then (b - 0x41 + 10).toNat
  else (b - 0x61 + 10).toNat

@[inline] def octVal (b : UInt8) : Nat := (b - 0x30).toNat

/-- Eat one EOL marker (CRLF, LF, or CR).  Returns whether one was consumed. -/
def eatEOL (r : Reader) : Bool × Reader :=
  match r.peek? with
  | some 0x0D =>
      match r.peekAt? 1 with
      | some 0x0A => (true, r.advance 2)
      | _         => (true, r.advance 1)
  | some 0x0A => (true, r.advance 1)
  | _         => (false, r)

/-- Skip a single comment beginning at `%` (consumes terminating EOL). -/
def skipComment (r : Reader) : Reader := Id.run do
  let mut r := r
  -- consume initial '%'
  match r.peek? with
  | some 0x25 => r := r.advance 1
  | _ => return r
  while ! r.atEOF do
    match r.peek? with
    | some 0x0A | some 0x0D => break
    | _ => r := r.advance 1
  let (_, r2) := eatEOL r
  return r2

/-- §7.2 whitespace + comments collapse to a single separator. -/
def skipWS (r : Reader) : Reader := Id.run do
  let mut r := r
  while ! r.atEOF do
    match r.peek? with
    | some b =>
        if isWhite b then
          r := r.advance 1
        else if b = 0x25 then
          r := skipComment r
        else
          break
    | none => break
  return r

end PdfLean.Lex
