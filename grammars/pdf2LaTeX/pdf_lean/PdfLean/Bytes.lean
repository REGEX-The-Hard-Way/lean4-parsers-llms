/-
  PdfLean.Bytes
  -------------
  Low-level byte buffer reader.  Wraps a `ByteArray` and a position cursor;
  every primitive parser in the library threads one of these.
-/

namespace PdfLean

/-- Parse error with byte offset and message. -/
structure ParseError where
  pos : Nat
  msg : String
  deriving Repr, Inhabited

instance : ToString ParseError where
  toString e := s!"parse error @ {e.pos}: {e.msg}"

/-- Position-tracking byte reader. -/
structure Reader where
  data : ByteArray
  pos  : Nat := 0

namespace Reader

@[inline] def size (r : Reader) : Nat := r.data.size

@[inline] def remaining (r : Reader) : Nat := r.size - r.pos

@[inline] def atEOF (r : Reader) : Bool := r.pos ≥ r.size

@[inline] def peek? (r : Reader) : Option UInt8 :=
  if r.pos < r.data.size then some (r.data.get! r.pos) else none

@[inline] def peekAt? (r : Reader) (off : Nat) : Option UInt8 :=
  let i := r.pos + off
  if i < r.data.size then some (r.data.get! i) else none

@[inline] def get? (r : Reader) (i : Nat) : Option UInt8 :=
  if i < r.data.size then some (r.data.get! i) else none

@[inline] def advance (r : Reader) (n : Nat) : Reader :=
  { r with pos := min (r.pos + n) r.size }

@[inline] def setPos (r : Reader) (p : Nat) : Reader :=
  { r with pos := min p r.size }

/-- Read `n` raw bytes starting at the cursor; advances cursor. -/
def take (r : Reader) (n : Nat) : ByteArray × Reader :=
  let stop := min (r.pos + n) r.size
  (r.data.extract r.pos stop, { r with pos := stop })

/-- Compare a literal byte sequence at the cursor. -/
def lookingAt (r : Reader) (bs : ByteArray) : Bool :=
  if r.pos + bs.size > r.size then false
  else Id.run do
    let mut i := 0
    while i < bs.size do
      if r.data.get! (r.pos + i) ≠ bs.get! i then
        return false
      i := i + 1
    return true

def lookingAtStr (r : Reader) (s : String) : Bool :=
  lookingAt r s.toUTF8

/-- Big-endian unsigned int decode of `n` bytes from the cursor.
    Used by the xref-stream binary format (§ 7.5.8.3). -/
def readBEUInt (r : Reader) (n : Nat) : Nat × Reader := Id.run do
  let mut acc : Nat := 0
  let mut i := 0
  while i < n do
    if r.pos + i < r.size then
      acc := acc * 256 + (r.data.get! (r.pos + i)).toNat
    i := i + 1
  return (acc, r.advance n)

/-- Search for a literal byte pattern starting at or after `from`,
    returning the offset where the pattern begins. -/
def find? (r : Reader) (pat : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  if pat.size = 0 then return some start
  if r.size < pat.size then return none
  let upper := r.size - pat.size
  let mut i := start
  while i ≤ upper do
    let mut ok := true
    let mut j := 0
    while j < pat.size do
      if r.data.get! (i + j) ≠ pat.get! j then
        ok := false
        break
      j := j + 1
    if ok then return some i
    i := i + 1
  return none

/-- Search backwards for a literal byte pattern (rightmost occurrence). -/
def findLast? (r : Reader) (pat : ByteArray) : Option Nat := Id.run do
  if pat.size = 0 ∨ r.size < pat.size then return none
  let mut i := r.size - pat.size
  while true do
    let mut ok := true
    let mut j := 0
    while j < pat.size do
      if r.data.get! (i + j) ≠ pat.get! j then
        ok := false
        break
      j := j + 1
    if ok then return some i
    if i = 0 then break
    i := i - 1
  return none

end Reader

/-- Construct a reader over a whole `ByteArray`. -/
def Reader.mk' (data : ByteArray) : Reader := { data := data, pos := 0 }

end PdfLean
