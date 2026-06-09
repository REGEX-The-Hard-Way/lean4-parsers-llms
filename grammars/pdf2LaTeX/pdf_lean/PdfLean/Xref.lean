/-
  PdfLean.Xref
  ------------
  Locate `%%EOF` and `startxref`, then parse either a classic xref table
  (§7.5.4) or an xref stream (§7.5.8), following the `Prev` chain.
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import PdfLean.Object
import PdfLean.Stream
import Std.Data.HashMap

namespace PdfLean
open Std (HashMap)
open PdfLean.Lex

inductive XrefEntry where
  | free       (next : Nat) (gen : Nat)
  | inUse      (offset : Nat) (gen : Nat)
  | compressed (objStm : Nat) (index : Nat)
  deriving Repr, Inhabited

structure XrefTable where
  size    : Nat := 0
  entries : HashMap (Nat × Nat) XrefEntry := {}
  /-- A second index by object number only, holding the latest entry —
      used for resolution when generation isn't known a priori. -/
  byObj   : HashMap Nat XrefEntry := {}
  trailer : PDFObject := PDFObject.null

namespace XrefTable

def empty : XrefTable :=
  { size := 0, entries := {}, byObj := {}, trailer := PDFObject.null }

def insert (t : XrefTable) (objNum gen : Nat) (e : XrefEntry) : XrefTable :=
  { t with
      entries := t.entries.insert (objNum, gen) e
      byObj   := t.byObj.insert objNum e }

end XrefTable

/-- Locate the offset of the *last* `startxref OFFSET` and read the offset.
    Searches the last 4096 bytes of the file. -/
def findStartxref (data : ByteArray) : Except ParseError Nat := Id.run do
  let r : Reader := Reader.mk' data
  match r.findLast? "startxref".toUTF8 with
  | none => return Except.error { pos := r.size, msg := "no startxref found" }
  | some off =>
      let r := r.setPos (off + "startxref".toUTF8.size)
      let r := skipWS r
      let (tok, _) := nextToken r
      match tok with
      | Token.int n =>
          if n ≥ 0 then return Except.ok n.toNat
          else return Except.error { pos := r.pos, msg := "negative startxref" }
      | _ => return Except.error { pos := r.pos, msg := "no number after startxref" }

/-- Parse one xref subsection: starts with `FIRST COUNT` then `COUNT` entries.
    Returns the table updates and the reader. -/
partial def parseXrefSubsections (r : Reader) (acc : XrefTable) :
    Except ParseError (XrefTable × Reader) := do
  let r := skipWS r
  -- Either we see "trailer" (end of subsections) or "FIRST COUNT".
  if r.lookingAtStr "trailer" then
    return (acc, r)
  let (t1, r1) := nextToken r
  let (t2, r2) := nextToken r1
  match t1, t2 with
  | Token.int first, Token.int count =>
      if first < 0 ∨ count < 0 then
        Except.error { pos := r.pos, msg := "negative xref subsection header" }
      else
        let mut acc := acc
        let mut r := r2
        let mut i : Nat := 0
        while i < count.toNat do
          -- Find the start of this 20-byte entry: skip whitespace
          r := skipWS r
          -- Parse "OOOOOOOOOO GGGGG c"
          let (tA, ra) := nextToken r
          let (tB, rb) := nextToken ra
          let (tC, rc) := nextToken rb
          match tA, tB, tC with
          | Token.int a, Token.int b, Token.kw c =>
              let aN := a.toNat
              let bN := b.toNat
              let objNum := first.toNat + i
              if c = "n" then
                acc := acc.insert objNum bN (XrefEntry.inUse aN bN)
              else if c = "f" then
                acc := acc.insert objNum bN (XrefEntry.free aN bN)
              else
                pure ()  -- skip unknown
              r := rc
          | _, _, _ =>
              -- Defensive recovery: bail out
              return (acc, r)
          i := i + 1
        parseXrefSubsections r acc
  | _, _ => return (acc, r)

/-- Decode an xref-stream's binary data given the W widths.
    Each record is W[0] + W[1] + W[2] bytes; type defaults to 1 if W[0]=0. -/
def parseXrefStreamData (data : ByteArray) (w : Array Nat)
    (index : Array (Nat × Nat)) : XrefTable → XrefTable := fun acc => Id.run do
  let w0 := w.getD 0 1
  let w1 := w.getD 1 0
  let w2 := w.getD 2 0
  let recSize := w0 + w1 + w2
  if recSize = 0 then return acc
  let mut acc := acc
  let mut cursor : Nat := 0
  for (first, count) in index do
    for k in [0:count] do
      if cursor + recSize > data.size then
        return acc
      let mut tt : Nat := 1
      let mut p := cursor
      if w0 > 0 then
        let mut v : Nat := 0
        for j in [0:w0] do
          v := v * 256 + (data.get! (p + j)).toNat
        tt := v
      p := p + w0
      let mut f2 : Nat := 0
      for j in [0:w1] do
        f2 := f2 * 256 + (data.get! (p + j)).toNat
      p := p + w1
      let mut f3 : Nat := 0
      for j in [0:w2] do
        f3 := f3 * 256 + (data.get! (p + j)).toNat
      let objNum := first + k
      let entry :=
        if tt = 0 then XrefEntry.free f2 f3
        else if tt = 1 then XrefEntry.inUse f2 f3
        else if tt = 2 then XrefEntry.compressed f2 f3
        else XrefEntry.free 0 0   -- treat unknown as null (free)
      let gen := if tt = 1 then f3 else if tt = 0 then f3 else 0
      acc := acc.insert objNum gen entry
      cursor := cursor + recSize
  return acc

/-- Read one xref *section* starting at `offset`.  Returns the merged table
    and a possible next offset (from /Prev). -/
def readOneSection (data : ByteArray) (offset : Nat) (acc : XrefTable) :
    Except ParseError (XrefTable × Option Nat) := do
  let r : Reader := { data := data, pos := offset }
  let r := skipWS r
  if r.lookingAtStr "xref" then
    -- Classic table.
    let r := r.advance "xref".toUTF8.size
    let (acc, r) ← parseXrefSubsections r acc
    -- Trailer dict
    let r := skipWS r
    if ! r.lookingAtStr "trailer" then
      Except.error { pos := r.pos, msg := "expected 'trailer'" }
    else
      let r := r.advance "trailer".toUTF8.size
      let r := skipWS r
      let (trailer, _) ← parseObject r
      let acc := if acc.trailer matches PDFObject.null then { acc with trailer := trailer } else acc
      let prev :=
        match trailer.getKey "Prev" with
        | some (PDFObject.int n) => if n ≥ 0 then some n.toNat else none
        | _ => none
      let acc :=
        match trailer.getKey "Size" with
        | some (PDFObject.int n) => if n ≥ 0 ∧ acc.size = 0 then { acc with size := n.toNat } else acc
        | _ => acc
      Except.ok (acc, prev)
  else
    -- XRef stream: an indirect object follows.
    match parseIndirectObject r with
    | Except.error e => Except.error e
    | Except.ok ((_, _), obj, _) =>
        match obj with
        | PDFObject.stream d raw =>
            -- Required dict keys: Size, W; optional: Index, Prev.
            let dictObj := PDFObject.dict d
            let size :=
              match dictObj.getKey "Size" with
              | some (PDFObject.int n) => if n ≥ 0 then n.toNat else 0
              | _ => 0
            let w : Array Nat :=
              match dictObj.getKey "W" with
              | some (PDFObject.array xs) =>
                  xs.map (fun o => match o with
                    | PDFObject.int n => if n ≥ 0 then n.toNat else 0
                    | _ => 0)
              | _ => #[1, 0, 0]
            let index : Array (Nat × Nat) :=
              match dictObj.getKey "Index" with
              | some (PDFObject.array xs) => Id.run do
                  let mut out : Array (Nat × Nat) := #[]
                  let mut i := 0
                  while i + 1 < xs.size do
                    let a := match xs[i]! with
                      | PDFObject.int n => if n ≥ 0 then n.toNat else 0
                      | _ => 0
                    let b := match xs[i+1]! with
                      | PDFObject.int n => if n ≥ 0 then n.toNat else 0
                      | _ => 0
                    out := out.push (a, b)
                    i := i + 2
                  pure out
              | _ => #[(0, size)]
            -- NOTE: stream may be Flate-compressed; we don't decompress here.
            -- The caller is responsible for ensuring streams are uncompressed.
            let acc := parseXrefStreamData raw w index acc
            let acc := if acc.size = 0 then { acc with size := size } else acc
            let acc := if acc.trailer matches PDFObject.null
                       then { acc with trailer := dictObj } else acc
            let prev :=
              match dictObj.getKey "Prev" with
              | some (PDFObject.int n) => if n ≥ 0 then some n.toNat else none
              | _ => none
            Except.ok (acc, prev)
        | _ => Except.error { pos := r.pos, msg := "xref offset not stream nor table" }

/-- Walk the Prev chain, accumulating the latest entry for each (objNum, gen). -/
partial def loadXrefChain (data : ByteArray) (offset : Nat) (acc : XrefTable)
    (depth : Nat := 0) : Except ParseError XrefTable := do
  if depth > 64 then return acc   -- guard against cycles
  let (acc', prev) ← readOneSection data offset acc
  match prev with
  | some p => loadXrefChain data p acc' (depth + 1)
  | none   => Except.ok acc'

/-- Top-level: read a PDF file's cross-reference table. -/
def loadXref (data : ByteArray) : Except ParseError XrefTable := do
  let off ← findStartxref data
  loadXrefChain data off XrefTable.empty

end PdfLean
