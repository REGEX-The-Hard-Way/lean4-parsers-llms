/-
  PdfLean.Document
  ----------------
  Glue: open a file, build the xref, resolve indirect objects, walk the
  page tree.  Object-stream (compressed object) resolution is supported
  for already-decompressed streams.
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import PdfLean.Object
import PdfLean.Stream
import PdfLean.Xref

namespace PdfLean
open PdfLean.Lex
open Std (HashMap)

structure Document where
  data  : ByteArray
  xref  : XrefTable
  /-- Cache of resolved indirect objects.  Lazy. -/
  cache : HashMap (Nat × Nat) PDFObject := {}

namespace Document

def open' (data : ByteArray) : Except ParseError Document := do
  let x ← loadXref data
  Except.ok { data := data, xref := x, cache := {} }

/-- Fetch an indirect object by `(objNum, gen)`.  Returns `null` if missing. -/
partial def fetch (d : Document) (objNum gen : Nat) :
    Except ParseError (PDFObject × Document) := do
  match d.cache[(objNum, gen)]? with
  | some o => Except.ok (o, d)
  | none =>
    let entry :=
      match d.xref.entries[(objNum, gen)]? with
      | some e => some e
      | none   => d.xref.byObj[objNum]?
    match entry with
    | none => Except.ok (PDFObject.null, d)
    | some (XrefEntry.free _ _) => Except.ok (PDFObject.null, d)
    | some (XrefEntry.inUse off _) =>
        let r : Reader := { data := d.data, pos := off }
        let ((_o, _g), val, _) ← parseIndirectObject r
        let d' := { d with cache := d.cache.insert (objNum, gen) val }
        Except.ok (val, d')
    | some (XrefEntry.compressed objStmNum idx) =>
        -- Resolve the containing object stream then extract object idx.
        let (objStm, d) ← d.fetch objStmNum 0
        match objStm with
        | PDFObject.stream sd raw =>
            let dictObj := PDFObject.dict sd
            let n := match dictObj.getKey "N" with
              | some (PDFObject.int n) => if n ≥ 0 then n.toNat else 0
              | _ => 0
            let first := match dictObj.getKey "First" with
              | some (PDFObject.int n) => if n ≥ 0 then n.toNat else 0
              | _ => 0
            -- Read N (objnum, offset) pairs from start of the stream.
            let r0 : Reader := { data := raw, pos := 0 }
            let mut pairs : Array (Nat × Nat) := #[]
            let mut r := r0
            let mut i : Nat := 0
            while i < n do
              let (ta, ra) := nextToken r
              let (tb, rb) := nextToken ra
              match ta, tb with
              | Token.int o, Token.int off =>
                  if o ≥ 0 ∧ off ≥ 0 then
                    pairs := pairs.push (o.toNat, off.toNat)
              | _, _ => pure ()
              r := rb
              i := i + 1
            if idx ≥ pairs.size then
              return (PDFObject.null, d)
            let (_, off) := pairs[idx]!
            let r2 : Reader := { data := raw, pos := first + off }
            let (val, _) ← parseObject r2
            let d' := { d with cache := d.cache.insert (objNum, gen) val }
            Except.ok (val, d')
        | _ => Except.ok (PDFObject.null, d)

/-- One-step dereference: if `o` is a `ref`, fetch it. -/
def deref (d : Document) (o : PDFObject) :
    Except ParseError (PDFObject × Document) :=
  match o with
  | PDFObject.ref n g => d.fetch n g
  | _                 => Except.ok (o, d)

/-- Recursively dereference (with cycle bound). -/
partial def derefDeep (d : Document) (o : PDFObject) (fuel : Nat := 64) :
    Except ParseError (PDFObject × Document) := do
  if fuel = 0 then return (o, d)
  match o with
  | PDFObject.ref n g =>
      let (o', d') ← d.fetch n g
      derefDeep d' o' (fuel - 1)
  | _ => Except.ok (o, d)

/-- Return the document catalog (referenced from /Root in the trailer). -/
def catalog (d : Document) : Except ParseError (PDFObject × Document) := do
  let root := d.xref.trailer.getKey "Root"
  match root with
  | some o => d.derefDeep o
  | none   => Except.error { pos := 0, msg := "no /Root in trailer" }

/-- Walk the /Pages tree and return a flat list of page-dictionary objects. -/
partial def collectPages (d : Document) (node : PDFObject) (acc : Array PDFObject) :
    Except ParseError (Array PDFObject × Document) := do
  let (node, d) ← d.derefDeep node
  match node.getKey "Type" with
  | some (PDFObject.name n) =>
      let s := String.fromUTF8! n
      if s = "Pages" then
        match node.getKey "Kids" with
        | some (PDFObject.array kids) =>
            let mut acc := acc
            let mut d := d
            for k in kids do
              let (kids', d') ← d.collectPages k acc
              acc := kids'
              d := d'
            return (acc, d)
        | _ => return (acc, d)
      else if s = "Page" then
        return (acc.push node, d)
      else
        return (acc, d)
  | _ => return (acc, d)

/-- Top-level: list of all page objects (dereferenced). -/
def pages (d : Document) : Except ParseError (Array PDFObject × Document) := do
  let (cat, d) ← d.catalog
  match cat.getKey "Pages" with
  | some root => d.collectPages root #[]
  | none      => Except.error { pos := 0, msg := "catalog has no /Pages" }

end Document
end PdfLean
