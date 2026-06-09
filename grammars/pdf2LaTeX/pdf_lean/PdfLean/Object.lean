/-
  PdfLean.Object
  --------------
  Parser for PDF direct objects (no streams; streams are spliced in by
  the indirect-object parser).
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast

namespace PdfLean
open PdfLean.Lex

abbrev Parse (α) := Reader → Except ParseError (α × Reader)

@[inline] def err (r : Reader) (msg : String) : Except ParseError α :=
  Except.error { pos := r.pos, msg := msg }

mutual

partial def parseObject : Parse PDFObject := fun r => do
  let r0 := r
  let (t, r1) := nextToken r
  match t with
  | Token.bool b   => Except.ok (PDFObject.bool b, r1)
  | Token.null     => Except.ok (PDFObject.null, r1)
  | Token.litStr s => Except.ok (PDFObject.str s StringKind.literal, r1)
  | Token.hexStr s => Except.ok (PDFObject.str s StringKind.hex, r1)
  | Token.name n   => Except.ok (PDFObject.name n, r1)
  | Token.real s   => Except.ok (PDFObject.real s, r1)
  | Token.arrOpen  => parseArrayBody r1 #[]
  | Token.dictOpen => parseDictBody r1 #[]
  | Token.int n    =>
      let (t2, r2) := nextToken r1
      match t2 with
      | Token.int g =>
          let (t3, r3) := nextToken r2
          match t3 with
          | Token.kw "R" =>
              if n ≥ 0 ∧ g ≥ 0 then
                Except.ok (PDFObject.ref n.toNat g.toNat, r3)
              else
                Except.ok (PDFObject.int n, r1)
          | _ => Except.ok (PDFObject.int n, r1)
      | _ => Except.ok (PDFObject.int n, r1)
  | Token.kw kw    => err r0 s!"unexpected keyword '{kw}' while parsing object"
  | Token.arrClose => err r0 "unexpected ']'"
  | Token.dictClose => err r0 "unexpected '>>'"
  | Token.eof      => err r0 "unexpected EOF"

partial def parseArrayBody (r : Reader) (acc : Array PDFObject) :
    Except ParseError (PDFObject × Reader) := do
  let r' := skipWS r
  let (t, r2) := nextToken r'
  match t with
  | Token.arrClose => Except.ok (PDFObject.array acc, r2)
  | Token.eof      => err r' "EOF in array"
  | _ =>
      -- Re-parse from r' as a full object
      let (o, rn) ← parseObject r'
      parseArrayBody rn (acc.push o)

partial def parseDictBody (r : Reader) (acc : Array (ByteArray × PDFObject)) :
    Except ParseError (PDFObject × Reader) := do
  let r' := skipWS r
  let (t, r2) := nextToken r'
  match t with
  | Token.dictClose =>
      Except.ok (PDFObject.dict (DictEntries.ofList acc.toList), r2)
  | Token.eof => err r' "EOF in dict"
  | Token.name k =>
      let (v, rn) ← parseObject r2
      match v with
      | PDFObject.null => parseDictBody rn acc
      | _              => parseDictBody rn (acc.push (k, v))
  | _ => err r' s!"expected name in dict, got {t}"

end

end PdfLean
