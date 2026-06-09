/-
  PdfLean.Content
  ---------------
  Content-stream parser (§7.8.2).  We parse into a sequence of
  `(operator, operands)` pairs without trying to interpret them.
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import PdfLean.Object

namespace PdfLean
open PdfLean.Lex

structure Op where
  name     : String
  operands : Array PDFObject
  deriving Inhabited

def Op.repr (o : Op) : String :=
  let opS := o.operands.map PDFObject.repr
  String.intercalate " " (opS.toList ++ [o.name])

instance : Repr Op := ⟨fun o _ => o.repr⟩
instance : ToString Op := ⟨Op.repr⟩

/-- Parse a content stream into a list of operations.  Inline images
    (`BI ... ID ... EI`) are emitted as a synthetic op named `BI` whose
    operands are the dictionary entries followed by a literal-string with
    the image bytes. -/
partial def parseContent (raw : ByteArray) : Array Op := Id.run do
  let mut r : Reader := Reader.mk' raw
  let mut ops : Array Op := #[]
  let mut operands : Array PDFObject := #[]
  while ! r.atEOF do
    let r' := skipWS r
    if r'.atEOF then break
    -- Save position so we can call parseObject and have it consume
    -- a single object including any leading int that isn't a ref.
    -- The trick: in a content stream, a keyword always closes operands.
    -- So we peek the next token.
    match r'.peek? with
    | none => break
    | some b =>
      -- If this looks like a keyword (regular but NOT a number/name/string
      -- delimiter), consume it as an operator.
      if b = 0x2F                              -- name
         ∨ b = 0x28                            -- (
         ∨ b = 0x3C                            -- < or <<
         ∨ b = 0x5B                            -- [
         ∨ b = 0x2B ∨ b = 0x2D ∨ b = 0x2E      -- + - .
         ∨ isDigit b
      then
        -- Parse as a direct object
        match parseObject r' with
        | Except.error _ => break
        | Except.ok (o, rn) =>
            operands := operands.push o
            r := rn
      else
        -- Read the keyword
        let (tk, rn) := nextToken r'
        match tk with
        | Token.kw name =>
            -- Special case: BI ... ID ... EI
            if name = "BI" then
              -- Read image dict entries until we see "ID"
              let mut entries : Array PDFObject := #[]
              let mut rr := rn
              let mut done := false
              while ! done && ! rr.atEOF do
                let rr' := skipWS rr
                if rr'.lookingAtStr "ID" then
                  rr := rr'.advance 2
                  done := true
                else
                  match parseObject rr' with
                  | Except.error _ => done := true
                  | Except.ok (o, rn2) =>
                      entries := entries.push o
                      rr := rn2
              -- Skip exactly one whitespace byte after ID, then scan for EI
              match rr.peek? with
              | some b => if isWhite b then rr := rr.advance 1
              | none => pure ()
              -- Find EI preceded by whitespace
              let pat : ByteArray := "EI".toUTF8
              match rr.find? pat rr.pos with
              | some off =>
                  let imgBytes := rr.data.extract rr.pos off
                  ops := ops.push {
                    name := "BI"
                    operands := entries.push (PDFObject.str imgBytes StringKind.literal)
                  }
                  r := { rr with pos := off + 2 }
              | none =>
                  break
            else
              ops := ops.push { name := name, operands := operands }
              operands := #[]
              r := rn
        | Token.bool _ | Token.null =>
            -- Treat true/false/null as operands by re-parsing
            match parseObject r' with
            | Except.error _ => break
            | Except.ok (o, rn) =>
                operands := operands.push o
                r := rn
        | Token.eof => break
        | _ =>
            match parseObject r' with
            | Except.error _ => break
            | Except.ok (o, rn) =>
                operands := operands.push o
                r := rn
  return ops

end PdfLean
