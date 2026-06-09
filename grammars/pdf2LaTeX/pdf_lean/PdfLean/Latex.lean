/-
  PdfLean.Latex
  -------------
  Render parsed page content as LaTeX.  The strategy: for each page we
  emit a `tikzpicture` of the page's MediaBox, with one `\node` per text
  run at its current text-matrix position.  Graphics state (q/Q, cm),
  text state (BT/ET, Td/TD/Tm/T*, Tf), and text-showing operators
  (Tj/TJ/'/") are tracked.  Everything else is ignored.
-/
import PdfLean.Bytes
import PdfLean.Lex
import PdfLean.Tokens
import PdfLean.Ast
import PdfLean.Object
import PdfLean.Document
import PdfLean.CMap
import PdfLean.Aglfn
import PdfLean.Content
import Std.Data.HashMap

namespace PdfLean
open Std (HashMap)

/-- A 3x3 PDF transformation matrix `[a b 0; c d 0; e f 1]` represented
    as the six free parameters `(a, b, c, d, e, f)`. -/
structure Mat where
  a : Float := 1
  b : Float := 0
  c : Float := 0
  d : Float := 1
  e : Float := 0
  f : Float := 0
  deriving Inhabited

namespace Mat
def id : Mat := {}

def mul (m n : Mat) : Mat :=
  { a := m.a * n.a + m.b * n.c
  , b := m.a * n.b + m.b * n.d
  , c := m.c * n.a + m.d * n.c
  , d := m.c * n.b + m.d * n.d
  , e := m.e * n.a + m.f * n.c + n.e
  , f := m.e * n.b + m.f * n.d + n.f }

/-- Apply the matrix to a point. -/
def apply (m : Mat) (x y : Float) : Float × Float :=
  (m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f)
end Mat

/-- LaTeX-escape a single Unicode codepoint, returning UTF-8 text. -/
def escapeCp (cp : Nat) : String :=
  if cp < 0x20 then ""
  else if cp = 0x5C then "\\textbackslash{}"
  else if cp = 0x7B then "\\{"
  else if cp = 0x7D then "\\}"
  else if cp = 0x23 then "\\#"
  else if cp = 0x24 then "\\$"
  else if cp = 0x25 then "\\%"
  else if cp = 0x26 then "\\&"
  else if cp = 0x5F then "\\_"
  else if cp = 0x5E then "\\^{}"
  else if cp = 0x7E then "\\~{}"
  else if cp = 0x3C then "\\textless{}"
  else if cp = 0x3E then "\\textgreater{}"
  else
    String.singleton (Char.ofNat cp)

/-- Walk a UTF-8 byte sequence and emit LaTeX-escaped text. -/
def utf8ToLatex (bs : ByteArray) : String := Id.run do
  let mut s := ""
  let mut i : Nat := 0
  while i < bs.size do
    let b := bs[i]!
    if b < 0x80 then
      s := s ++ escapeCp b.toNat
      i := i + 1
    else if b < 0xC0 then
      -- stray continuation; skip
      i := i + 1
    else if b < 0xE0 ∧ i + 1 < bs.size then
      let cp := ((b - 0xC0).toNat * 64) + (bs[i+1]! - 0x80).toNat
      s := s ++ escapeCp cp
      i := i + 2
    else if b < 0xF0 ∧ i + 2 < bs.size then
      let cp := ((b - 0xE0).toNat * 4096)
              + ((bs[i+1]! - 0x80).toNat * 64)
              + (bs[i+2]! - 0x80).toNat
      s := s ++ escapeCp cp
      i := i + 3
    else if i + 3 < bs.size then
      let cp := ((b - 0xF0).toNat * 262144)
              + ((bs[i+1]! - 0x80).toNat * 4096)
              + ((bs[i+2]! - 0x80).toNat * 64)
              + (bs[i+3]! - 0x80).toNat
      s := s ++ escapeCp cp
      i := i + 4
    else
      i := i + 1
  pure s

/-- Apply a font CMap (if any) to a PDF text-show operand and produce
    LaTeX-ready text. -/
def stringContentCMap (cmap : Option CMap) (o : PDFObject) : String :=
  match o with
  | PDFObject.str bs _ =>
      let decoded :=
        match cmap with
        | some m => m.applyBytes bs
        | none =>
            -- No CMap: best-effort treat raw bytes as Latin-1.
            Id.run do
              let mut out : ByteArray := ByteArray.empty
              for i in [0:bs.size] do
                let b := bs[i]!
                if b < 0x80 then
                  out := out.push b
                else
                  let n := b.toNat
                  out := out.push (UInt8.ofNat (0xC0 ||| (n >>> 6)))
                  out := out.push (UInt8.ofNat (0x80 ||| (n &&& 0x3F)))
              pure out
      utf8ToLatex decoded
  | _ => ""

/-- Backward-compatible helper used elsewhere. -/
def stringContent (o : PDFObject) : String := stringContentCMap none o

/-- A single emitted text run: (x, y, fontSize, text). -/
structure TextRun where
  x : Float
  y : Float
  fs : Float
  text : String
  deriving Inhabited

/-- Drawing state. -/
structure State where
  ctm    : Mat := Mat.id        -- current transformation matrix
  tm     : Mat := Mat.id        -- text matrix (between BT..ET)
  tlm    : Mat := Mat.id        -- text line matrix
  fontSize : Float := 12
  fontName : String := ""       -- e.g. "F1", "Ty1"
  leading  : Float := 0
  inText   : Bool := false
  /-- Stack for q/Q nesting. -/
  stack    : List Mat := []
  /-- Map from page-local font name → loaded CMap. -/
  fonts    : HashMap String CMap := {}
  /-- Collected text runs (x, y, fontSize, text); flushed at end of page. -/
  runs     : Array TextRun := #[]

instance : Inhabited State := ⟨{}⟩

namespace State

def push (s : State) : State := { s with stack := s.ctm :: s.stack }
def pop  (s : State) : State :=
  match s.stack with
  | [] => s
  | m :: rest => { s with ctm := m, stack := rest }

/-- Emit a text run at the current text-matrix position. -/
def emitText (s : State) (txt : String) : State :=
  if txt.isEmpty then s else
  let m := s.ctm.mul s.tm
  { s with runs := s.runs.push { x := m.e, y := m.f, fs := s.fontSize, text := txt } }

end State

/-- Parse a PDF real string, e.g. "-3.14", ".5", "12.", "+17". -/
def parseReal (s : String) : Float := Id.run do
  let cs := s.toList
  let (sign, rest) :=
    match cs with
    | '-' :: r => (-1.0, r)
    | '+' :: r => (1.0, r)
    | r        => (1.0, r)
  let mut intPart : Float := 0
  let mut fracPart : Float := 0
  let mut fracScale : Float := 1
  let mut sawDot := false
  for c in rest do
    if c = '.' then
      sawDot := true
    else if c.isDigit then
      let d := Float.ofNat (c.toNat - '0'.toNat)
      if sawDot then
        fracScale := fracScale * 10
        fracPart := fracPart + d / fracScale
      else
        intPart := intPart * 10 + d
  return sign * (intPart + fracPart)

/-- Convert a PDFObject operand to Float. -/
def toFloat? (o : PDFObject) : Option Float :=
  match o with
  | PDFObject.int n  => some (Float.ofInt n)
  | PDFObject.real s => some (parseReal s)
  | _                => none

def toFloatD (o : PDFObject) (d : Float := 0) : Float :=
  (toFloat? o).getD d

/-- Run a single content-stream operator against the state. -/
partial def stepOp (s : State) (op : Op) : State :=
  let A := op.operands
  match op.name with
  -- Graphics state
  | "q"  => s.push
  | "Q"  => s.pop
  | "cm" =>
      if A.size = 6 then
        let m : Mat :=
          { a := toFloatD A[0]!, b := toFloatD A[1]!
          , c := toFloatD A[2]!, d := toFloatD A[3]!
          , e := toFloatD A[4]!, f := toFloatD A[5]! }
        { s with ctm := s.ctm.mul m }
      else s
  -- Text state
  | "BT" => { s with inText := true,  tm := Mat.id, tlm := Mat.id }
  | "ET" => { s with inText := false }
  | "Tf" =>
      let nm := match A[0]? with
        | some (PDFObject.name bs) => String.fromUTF8! bs
        | _ => s.fontName
      let sz := if A.size ≥ 2 then toFloatD A[1]! else s.fontSize
      { s with fontName := nm, fontSize := sz }
  | "TL" =>
      if A.size ≥ 1 then { s with leading := toFloatD A[0]! }
      else s
  -- Text positioning
  | "Td" =>
      if A.size = 2 then
        let tx := toFloatD A[0]!; let ty := toFloatD A[1]!
        let mv : Mat := { e := tx, f := ty }
        let tlm' := mv.mul s.tlm
        { s with tlm := tlm', tm := tlm' }
      else s
  | "TD" =>
      if A.size = 2 then
        let tx := toFloatD A[0]!; let ty := toFloatD A[1]!
        let mv : Mat := { e := tx, f := ty }
        let tlm' := mv.mul s.tlm
        { s with leading := -ty, tlm := tlm', tm := tlm' }
      else s
  | "Tm" =>
      if A.size = 6 then
        let m : Mat :=
          { a := toFloatD A[0]!, b := toFloatD A[1]!
          , c := toFloatD A[2]!, d := toFloatD A[3]!
          , e := toFloatD A[4]!, f := toFloatD A[5]! }
        { s with tm := m, tlm := m }
      else s
  | "T*" =>
      let mv : Mat := { e := 0, f := -s.leading }
      let tlm' := mv.mul s.tlm
      { s with tlm := tlm', tm := tlm' }
  -- Text showing
  | "Tj" =>
      let cmap := s.fonts[s.fontName]?
      if A.size = 1 then s.emitText (stringContentCMap cmap A[0]!) else s
  | "'"  =>
      let s := stepOp s { name := "T*", operands := #[] }
      let cmap := s.fonts[s.fontName]?
      if A.size = 1 then s.emitText (stringContentCMap cmap A[0]!) else s
  | "\"" =>
      let s := if A.size = 3 then
                { s with leading := toFloatD A[1]! }
               else s
      let s := stepOp s { name := "T*", operands := #[] }
      let cmap := s.fonts[s.fontName]?
      if A.size = 3 then s.emitText (stringContentCMap cmap A[2]!) else s
  | "TJ" =>
      let cmap := s.fonts[s.fontName]?
      if A.size = 1 then
        match A[0]! with
        | PDFObject.array xs =>
            let acc : String := Id.run do
              let mut a := ""
              for o in xs do
                match o with
                | PDFObject.str _ _ => a := a ++ stringContentCMap cmap o
                | PDFObject.int n   => if n ≤ -100 then a := a ++ " "
                | PDFObject.real r  =>
                    if parseReal r ≤ -100.0 then a := a ++ " "
                | _ => pure ()
              pure a
            s.emitText acc
        | _ => s
      else s
  | _ => s   -- ignore everything else

/-- Reduce a list of ops into final state. -/
def runOps (initCtm : Mat) (fonts : HashMap String CMap)
    (ops : Array Op) : State := Id.run do
  let mut s : State := { ctm := initCtm, fonts := fonts }
  for op in ops do
    s := stepOp s op
  return s

/-- Convert a Unicode codepoint that is meant to *be* an accent into the
    matching combining mark.  Used to fold standalone accent glyphs (which
    TeX engines emit as separate spacing chars positioned over a base
    letter) into proper combining sequences. -/
def toCombining (cp : Nat) : Option Nat :=
  match cp with
  | 0x0060 | 0x02CB => some 0x0300        -- grave
  | 0x00B4 | 0x02CA => some 0x0301        -- acute
  | 0x005E | 0x02C6 => some 0x0302        -- circumflex
  | 0x007E | 0x02DC => some 0x0303        -- tilde
  | 0x00AF | 0x02C9 => some 0x0304        -- macron
  | 0x02D8          => some 0x0306        -- breve
  | 0x02D9          => some 0x0307        -- dot above
  | 0x00A8          => some 0x0308        -- diaeresis
  | 0x02DA          => some 0x030A        -- ring above
  | 0x02DD          => some 0x030B        -- double acute
  | 0x02C7          => some 0x030C        -- caron
  | 0x00B8          => some 0x0327        -- cedilla
  | _ => none

/-- Wrap a single codepoint as a Lean `String`.  Lean serialises strings as
    UTF-8 automatically, so we do **not** decompose into bytes here. -/
private def cpToUtf8 (cp : Nat) : String :=
  if cp = 0 then "" else String.singleton (Char.ofNat cp)

/-- Return the first Unicode codepoint of `s`, or 0 if empty. -/
def firstCp (s : String) : Nat :=
  match s.toList with
  | []     => 0
  | c :: _ => c.toNat

/-- A run is "an accent" if it contains exactly one codepoint that maps
    to a combining mark via `toCombining`. -/
def isAccentRun (s : String) : Option Nat :=
  if s.length = 0 then none
  else
    let cp := firstCp s
    let len := (cpToUtf8 cp).length
    if len = s.length then toCombining cp else none

/-- Lookup table: (base codepoint, combining mark) → precomposed codepoint.
    Covers all ISO Latin-1 + the most common Latin Extended-A diacritics. -/
def precomposed (base : Nat) (mark : Nat) : Nat :=
  -- grave
  if mark = 0x300 then
    match base with
    | 0x41 => 0xC0 | 0x45 => 0xC8 | 0x49 => 0xCC | 0x4F => 0xD2 | 0x55 => 0xD9
    | 0x61 => 0xE0 | 0x65 => 0xE8 | 0x69 => 0xEC | 0x6F => 0xF2 | 0x75 => 0xF9
    | _ => 0
  -- acute
  else if mark = 0x301 then
    match base with
    | 0x41 => 0xC1 | 0x45 => 0xC9 | 0x49 => 0xCD | 0x4F => 0xD3 | 0x55 => 0xDA | 0x59 => 0xDD
    | 0x61 => 0xE1 | 0x65 => 0xE9 | 0x69 => 0xED | 0x6F => 0xF3 | 0x75 => 0xFA | 0x79 => 0xFD
    | 0x43 => 0x106 | 0x63 => 0x107 | 0x4E => 0x143 | 0x6E => 0x144
    | _ => 0
  -- circumflex
  else if mark = 0x302 then
    match base with
    | 0x41 => 0xC2 | 0x45 => 0xCA | 0x49 => 0xCE | 0x4F => 0xD4 | 0x55 => 0xDB
    | 0x61 => 0xE2 | 0x65 => 0xEA | 0x69 => 0xEE | 0x6F => 0xF4 | 0x75 => 0xFB
    | _ => 0
  -- tilde
  else if mark = 0x303 then
    match base with
    | 0x41 => 0xC3 | 0x4E => 0xD1 | 0x4F => 0xD5
    | 0x61 => 0xE3 | 0x6E => 0xF1 | 0x6F => 0xF5
    | _ => 0
  -- diaeresis
  else if mark = 0x308 then
    match base with
    | 0x41 => 0xC4 | 0x45 => 0xCB | 0x49 => 0xCF | 0x4F => 0xD6 | 0x55 => 0xDC | 0x59 => 0x178
    | 0x61 => 0xE4 | 0x65 => 0xEB | 0x69 => 0xEF | 0x6F => 0xF6 | 0x75 => 0xFC | 0x79 => 0xFF
    | _ => 0
  -- caron
  else if mark = 0x30C then
    match base with
    | 0x53 => 0x160 | 0x73 => 0x161 | 0x5A => 0x17D | 0x7A => 0x17E
    | 0x43 => 0x10C | 0x63 => 0x10D | 0x4E => 0x147 | 0x6E => 0x148
    | _ => 0
  -- ring
  else if mark = 0x30A then
    match base with
    | 0x41 => 0xC5 | 0x61 => 0xE5
    | _ => 0
  -- cedilla
  else if mark = 0x327 then
    match base with
    | 0x43 => 0xC7 | 0x63 => 0xE7
    | _ => 0
  -- macron
  else if mark = 0x304 then
    match base with
    | 0x41 => 0x100 | 0x45 => 0x112 | 0x49 => 0x12A | 0x4F => 0x14C | 0x55 => 0x16A
    | 0x61 => 0x101 | 0x65 => 0x113 | 0x69 => 0x12B | 0x6F => 0x14D | 0x75 => 0x16B
    | _ => 0
  else 0

/-- Combine `base` (a single base char) with combining `mark`.  Returns
    a precomposed char string when one exists; otherwise emits base+mark.
    The result is meant to be safely typeset by `[utf8]{inputenc}`. -/
def composeChar (base : Nat) (mark : Nat) : String :=
  let p := precomposed base mark
  if p ≠ 0 then cpToUtf8 p
  else cpToUtf8 base ++ cpToUtf8 mark

/-- Merge adjacent runs that overlap on the page, folding standalone
    accents into precomposed characters where possible.  Heuristic:
    runs merge if baselines match within 0.5 pt and the x-gap is below
    1.5 × the larger font size. -/
def mergeRuns (rs : Array TextRun) : Array TextRun := Id.run do
  if rs.size = 0 then return rs
  let mut out : Array TextRun := #[]
  let mut cur : TextRun := rs[0]!
  for k in [1:rs.size] do
    let nx := rs[k]!
    let dy := (cur.y - nx.y).abs
    let dx := (nx.x - cur.x).abs
    let ll := if cur.fs > nx.fs then cur.fs else nx.fs
    let close := dy < 0.5 ∧ dx < ll
    if close then
      match isAccentRun cur.text, isAccentRun nx.text with
      | some accCp, _ =>
          -- previous = accent, next starts with base letter
          let baseFirst := firstCp nx.text
          let rest := (nx.text.drop 1).toString
          let merged := composeChar baseFirst accCp ++ rest
          cur := { cur with x := nx.x, text := merged }
      | _, some accCp =>
          -- next = accent over the *last* char of cur
          if cur.text.length = 0 then
            cur := { cur with text := cpToUtf8 accCp }
          else
            let baseChar : Nat :=
              (match (cur.text.toList).reverse with
               | c :: _ => c.toNat
               | _      => 0)
            let pre := cur.text.dropRight 1
            let merged := pre ++ composeChar baseChar accCp
            cur := { cur with text := merged }
      | _, _ =>
          cur := { cur with text := cur.text ++ nx.text }
    else
      out := out.push cur
      cur := nx
  out := out.push cur
  return out

/-- Build a 256-entry default encoding (WinAnsi, MacRoman, Standard, …).
    For now we treat all named encodings as WinAnsi-like, since most PDFs
    that bother naming their encoding use one of the Latin-1 variants. -/
def baseEncodingCMap (name : String) : CMap := Id.run do
  let mut t : HashMap Nat ByteArray := {}
  -- ASCII subset: identity
  for c in [0x20:0x7F] do
    t := t.insert c (ByteArray.empty.push (UInt8.ofNat c))
  -- Latin-1 supplement (works for WinAnsi mostly): A0..FF
  if name = "WinAnsiEncoding" ∨ name = "MacRomanEncoding"
     ∨ name = "StandardEncoding" ∨ name.isEmpty then
    for c in [0xA0:0x100] do
      let cp := if name = "MacRomanEncoding" then c else c
      t := t.insert c (utf8Bytes cp)
  pure { codeBytes := 1, table := t }

/-- Translate a glyph name to a UTF-8 byte sequence.  Empty if unknown. -/
def glyphNameToBytes (name : String) : ByteArray :=
  let cp := aglToUnicode name
  if cp = 0 then ByteArray.empty else utf8Bytes cp

/-- Build a CMap from a font's `/Encoding` dictionary, applying any
    `/Differences` overrides on top of the base encoding. -/
def encodingToCMap (enc : PDFObject) : CMap := Id.run do
  -- Determine the base
  let baseName : String :=
    match enc with
    | PDFObject.name n => String.fromUTF8! n
    | _ =>
        match enc.getKey "BaseEncoding" with
        | some (PDFObject.name n) => String.fromUTF8! n
        | _ => "WinAnsiEncoding"
  let mut m := baseEncodingCMap baseName
  -- Apply /Differences if present
  match enc.getKey "Differences" with
  | some (PDFObject.array xs) =>
      let mut code : Nat := 0
      for o in xs do
        match o with
        | PDFObject.int n => if n ≥ 0 then code := n.toNat
        | PDFObject.name nm =>
            let bs := glyphNameToBytes (String.fromUTF8! nm)
            if !bs.isEmpty then
              m := { m with table := m.table.insert code bs }
            code := code + 1
        | _ => pure ()
  | _ => pure ()
  pure m

/-- Load CMaps for every font in a page's Resources dictionary.
    Strategy: prefer `/ToUnicode`; otherwise build one from `/Encoding`. -/
partial def loadFontCMaps (d : Document) (page : PDFObject) :
    Except ParseError (HashMap String CMap × Document) := do
  let (res, d) ←
    match page.getKey "Resources" with
    | some o => d.derefDeep o
    | none   => Except.ok (PDFObject.null, d)
  let (fontDict, d) ←
    match res.getKey "Font" with
    | some o => d.derefDeep o
    | none   => Except.ok (PDFObject.null, d)
  match fontDict.asDict? with
  | none => Except.ok ({}, d)
  | some es =>
      let mut fonts : HashMap String CMap := {}
      let mut d := d
      for (k, v) in es.toList do
        let name := String.fromUTF8! k
        let (font, d') ← d.derefDeep v
        d := d'
        -- Prefer /ToUnicode
        let mut got : Option CMap := none
        match font.getKey "ToUnicode" with
        | some tu =>
            let (tuObj, d') ← d.derefDeep tu
            d := d'
            match tuObj with
            | PDFObject.stream _ raw =>
                got := some (parseCMap raw)
            | _ => pure ()
        | none => pure ()
        -- Fallback: build from /Encoding (always; even if the encoding is
        -- merely a name).  Merge with ToUnicode if both exist.
        match font.getKey "Encoding" with
        | some encRef =>
            let (encObj, d') ← d.derefDeep encRef
            d := d'
            let encMap := encodingToCMap encObj
            let merged : CMap :=
              match got with
              | some m => Id.run do
                  let mut t := encMap.table
                  for (c, b) in m.table.toList do
                    t := t.insert c b
                  pure { codeBytes := max encMap.codeBytes m.codeBytes,
                         table := t }
              | none => encMap
            got := some merged
        | none => pure ()
        match got with
        | some m => fonts := fonts.insert name m
        | none => pure ()
      Except.ok (fonts, d)

/-- Concatenate the bytes of a single stream or an array of stream refs. -/
partial def collectStreams (d : Document) (o : PDFObject) :
    Except ParseError (ByteArray × Document) := do
  match o with
  | PDFObject.stream _ bs => Except.ok (bs, d)
  | PDFObject.array xs =>
      let mut acc : ByteArray := ByteArray.empty
      let mut d := d
      for x in xs do
        let (x', d') ← d.derefDeep x
        d := d'
        let (bs, d') ← collectStreams d x'
        d := d'
        acc := acc ++ bs ++ "\n".toUTF8
      Except.ok (acc, d)
  | _ => Except.ok (ByteArray.empty, d)

/-- Render a single page to TikZ. -/
def renderPage (d : Document) (page : PDFObject)
    : Except ParseError (String × Document) := do
  -- MediaBox: [llx lly urx ury]
  let (mb, d) ←
    match page.getKey "MediaBox" with
    | some o => d.derefDeep o
    | none   => Except.ok (PDFObject.array #[PDFObject.int 0, PDFObject.int 0,
                                              PDFObject.int 612, PDFObject.int 792], d)
  let (llx, lly, urx, ury) :=
    match mb with
    | PDFObject.array xs =>
      if xs.size = 4 then
        (toFloatD xs[0]!, toFloatD xs[1]!, toFloatD xs[2]!, toFloatD xs[3]!)
      else (0.0, 0.0, 612.0, 792.0)
    | _ => (0.0, 0.0, 612.0, 792.0)
  -- /Contents may be a stream or array of streams
  let (contents, d) ←
    match page.getKey "Contents" with
    | some o => d.derefDeep o
    | none   => Except.ok (PDFObject.null, d)
  let (raw, d) ← collectStreams d contents
  let (fonts, d) ← loadFontCMaps d page
  let ops := parseContent raw
  let st := runOps Mat.id fonts ops
  let merged := mergeRuns st.runs
  -- Emit a tikzpicture with one \node per merged run
  let header := s!"% --- page ---\n\\begin\{tikzpicture}[x=1pt,y=1pt]\n\\useasboundingbox ({llx},{lly}) rectangle ({urx},{ury});"
  let body := String.intercalate "\n" (merged.toList.map fun r =>
    s!"\\node[anchor=base west, inner sep=0pt, font=\\fontsize\{{r.fs}}\{{r.fs * 1.2}}\\selectfont] at ({r.x}pt,{r.y}pt) \{{r.text}};")
  let footer := "\\end{tikzpicture}\n\\clearpage\n"
  return (header ++ "\n" ++ body ++ "\n" ++ footer, d)

/-- Render a whole document to a LaTeX string. -/
def renderDocument (d : Document) : Except ParseError String := do
  let (pgs, d) ← d.pages
  let mut out := preamble
  let mut d := d
  for p in pgs do
    let (s, d') ← renderPage d p
    out := out ++ s
    d := d'
  out := out ++ closing
  return out
where
  preamble : String :=
"\\documentclass[a4paper]{article}\n\
\\usepackage[utf8]{inputenc}\n\
\\usepackage[T1]{fontenc}\n\
\\usepackage{lmodern}\n\
\\usepackage{textcomp}\n\
\\usepackage{tikz}\n\
\\usepackage[margin=0pt,paperwidth=612pt,paperheight=792pt]{geometry}\n\
\\setlength{\\parindent}{0pt}\n\
\\pagestyle{empty}\n\
\\begin{document}\n"
  closing : String := "\\end{document}\n"

end PdfLean
