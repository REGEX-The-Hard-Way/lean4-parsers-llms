# Plan: A PDF 1.7 Parser in Lean 4

This is a concrete, implementation-ready blueprint for replicating the EBNF
grammar in `02_grammar.ebnf` as a Lean 4 library. It is organised in nine
phases, each producing a self-contained, testable module.

The plan deliberately avoids Lean's `Parsec`/`Lean.Parser` framework: PDF
needs random access into a *byte* buffer (not a `String`/UTF-8 stream) and a
custom monad fits better. The whole library should compile under stock
`lake new pdf-lean4 lib`.

---

## 0. Project layout

```
pdf-lean4/
├── lakefile.lean
├── lean-toolchain               -- pin a known-good Lean 4 release
├── Pdf.lean                     -- top-level re-export
└── Pdf/
    ├── Bytes.lean               -- ByteArray helpers, big-endian decoding
    ├── Lex.lean                 -- character classes + low-level reader
    ├── Tokens.lean              -- Token type & tokenizer
    ├── Ast.lean                 -- PDFObject ADT
    ├── Object.lean              -- direct-object parser
    ├── Stream.lean              -- stream extent + filter pipeline interface
    ├── Xref.lean                -- xref table & xref stream loader
    ├── Document.lean            -- end-to-end Document type
    ├── Filters/
    │   ├── ASCIIHex.lean
    │   ├── ASCII85.lean
    │   ├── Flate.lean           -- via FFI to zlib (or pure-Lean later)
    │   ├── LZW.lean
    │   ├── RunLength.lean
    │   └── Predictor.lean
    └── Content.lean             -- content-stream operator parser
Tests/
    └── …                        -- LTest test cases + corpus
```

---

## 1. Phase 1 — Byte foundation (`Pdf/Bytes.lean`)

Define a tiny zero-cost wrapper around `ByteArray` that owns a slice and a
cursor.

```lean
structure Reader where
  data    : ByteArray
  pos     : Nat := 0
  /-- inclusive end (exclusive form is `data.size` clamped) -/

abbrev R (α) := EStateM ParseError Reader α
```

Functions to implement:

| Function                                | Purpose                       |
|-----------------------------------------|-------------------------------|
| `Reader.peek?`, `Reader.peekAt? n`      | look-ahead without advancing  |
| `Reader.advance n`, `Reader.skip pred`  | move cursor                   |
| `Reader.takeWhile pred : R ByteArray`   | longest run                   |
| `Reader.expectByte b`, `expectBytes bs` | hard match                    |
| `Reader.atEOF`, `Reader.size`           | end checks                    |
| `Reader.beU8/16/24/32`                  | big-endian field decode for XRef streams |

Define `ParseError := { pos : Nat, msg : String }`.

**Tests:** unit tests for each helper on hand-rolled `ByteArray.mk #[…]`.

---

## 2. Phase 2 — Lexical primitives (`Pdf/Lex.lean`)

Translate § 7.2 character classes into total predicates:

```lean
def isWhite (b : UInt8) : Bool :=
  b = 0 || b = 9 || b = 10 || b = 12 || b = 13 || b = 32

def isDelim (b : UInt8) : Bool :=
  b == '('.toUInt8 || b == ')'.toUInt8 || b == '<'.toUInt8 ||
  b == '>'.toUInt8 || b == '['.toUInt8 || b == ']'.toUInt8 ||
  b == '{'.toUInt8 || b == '}'.toUInt8 || b == '/'.toUInt8 ||
  b == '%'.toUInt8

def isRegular (b : UInt8) : Bool := !(isWhite b) && !(isDelim b)
```

Then:

* `skipWhiteAndComments : R Unit` — collapses every § 7.2.3 comment to a
  single whitespace except for the *header* and *trailer* sentinels.
* `readEOL : R Unit` — accepts `CRLF`, `LF`, or `CR` (in that priority).
* `readEOLStrict : R Unit` — for `stream` keyword; rejects lone `CR`.

This is the lone module that knows about ASCII byte values; everything above
is byte-agnostic.

---

## 3. Phase 3 — Token type & tokenizer (`Pdf/Tokens.lean`)

```lean
inductive Token where
  | bool      (b : Bool)
  | null
  | int       (n : Int)
  | real      (n : Float)
  | litStr    (bs : ByteArray)
  | hexStr    (bs : ByteArray)
  | name      (bs : ByteArray)            -- decoded (no leading /)
  | arrOpen | arrClose
  | dictOpen | dictClose                  -- << >>
  | kw        (s : String)                -- true/false/null are NOT here
  | eof
  deriving Repr, Inhabited
```

`nextToken : R Token` is a deterministic recursive-descent function:

1. `skipWhiteAndComments`
2. peek the first byte; dispatch on the table

| First byte | Action                                                |
|------------|-------------------------------------------------------|
| `(`        | call `readLiteralString`                              |
| `<`        | if next is `<` → `dictOpen`, else `readHexString`     |
| `>`        | must be `>>` → `dictClose`                            |
| `[` / `]`  | `arrOpen` / `arrClose`                                |
| `/`        | `readName`                                            |
| `+ - .` or digit | `readNumber` (also catches negative `-.5`)      |
| else       | `readKeyword` (longest run of regular chars); map     |
|            | `true`/`false`/`null` to dedicated tokens, otherwise  |
|            | yield `kw`                                            |

`readLiteralString` implements all of § 7.3.4.2: paren depth counting,
backslash escapes, octal escapes (1–3 digits with the spec's "next-char
disambiguation" rule), line continuation, and EOL normalisation.

`readHexString` ignores embedded whitespace and pads odd nibble count.

`readName` decodes `#xx` and rejects NUL.

**Test corpus:** a small `.txt` of annotated examples drawn directly from
the spec (the EXAMPLE blocks in § 7.3.\*); each token's expected
representation is a Lean literal, run via a `#guard` block.

---

## 4. Phase 4 — Object AST (`Pdf/Ast.lean`)

```lean
mutual
  inductive PDFObject where
    | null
    | bool   (b : Bool)
    | int    (n : Int)
    | real   (x : Float)
    | str    (bs : ByteArray) (kind : StringKind)
    | name   (bs : ByteArray)
    | array  (xs : Array PDFObject)
    | dict   (entries : Array (ByteArray × PDFObject))    -- preserve order
    | stream (dict : PDFObject) (raw : ByteArray)
    | ref    (objNum : Nat) (gen : Nat)
    deriving Inhabited

  inductive StringKind | literal | hex
end
```

Helpers: `getKey`, `getName`, `getInt`, `asArray`, `asDict`, plus a
`Repr`/`ToJson` instance for debugging.

> *Why an `Array (ByteArray × PDFObject)` rather than a `HashMap`?*
> The spec forbids duplicate keys, but real-world PDFs have them; we keep
> insertion order to be debuggable and let a higher layer dedupe.

---

## 5. Phase 5 — Direct-object parser (`Pdf/Object.lean`)

```lean
partial def parseObject : R PDFObject
```

Recursive descent on `Token`. Two subtleties:

* When `nextToken` yields an `int` followed by another `int` followed by the
  keyword `R`, fold them into `PDFObject.ref`. Use a *speculative* read with
  rollback (save `Reader.pos`).
* `parseDict` calls `parseObject` for values; if the value is `null`, drop
  the entry (§ 7.3.7).

Cycle detection is **not** done here — it belongs to the resolver in Phase 8.

---

## 6. Phase 6 — Stream extent (`Pdf/Stream.lean`)

`parseStreamBody (dict : PDFObject) : R PDFObject` is invoked when the
indirect-object body starts with a dictionary and the next keyword is
`stream`:

1. Consume `stream` and a *strict* EOL (LF or CRLF, never lone CR).
2. Read `Length` from the dict.
   * If `Length` is an `int` literal → take exactly that many bytes.
   * If it is an indirect reference → record the start offset, **scan
     forward** for the literal pattern `\nendstream`/`\rendstream`/
     `endstream` as a fallback, then verify against `Length` once the xref
     is loaded.
3. Optional EOL.
4. Expect keyword `endstream`.

Filter dispatch lives behind a typeclass:

```lean
class Filter where
  decode : ByteArray → PDFObject → Except String ByteArray  -- params dict
```

Implementations in `Pdf/Filters/*`. `Flate` initially calls `zlib`
(`uncompress`) via `extern` declarations; pure-Lean Inflate is a follow-up.

---

## 7. Phase 7 — Cross-reference loader (`Pdf/Xref.lean`)

The function `loadXref : ByteArray → Except ParseError XrefTable` does:

1. **Locate `%%EOF`.** Search backwards over the last ≤ 1024 bytes.
2. **Read `startxref`.** Two lines above `%%EOF`.
3. **Branch on what is at offset.**
   * If the byte sequence at `OFFSET` is `xref` → call `parseXrefTable`,
     then `parseTrailerDict`.
   * Otherwise treat it as the start of an indirect object → call
     `parseIndirectObject`, expect a stream with `/Type /XRef`, decode its
     stream, then call `parseXrefStream`.
4. **Follow the `Prev` chain** (table or stream); the *latest* entry for
   each object number wins.
5. If a hybrid `XRefStm` entry exists, merge its entries on top of the
   table's entries.

```lean
inductive XrefEntry
  | free      (next : Nat) (gen : Nat)
  | inUse     (offset : Nat) (gen : Nat)
  | compressed (objStm : Nat) (index : Nat)

structure XrefTable where
  size    : Nat
  entries : Std.HashMap (Nat × Nat) XrefEntry      -- (objnum, gen) → entry
  trailer : PDFObject
```

Strictly validate the 20-byte fixed format of classic entries; for XRef
streams use the `W` widths and the big-endian helpers from Phase 1.

---

## 8. Phase 8 — Document model (`Pdf/Document.lean`)

```lean
structure Document where
  data    : ByteArray
  xref    : XrefTable
  -- lazily filled caches:
  cache   : IO.Ref (Std.HashMap (Nat × Nat) PDFObject)
```

API:

| Function                                  | Behaviour                |
|-------------------------------------------|--------------------------|
| `Document.open (bs : ByteArray) : IO Document` | Load + xref         |
| `Document.fetch (id : Nat × Nat) : IO PDFObject` | Resolve indirect    |
| `Document.deref (o : PDFObject) : IO PDFObject`  | Follow `ref` once   |
| `Document.derefDeep`                              | Recursive (with cycle break) |
| `Document.catalog`, `Document.pages`              | High-level helpers  |

`fetch` consults the cache; on miss it dispatches by entry type:

* **Type 1 (in-use):** `Reader.pos := offset`, parse one indirect object.
* **Type 2 (compressed):** load the object-stream, decode (Flate),
  then read the `(objnum, offset)` table inside its decoded data and parse
  the requested object value.
* **Type 0 (free):** return `PDFObject.null`.

Apply encryption decryption (if `/Encrypt` is present) on fetched strings
and stream bytes — gated behind a Phase-9 module if implemented later.

---

## 9. Phase 9 — Content streams (`Pdf/Content.lean`)

```lean
inductive ContentItem
  | op          (operator : String) (operands : Array PDFObject)
  | inlineImage (dict : PDFObject) (data : ByteArray)
```

Two-state machine:

* **Operand state:** call `parseObject`; push onto an operand buffer.
* **Operator state:** when `nextToken` returns `kw s`, emit
  `ContentItem.op s (operands.toArray)`, clear buffer.
* `BI` switches into a small inline-image dictionary parser, then
  `ID`, then byte-scan until the literal `EI` preceded by whitespace.

The set of legal operators is `Annex A` (≈ 73 operators); a `String → Bool`
membership test gives a useful error when an unknown operator appears
outside of `BX … EX` brackets.

---

## 10. Testing strategy

1. **Spec-derived unit tests.** Every `EXAMPLE` block in § 7.3–7.5 becomes
   a `#guard` test (lex, parse, round-trip).
2. **Conformance corpora.** Run against:
   * `veraPDF` corpus  (https://github.com/veraPDF/veraPDF-corpus)
   * `pdf.js` corpus   (a small subset of well-known fixtures)
   * Hand-crafted edge cases: lone-CR EOL, `\` line continuation, `#xx`
     names, hybrid xref files, encrypted files (skip if no decrypt impl).
3. **Property tests.** Use `Plausible`/`SlimCheck`:
   * `parse ∘ pretty = id` for `PDFObject` (exclude streams, references).
   * Permuting whitespace inside dicts/arrays does not change the AST.
4. **Random fuzzing.** A 1-MB random `ByteArray` should never `panic`; only
   `Except` errors are allowed.

---

## 11. Milestones & estimates

| Phase | Module(s)                  | Effort  | Verifies                    |
|------:|----------------------------|---------|-----------------------------|
| 1     | `Bytes`                    | 0.5 d   | byte helpers compile & test |
| 2-3   | `Lex`, `Tokens`            | 2 d     | `EXAMPLE`s tokenise         |
| 4-5   | `Ast`, `Object`            | 1 d     | parses every example dict   |
| 6     | `Stream`                   | 1 d     | round-trip stream w/ Length |
| 7     | `Xref` (table + stream)    | 2 d     | reads its own output PDF    |
| 8     | `Document` resolver        | 1 d     | Catalog/Pages walk works    |
| F1    | `Filters/Flate` (zlib FFI) | 0.5 d   | decompress sample stream    |
| F2    | `Filters/*` rest           | 1 d     | corpus passes               |
| 9     | `Content`                  | 1 d     | parses real page streams    |
|       | **Total**                  | **~10 days** | end-to-end usable    |

---

## 12. Out of scope (initial release)

- Encryption (RC4/AES); shape the API to make this addable as a
  decoration on `Document.fetch`.
- Linearized-PDF fast path (Annex F).
- Rendering / glyph extraction (Chapters 8–9 of the spec).
- Writing/encoding PDFs (this is a parser, not a serializer).

These can each be tackled as independent follow-up phases without
touching the parser core.

---

## 13. Why Lean 4

- **Total functions + termination checks.** PDF parsers are notorious for
  infinite loops on hostile inputs; Lean's `partial`/`decreasing_by`
  discipline forces every recursive descent to be justified.
- **`ByteArray` is a primitive.** Direct memory access without UTF-8 hazards.
- **Proof potential.** The token grammar above (Phases 2–5) is small enough
  that, after the executable parser ships, one can return and prove
  `parseObject_pretty_round_trip` and `xrefTable_unique_keys` as theorems
  without rewriting the implementation.
