# Deep Analysis of PDF Syntax (ISO 32000-1:2008 / PDF 1.7)

Source: `pdf32000_2008.pdf` (Adobe-published, 756 pages, identical to ISO 32000-1:2008).
Sections studied: **Chapter 7 — Syntax**, sub-clauses 7.2–7.5, 7.8.2.

The PDF spec does not present a formal grammar. It mixes prose, tables, and examples.
This document distills it into a precise, token-level account ready for an EBNF and a
Lean 4 parser.

---

## 1. Overall Structure

A *basic* PDF file (Figure 2 of the spec) has four ordered parts:

```diagram
╭───────────────────╮
│ %PDF-1.N          │  Header           (line 1)
│ %binary marker?   │
├───────────────────┤
│ Indirect objects  │  Body
│ (incl. streams,   │
│  object streams)  │
├───────────────────┤
│ xref table        │  Cross-reference  (or replaced by an XRef stream in ≥1.5)
├───────────────────┤
│ trailer << … >>   │  Trailer
│ startxref N       │
│ %%EOF             │
╰───────────────────╯
```

An *incrementally updated* file is the original file followed by zero or more
appended (Body, XRef, Trailer) triples, each ending in `%%EOF`. Each new
trailer must include a `Prev` entry pointing at the previous xref offset.

A *PDF 1.5+ pure cross-reference-stream* file replaces the `xref` table and
`trailer` keywords entirely with an indirect XRef stream object; only the
`startxref OFF / %%EOF` segment remains as a fixed marker.

A *hybrid* file (7.5.8.4) is a 1.4-style file augmented with an `XRefStm` entry
in the trailer pointing at a compressed XRef stream (so that older readers see
the legacy table while modern readers use the stream).

> **Key implication for parsing.** Because a writer may have produced any of
> these layouts, a real parser cannot scan top-to-bottom. The PDF spec
> mandates *bottom-up* parsing: locate `%%EOF`, read backwards to `startxref`,
> jump to the cross-reference, then random-access objects.

---

## 2. Lexical Layer (§ 7.2)

### 2.1 Character classes

| Class       | Bytes (hex)                                 |
|-------------|----------------------------------------------|
| White-space | 00, 09, 0A, 0C, 0D, 20                       |
| Delimiter   | 28 ( , 29 ) , 3C < , 3E > , 5B [ , 5D ] , 7B { , 7D } , 2F / , 25 % |
| Regular     | every other byte (incl. ≥ 0x80)              |

End-of-line marker is `CR`, `LF`, or `CR LF`. The pair counts as **one** EOL.
Any whitespace run collapses to a single separator *outside* strings/streams/comments.

### 2.2 Comments

`%` to (but not including) the next EOL. Treated as a single white-space.
Two comments are *semantic*:
- `%PDF–1.N` (header)
- `%%EOF` (trailer terminator)

### 2.3 Tokens

A token is one of: a **delimiter group** (`(`, `)`, `<`, `>`, `<<`, `>>`, `[`,
`]`, `{`, `}`, `/`-prefixed name, comment), a **literal string**, a
**hexadecimal string**, a **number**, or a **keyword** (longest run of
non-delimiter, non-whitespace bytes that is not a number — e.g. `true`,
`false`, `null`, `obj`, `endobj`, `R`, `stream`, `endstream`, `xref`,
`trailer`, `startxref`, `n`, `f`).

Note: `<` followed by `<` forms `<<` (dict open), otherwise it begins a hex
string — so the lexer needs a 1-byte lookahead. Same for `>>` vs lone `>`.

### 2.4 Numbers

- Integer: `[+-]?[0-9]+`
- Real:    `[+-]?( [0-9]+ \. [0-9]* | \. [0-9]+ | [0-9]+ \.)`
- No exponent, no non-decimal radices (Note 1 of § 7.3.3).

### 2.5 Strings

**Literal** `( … )`:
- Balanced parentheses allowed unescaped.
- Escapes: `\n \r \t \b \f \( \) \\ \ddd` (1–3 octal digits, high bits ignored).
- `\` at end of line is a *continuation* (drop both).
- Lone CR, LF, or CR LF inside string normalizes to a single LF byte.

**Hex** `< … >`:
- ASCII hex digits, whitespace ignored.
- Odd digit count: append a trailing `0`.

### 2.6 Names

`/` then a sequence of regular characters. `#xx` introduces any byte (must be
used for chars outside `!`..`~`, for `#` itself, and for white space).
The name `/` (empty) is valid. NUL (0) is not allowed in a decoded name.

---

## 3. Object Layer (§ 7.3)

Eight primitive types: `Boolean`, `Integer`, `Real`, `String`, `Name`,
`Array`, `Dictionary`, `Stream`, plus `Null`. (The spec calls it eight, but
counts integer+real together.)

- **Array**: `[` *object*\* `]`.
- **Dictionary**: `<<` (`Name` *object*)\* `>>`. Keys must be names; duplicate
  keys disallowed; a value of `null` is equivalent to omitting the entry.
- **Stream**: a *direct* dictionary, then keyword `stream`, then EOL (`LF` or
  `CR LF` — *never* a lone `CR`), then exactly `Length` bytes of raw data,
  then optional EOL, then keyword `endstream`. Streams must be **indirect**
  (only appear as the value inside `obj … endobj`).
- **Indirect object**: `OBJNUM GENNUM obj` *object* `endobj` where
  `OBJNUM ≥ 1`, `GENNUM ≥ 0`.
- **Indirect reference**: `OBJNUM GENNUM R`.
- **Null**: keyword `null`. A reference to a non-existent object also
  resolves to `null`.

The object grammar is *context-free* but resolution of references and stream
length is *semantic* (requires the xref table).

---

## 4. File Structure (§ 7.5)

### 4.1 Header (§ 7.5.2)

```
%PDF-1.N\n          where N ∈ {0..7}
[%XXXX\n]?          optional binary marker; 4 or more bytes ≥ 0x80
```

### 4.2 Body (§ 7.5.3)

A sequence of indirect-object definitions, including object streams (1.5+).

### 4.3 Cross-reference table (§ 7.5.4)

```
xref\n
SUB+
```

A subsection is:
```
FIRST COUNT\n
ENTRY×COUNT
```

Each entry is *exactly 20 bytes*, fixed format:

- in-use:  `nnnnnnnnnn ggggg n EOL2`
- free:    `nnnnnnnnnn ggggg f EOL2`

`EOL2` is 2 bytes — `SP CR`, `SP LF`, or `CR LF`.

The 0-th entry must be free with generation 65535; free entries form a
linked list whose tail links back to 0.

### 4.4 Trailer (§ 7.5.5)

```
trailer
<< … >>
startxref
OFFSET
%%EOF
```

Required dict keys: `Size`, `Root`. Optional: `Prev`, `Encrypt` (req if
encrypted), `Info`, `ID`, `XRefStm` (hybrid).

### 4.5 Incremental updates (§ 7.5.6)

Append (Body′, XRef′, Trailer′) blocks. Each new trailer carries `Prev`.
A reader must follow the `Prev` chain.

### 4.6 Object streams (§ 7.5.7)

A stream of `/Type /ObjStm` whose data starts with `N` `(objnum, offset)`
integer pairs (white-space separated), followed at byte position `First`
by `N` concatenated object values (no `obj`/`endobj`). All compressed
objects have generation 0.

### 4.7 Cross-reference streams (§ 7.5.8)

A stream of `/Type /XRef` whose dictionary merges the keys of Table 5
(stream), Table 15 (trailer), and Table 17 (`Index`, `W`, optional `Prev`).

Each entry has up to 3 fields whose widths are given by the `W` array
(big-endian). Entry types:

| Type | Field 2                              | Field 3                                   |
|------|--------------------------------------|-------------------------------------------|
| 0    | next free object number              | next-use generation                       |
| 1    | byte offset of object                | generation                                |
| 2    | containing object-stream object num  | index within the object stream            |

A field width of 0 means "use default" (e.g. type defaults to 1).

---

## 5. Content Streams (§ 7.8.2)

A content stream is a decoded stream interpreted with the same lexical
rules. Tokens are operands (any direct object, no streams, no indirect
refs) followed by a *keyword operator* (a name without leading `/`, e.g.
`m`, `l`, `re`, `f`, `B`, `Tj`, `BT`, `ET`, `BX`, `EX`, …). Operators are
postfix; there is no operand stack across instructions. Some operators
(notably the inline-image group `BI … ID … EI`) carry their own embedded
data and need special lexical handling.

---

## 6. Practical Notes for a Parser

- The spec is permissive: extra whitespace is fine, missing trailing EOLs
  before `endstream` are common, files in the wild violate the 255-char
  line limit, etc. A real parser must be tolerant.
- `Length` in a stream dictionary may itself be an indirect reference, so
  the stream extent may not be known until after the xref is resolved.
  Production parsers handle this by either (a) two-pass parsing or (b)
  scanning forward for `endstream` as a fallback.
- Encrypted documents (§ 7.6) require decrypting strings and stream bytes
  *after* tokenization but *before* interpretation. The lexer is unaffected.
- `startxref` may point at a normal `xref` keyword *or* at the start of an
  XRef-stream indirect object; the reader must dispatch on what it finds.
- Files frequently have garbage before the `%PDF` header; spec-conformant
  readers are encouraged to scan up to the first `%PDF-` within the first
  1024 bytes.
