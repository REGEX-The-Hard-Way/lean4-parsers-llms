# pdf_lean — A PDF parser in Lean 4 with a LaTeX back-end

A from-scratch implementation of the parser specified in
[`../02_grammar.ebnf`](../02_grammar.ebnf), following the deep analysis
in [`../01_analysis.md`](../01_analysis.md).  It can:

1. tokenise and parse the byte stream of a PDF (ISO 32000-1:2008 / 1.7),
2. resolve indirect references through both classic xref tables and
   (uncompressed) xref streams, including the `Prev` chain,
3. extract compressed objects from `/Type /ObjStm` object streams,
4. walk the `/Pages` tree and parse content streams, and
5. **emit a `.tex` document that, when compiled with `pdflatex`, re-creates
   the original PDF page-by-page** as a `tikzpicture` of positioned text
   nodes.

The repository deliberately scopes out Flate/LZW decompression and font
CMaps; PDFs must be passed through `mutool clean -d` first so that all
streams are uncompressed.

## Build

```sh
elan toolchain install $(cat lean-toolchain | sed 's|^.*:||')
lake build
```

This produces the executable `.lake/build/bin/pdf2tex`.

## Usage

```sh
# 1. Strip Flate / object-stream compression from the source PDF
mutool clean -d -gggg input.pdf input_dec.pdf

# 2. Convert to LaTeX
./.lake/build/bin/pdf2tex input_dec.pdf out.tex

# 3. Compile back to PDF
pdflatex out.tex
```

## Verified end-to-end demo

```sh
$ pdflatex final.tex
$ mutool clean -d -gggg final.pdf final_dec.pdf
$ pdf2tex final_dec.pdf final_out.tex
loaded; xref entries=75 size=75
wrote final_out.tex (14617 chars)

$ pdflatex final_out.tex
Output written on final_out.pdf (4 pages, 68233 bytes).

$ diff <(pdftotext final.pdf -) <(pdftotext final_out.pdf -)
   ... only differences are non-ASCII glyphs (→, ligatures fi/fl)
       that require a /ToUnicode CMap to recover ...
```

## Module layout

| File                                                            | Phase | Purpose                                  |
|-----------------------------------------------------------------|-------|------------------------------------------|
| [`PdfLean/Bytes.lean`](PdfLean/Bytes.lean)                       | 1     | `ByteArray` reader, BE int decoding      |
| [`PdfLean/Lex.lean`](PdfLean/Lex.lean)                           | 2     | §7.2 character classes, WS + comments    |
| [`PdfLean/Tokens.lean`](PdfLean/Tokens.lean)                     | 3     | tokenizer producing `Token` values       |
| [`PdfLean/Ast.lean`](PdfLean/Ast.lean)                           | 4     | `PDFObject` ADT and helpers              |
| [`PdfLean/Object.lean`](PdfLean/Object.lean)                     | 5     | direct-object recursive-descent parser   |
| [`PdfLean/Stream.lean`](PdfLean/Stream.lean)                     | 6     | indirect-object + stream-extent parser   |
| [`PdfLean/Xref.lean`](PdfLean/Xref.lean)                         | 7     | xref table, xref stream, `Prev` chain    |
| [`PdfLean/Document.lean`](PdfLean/Document.lean)                 | 8     | `Document` model + page tree walk        |
| [`PdfLean/Content.lean`](PdfLean/Content.lean)                   | 9     | content-stream operator parser           |
| [`PdfLean/Latex.lean`](PdfLean/Latex.lean)                       | 9+    | LaTeX/TikZ back-end                      |
| [`Main.lean`](Main.lean)                                         | —     | command-line driver                       |

## Pipeline

```diagram
          input.pdf
              │
              ▼
   ╭──────────────────────╮
   │ mutool clean -d      │  (Flate decompression — external)
   ╰──────────┬───────────╯
              ▼
   ╭──────────────────────╮
   │ Bytes / Lex / Tokens │
   ╰──────────┬───────────╯
              ▼
   ╭──────────────────────╮
   │ Object + Stream      │  → PDFObject AST
   ╰──────────┬───────────╯
              ▼
   ╭──────────────────────╮
   │ Xref + Document      │  → resolved indirect objects
   ╰──────────┬───────────╯
              ▼
   ╭──────────────────────╮
   │ Content              │  → list of (operator, operands)
   ╰──────────┬───────────╯
              ▼
   ╭──────────────────────╮
   │ Latex                │  → tikzpicture of \node at (x,y) {text}
   ╰──────────┬───────────╯
              ▼
          out.tex
```

## Known limitations

* Ligatures (`fi`, `fl`, …) and any character above 0x7E are dropped because
  we don't decode `/ToUnicode` CMaps.  Adding this is the obvious next step.
* Inline graphics (paths, images, colour) are ignored — only text positions
  reach the LaTeX output.
* Encrypted PDFs are not supported.

These can each be slotted into the existing module structure without any
changes to the parser core.
