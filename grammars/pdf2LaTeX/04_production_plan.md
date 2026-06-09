# Production-Hardening Plan for `pdf_lean`

The current parser handles a clean, spec-conformant subset of PDF 1.7 and
emits a serviceable LaTeX rendering of pure-text pages.  Everything below
is what stands between that and a tool that could be pointed at an
arbitrary corpus — invoices, scanned forms, decade-old marketing PDFs,
adversarial inputs — without crashing, hanging, leaking secrets, or
silently dropping content.

The work is grouped by area, with each area sized in person-weeks (1 PW
≈ 40 focused engineering hours) and tagged with whether it is **R**equired
for a v1.0 release, a **N**ice-to-have, or a **L**ong-term goal.

---

## 1. Robustness against real-world PDFs (R, ~6 PW)

PDFs in the wild routinely violate the spec.  A production parser must
recover or fail gracefully, never panic.

### 1.1 Lexer-level tolerance

| Defect                                              | Required behaviour                              |
|------------------------------------------------------|-------------------------------------------------|
| Junk bytes before `%PDF-`                           | Scan first 1024 bytes for the marker.           |
| `%PDF-1.x` missing or malformed                     | Probe header heuristically; warn but proceed.   |
| `%%EOF` not on the last line / followed by garbage  | Search the last 2 KB; pick the *last* `%%EOF`.  |
| `startxref` offset is wrong by a few bytes          | Bracket-search ±64 bytes around the offset.     |
| Stream `/Length` lies                               | Always also forward-scan for `endstream`.       |
| Lone `\r` after `stream` keyword                    | Accept (the spec forbids it; PDFs do it).       |
| `endstream`/`endobj` not preceded by EOL            | Treat as soft delimiters.                       |
| Object IDs reused with wrong generation             | Latest definition wins (already partially done).|
| Truncated files                                     | Best-effort partial parse with diagnostics.     |
| Files with multiple/nested updates whose `Prev` is wrong | Detect cycles, fall back to linear xref scan. |

### 1.2 The "linear scan" fallback

When the cross-reference is corrupt, real readers (Acrobat, Poppler,
MuPDF) do a one-pass scan of the file for `\d+ \d+ obj` patterns and
build the xref themselves.  We need the same.

```lean
def rebuildXrefByScan (data : ByteArray) : XrefTable
```

This single function turns "unparseable" into "messy but useful" for
maybe a third of the broken-PDF corpus.

### 1.3 Per-object error isolation

Today a single bad object aborts the whole file.  Switch to:

```lean
| Object failed to parse → log warning, mark slot as null, continue
| Page failed to render  → emit a placeholder page, continue
```

so that a 3000-page document with one ill-formed image doesn't lose 2999
good pages.

### 1.4 Resource limits

Never trust file-supplied sizes.  Hard caps for:
- decoded stream size (default 256 MB)
- recursion depth in dictionaries / arrays / `Pages` tree (default 256)
- `Prev` chain length (currently 64 — make configurable)
- total objects (default 1 000 000)
- cumulative wall-clock budget (default 60 s)

Every limit must be exposed to the caller and produce a structured warning,
not a silent truncation.

---

## 2. Filters and compression (R, ~3 PW)

The current parser refuses any PDF whose streams are still encoded.

### 2.1 Flate (RFC 1950 + 1951)

The 80% case.  Two viable implementation paths:

* **FFI to zlib** (1 PW, fast).  Add a `Pdf/Filters/FlateFFI.lean`
  with `@[extern "uncompress"]` and link `-lz`.
* **Pure-Lean Inflate** (3 PW, portable).  Self-contained, no native
  dependency, easier to audit.  Performance acceptable up to a few MB/s.

A real release probably ships both behind a flag.

### 2.2 Predictor functions (§7.4.4.4)

`/Predictor 12` (PNG up) appears in nearly every modern PDF
cross-reference stream.  Without it, xref streams from any PDF produced
by Acrobat or Chrome are unreadable.  ~½ PW.

### 2.3 Other filters (~1 PW total)

| Filter            | When you'll meet it                  | Difficulty |
|-------------------|--------------------------------------|------------|
| `ASCIIHexDecode`  | rare, mostly debugging               | trivial    |
| `ASCII85Decode`   | older PostScript-derived PDFs        | trivial    |
| `RunLengthDecode` | bitmap masks                         | trivial    |
| `LZWDecode`       | older Adobe documents                | small      |
| `CCITTFaxDecode`  | scanned monochrome documents         | medium     |
| `DCTDecode`       | JPEG-encoded images (delegate)       | wrap libjpeg |
| `JBIG2Decode`     | scanned books                        | wrap libjbig2 |
| `JPXDecode`       | JPEG 2000 images                     | wrap openjpeg |
| `Crypt`           | per-object encryption (see §3)       | medium     |

Images aren't strictly needed for text extraction, but the *filter chain*
must succeed or we lose the page's content stream.  Stub the image
filters to "return raw" so text-only flows aren't blocked.

---

## 3. Encryption (R for many real-world inputs, ~3 PW)

§7.6 of the spec.  Required to read most corporate PDFs.

* **Standard security handlers V1 (RC4 40-bit), V2 (RC4 128-bit), V4 (RC4/AES-128 per CF), V5 (AES-256, PDF 2.0).**
* **Key derivation:** 7.6.3.3 algorithm 2 (V≤4) and 7.6.4.3 (V5).
* **Permission bits** must be honoured even when we *can* decrypt
  (printing, copy/paste).  This is more legal/UX than technical.
* **Per-string and per-stream decryption** integrated into the lexer
  (strings) and the filter pipeline (streams).
* **Public-key handlers** (PKCS#7) — defer to L.

Implementation pattern: `Document` carries a `securityHandler : Option SecHandler`
populated when `/Encrypt` exists in the trailer.  All `Tokens.litStr`,
`Tokens.hexStr`, and `Stream.parseStreamBody` consult it.

A `--password` CLI flag and an `IO String` callback for interactive
prompts.

---

## 4. Font handling and character mapping (R, ~5 PW)

This is where "pretty good" parsers become "actually usable" parsers.

### 4.1 `/ToUnicode` CMaps (§9.10.3)

A CMap is itself a tiny PostScript-flavoured language.  We need a parser
for `bfchar`, `bfrange`, and `cidchar` blocks.  Without this, every PDF
that uses font subsetting (which is *every* TeX-produced PDF) loses its
ligatures, accented letters, math symbols, and any non-ASCII character.

### 4.2 Predefined encodings (Appendix D)

* `WinAnsiEncoding`, `MacRomanEncoding`, `MacExpertEncoding`,
  `StandardEncoding`, `Symbol`, `ZapfDingbats`.
* The 14 base fonts (Helvetica, Times, Courier × 4 + 2 symbol).

### 4.3 Differences arrays

`/Encoding << /BaseEncoding /WinAnsi /Differences [ 1 /Adieresis … ] >>` —
overrides individual glyph slots.

### 4.4 Font widths and metrics

For accurate text positioning *between* `Tj` calls (not just `TJ`), we
need each glyph's advance width.  This means parsing
`/Widths` arrays in font dictionaries and, for CID fonts, `/W` arrays.

### 4.5 Text reconstruction

Today every `Tj` becomes a separate `\node`.  Production needs:
- Adjacent text runs on the same baseline merged into a single node.
- Inferred word breaks when the cumulative `Tm`/`Td` advance exceeds
  one space-width since the last glyph.
- Reading-order detection (left-to-right, top-to-bottom) for
  multi-column layouts.

This is the dominant differentiator between commercial and open-source
PDF text extractors.

### 4.6 Embedded font programs

For full fidelity (rendering glyphs that don't exist on the user's
machine), we'd need to emit the embedded Type1/Type3/TrueType/CFF font
program with the LaTeX output and reference it via `\usepackage{fontspec}`.
This is L territory.

---

## 5. Graphics (N→L, ~6 PW)

### 5.1 Path operators (§8.5)

`m l c v y re h S s f F f* B b B* b* n W W* …`

For LaTeX output: emit `\draw`, `\fill`, `\clip` TikZ commands.  Most
PDFs use rectangles for table borders and underlines — even partial
support pays off immediately.

### 5.2 Colour (§8.6)

`G g RG rg K k CS cs SC sc SCN scn` plus colour spaces
(DeviceGray/RGB/CMYK, CalRGB, ICCBased, Indexed, Pattern, Separation).
Map to `\definecolor` + TikZ `color=`.

### 5.3 Transparency (§11)

Soft masks, blend modes.  Largely impossible to faithfully replicate in
LaTeX; flatten or skip with a warning.

### 5.4 Images (§8.9)

* **Inline images** (`BI ... ID ... EI`) — extract bytes, write a
  `\includegraphics` referencing a sidecar file.
* **External XObjects** (`Do` operator) — same idea, pulled from the
  resource dictionary.
* Decode through filter chain (DCT → write as `.jpg`, Flate raw → write
  as `.png` via libpng FFI).

### 5.5 Form XObjects, Patterns, Shadings

Composable graphics objects.  Recurse into their content streams and
render inline.

### 5.6 Annotations (§12.5)

Hyperlinks (`/Link`) → `\hyperref`.  Form fields, comments, signatures
mostly drop-or-warn.

---

## 6. Higher-level structure (N, ~3 PW)

### 6.1 Logical content extraction (Tagged PDF, §14.7)

`/StructTreeRoot`, `/MarkedContent`.  When present, gives us paragraphs,
headings, lists, table cells, alt text — exactly the things needed to
emit *real* LaTeX (`\section`, `\itemize`, `tabular`) instead of
absolutely-positioned text nodes.

This is the path from "pixel-perfect placeholder" to "editable LaTeX
document".

### 6.2 Outlines (§12.3.3)

Convert `/Outlines` → `\section`/`\subsection` ToC.

### 6.3 Linearised PDF (Annex F)

Read enough of the linearisation dictionary to skip its quirks; we don't
need to *write* linearised PDFs.

### 6.4 PDF 2.0 (ISO 32000-2:2020)

Same syntax, new dictionary keys, AES-256 with `/V 5`, soft masks in xref
streams, namespaces in tagged PDF.  Mostly additive.

---

## 7. Performance (R, ~2 PW)

The current `Reader` copies a `ByteArray` for every `take` and walks
linearly for every `find?`.  A 100-page PDF with 5000 objects parses in
seconds; a 5000-page PDF will parse in minutes.

### 7.1 Algorithmic

* Boyer–Moore for `find?` / `findLast?`.
* Reuse the `data : ByteArray` slice; never copy bytes during parsing —
  thread `(start, len)` indices instead.
* Memoise resolved objects (already done) but bound the cache so a
  pathological circular reference can't OOM.

### 7.2 Lean-specific

* Compile with `-Dprofile.true=false`; turn on `@[inline]` annotations.
* Use `IO.FS.Handle.read` to stream large files instead of slurping.
* Replace `String` accumulators with `String.Builder` (Lean 4 has one).

### 7.3 Parallelism

Pages are independent once the xref is loaded.  `Task.spawn` per page,
collect TikZ output in order.

Target: 100 MB/s on the lexer, 10 pages/s on full extraction.

---

## 8. Security (R, ~2 PW)

PDFs are an attack surface.

| Threat                                  | Mitigation                                          |
|-----------------------------------------|-----------------------------------------------------|
| Zip bombs in Flate streams              | Cap decoded size; abort with structured error.      |
| Recursion bombs (deeply nested arrays)  | Hard depth cap.                                     |
| Reference cycles                        | Visited-set during deep deref.                      |
| Object-stream `/Length` lies            | Bounds-check every byte access.                     |
| Adversarial filenames in `/F`           | Sandbox / reject path traversal.                    |
| JavaScript actions                      | Never execute; warn and skip.                       |
| Embedded files (`/EmbeddedFile`)        | Extract only on explicit opt-in.                    |
| Encrypted documents with weak passwords | Use constant-time comparisons in key derivation.    |
| Memory-safety (Lean is GC'd, mostly OK) | Audit any `unsafe` / FFI boundary (zlib, libjpeg).  |

A separate **fuzzing harness** (~1 PW): wrap `pdf2tex` with `afl++` or
Honggfuzz, run for a CPU-week, fix every crash and hang.  Re-run
quarterly.

---

## 9. Conformance and testing (R, ~3 PW)

### 9.1 Spec-derived tests

Every `EXAMPLE` in chapter 7 of ISO 32000-1 already provides ~80 test
vectors.  Encode each as a `#guard` in the test directory.  Add the same
for chapters 8 and 9 once those operators are implemented.

### 9.2 External corpora

| Corpus                                    | Size         | Purpose                          |
|-------------------------------------------|--------------|----------------------------------|
| veraPDF corpus                            | ~12 GB       | Conformance tests for PDF/A      |
| pdf.js test suite                         | ~5 GB        | Real-world rendering quirks      |
| Mozilla "fuzz/zoo" PDFs                   | ~500 MB      | Crash-known-broken inputs        |
| PDF Association sample collection         | ~2 GB        | Broad coverage incl. PDF 2.0     |
| Internal customer corpus                  | varies       | The PDFs you actually care about |

For each corpus, define a regression test that records:
- did `pdf2tex` exit cleanly (or with a tagged warning)?
- did the LaTeX output compile?
- does `pdftotext output.pdf` match a recorded golden?

### 9.3 Differential testing

Run each PDF through (Poppler `pdftotext`) and our parser; diff the
extracted text.  Investigate every ≥ 5 % divergence.  This is the
single most effective way to surface CMap, encoding, and font issues.

### 9.4 Property tests

* `serialise ∘ parse = id` (modulo whitespace) for direct objects.
* `parse(rebuildXref(serialise(parse(p)))) = parse(p)` for documents.
* Random byte mutation never produces a panic, only `Except` errors.

### 9.5 Continuous integration

* Lean version pinned in `lean-toolchain`.
* GitHub Actions matrix: Linux/Mac/Windows × Lean stable/nightly.
* Cache `~/.elan` and `.lake/packages`.
* Block merges on test or fuzz failures.

---

## 10. LaTeX back-end maturity (N, ~2 PW)

The current TikZ-of-nodes back-end is a *layout* output, not a *document*
output.  Two distinct output modes are needed:

### 10.1 "Faithful layout" mode (today, refined)

* Per-page `tikzpicture`, `\node` per text run, bezier paths, image
  inclusions.
* Use `\setlength{\paperwidth}` to match `MediaBox`; honour rotation
  (`/Rotate`).
* Embed fonts via `fontspec` when available; fall back to nearest LaTeX
  font otherwise.

### 10.2 "Reflowable document" mode (new)

* Fed by Tagged-PDF structure tree.
* Emit `\section`, `\subsection`, `\itemize`, `\begin{tabular}`, etc.
* Inline math reconstruction (very hard — separate research project).
* Heuristics when no structure tree exists: clustering text runs into
  paragraphs by line/column geometry.

### 10.3 Other back-ends

A clean separation between the parser core and the renderer makes it
cheap to add:
- HTML/CSS (positioned `<div>`s)
- Plain-text (reading-order extraction)
- JSON dump (for downstream tools)
- SVG (one `<g>` per page)

---

## 11. API and packaging (R, ~1 PW)

### 11.1 Library surface

```lean
namespace PdfLean

structure Config where
  maxStreamSize  : Nat := 256 * 1024 * 1024
  maxDepth       : Nat := 256
  maxObjects     : Nat := 1_000_000
  password       : Option String := none
  warnings       : IO.Ref (Array Warning) := ...

inductive Warning where
  | malformedStream (objNum : Nat) (msg : String)
  | invalidXref (offset : Nat)
  | ...

def open    (path : String) (cfg : Config := {}) : IO (Except Error Document)
def text    (d : Document) : IO String
def render  (d : Document) (mode : RenderMode) : IO String

end PdfLean
```

### 11.2 CLI

```
pdf2tex [options] INPUT.pdf [OUTPUT.tex]
  --password PASS
  --pages 1,3-5,10-
  --mode {layout, reflow, text, json}
  --max-mem 512M
  --warnings-as-errors
  --no-decompress              (for testing)
```

### 11.3 Distribution

* Lake package on Reservoir.
* Pre-built binaries (Linux x86_64 + arm64, macOS, Windows) via
  `lake build --release` in CI.
* Optional `pip install pdf-lean-py` thin wrapper for Python users.

### 11.4 Documentation

* Tutorial: "From PDF to LaTeX in 5 minutes."
* Reference: every public function with examples.
* Architecture doc explaining the module graph and the spec mapping.
* CHANGELOG following SemVer.

---

## 12. Proof-of-correctness (L, open-ended)

Lean 4's whole point is that you *can* prove things.  Aspirational
theorems:

* `parse_pretty_round_trip : ∀ o : DirectObject, parse (pretty o) = .ok (o, _)`
* `xrefTable_unique : ∀ t, ∀ (i j : Nat × Nat), t.entries[i]? = t.entries[j]? → i = j`
* `lexer_total : ∀ bs, ∃ ts, lex bs = .ok ts ∨ lex bs = .error _` (no panics)
* `decompress_bound : ∀ encoded, sizeOf (flateDecode encoded) ≤ maxStreamSize`

Each makes a class of bug *impossible*.  A handful of these would set
`pdf_lean` apart from every other PDF library.

---

## 13. Effort summary

| Area                                 | Required for v1.0 | Person-weeks |
|--------------------------------------|-------------------|--------------|
| Robustness / error tolerance         | ✅                | 6            |
| Compression filters (Flate + predictors) | ✅            | 3            |
| Encryption (RC4 + AES)               | ✅                | 3            |
| Font handling (CMaps + encodings)    | ✅                | 5            |
| Performance                          | ✅                | 2            |
| Security & fuzzing                   | ✅                | 2            |
| Conformance & testing                | ✅                | 3            |
| LaTeX back-end refinement            | ⚠️ partial         | 2            |
| API / packaging / docs               | ✅                | 1            |
| Image filters (DCT/JBIG2/JPX)        | nice-to-have       | 2            |
| Path & colour graphics               | nice-to-have       | 4            |
| Tagged-PDF reflow mode               | nice-to-have       | 3            |
| Public-key encryption                | long-term          | 2            |
| Formal proofs                        | long-term          | open-ended   |
| **Required total**                   |                    | **~27 PW**   |
| **With niceties**                    |                    | **~36 PW**   |

So roughly **6 engineer-months for a credible v1.0** that opens almost
any PDF without falling over, plus another **2–3 months** to be useful
on graphic-heavy documents.

---

## 14. Suggested release sequence

```diagram
v0.2  ─►  Flate + predictors                     (week 3)
v0.3  ─►  Linear-scan xref fallback              (week 5)
v0.4  ─►  Predefined encodings + ToUnicode       (week 9)
v0.5  ─►  RC4/AES decryption                     (week 12)
v0.6  ─►  Per-object error isolation + fuzzing   (week 14)
v0.7  ─►  Performance pass + parallel pages      (week 16)
v0.8  ─►  Tagged-PDF reflow mode                 (week 20)
v0.9  ─►  Image extraction (DCT, raw Flate)      (week 23)
v1.0  ─►  Full corpus regression green; docs     (week 27)
```

Each milestone ships behind a feature flag and is gated by adding the
corresponding regression tests to CI.  Anything more aggressive risks
shipping a parser that *almost* works on real PDFs — a category the
ecosystem already has too many of.
