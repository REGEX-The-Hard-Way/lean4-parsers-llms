import PdfLean

open PdfLean

def usage : IO Unit := do
  IO.println "usage: pdf2tex <input.pdf> <output.tex>"
  IO.println ""
  IO.println "The input PDF must be uncompressed (no Flate streams)."
  IO.println "Pre-process compressed PDFs with, e.g.:"
  IO.println "    mutool clean -d -f -i -gggg in.pdf out.pdf"

def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, outp] =>
      let bytes ← IO.FS.readBinFile inp
      match Document.open' bytes with
      | Except.error e =>
          IO.eprintln s!"open failed: {e}"
          return 1
      | Except.ok doc =>
          IO.println s!"loaded; xref entries={doc.xref.entries.size} size={doc.xref.size}"
          match renderDocument doc with
          | Except.error e =>
              IO.eprintln s!"render failed: {e}"
              return 2
          | Except.ok tex =>
              IO.FS.writeFile outp tex
              IO.println s!"wrote {outp} ({tex.length} chars)"
              return 0
  | _ => usage; return 64
