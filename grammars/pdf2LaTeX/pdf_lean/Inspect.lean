import PdfLean
open PdfLean

def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, pageStr] =>
    match pageStr.toNat? with
    | none => IO.eprintln "bad page"; return 1
    | some pg =>
      let bytes ← IO.FS.readBinFile inp
      match Document.open' bytes with
      | Except.error e => IO.eprintln s!"open: {e}"; return 1
      | Except.ok doc =>
        match doc.pages with
        | Except.error e => IO.eprintln s!"pages: {e}"; return 1
        | Except.ok (pages, doc) =>
          IO.println s!"document has {pages.size} pages"
          if pg = 0 ∨ pg > pages.size then
            IO.println "page out of range"; return 1
          else
            let page := pages[pg - 1]!
            IO.println s!"page raw keys:"
            match page.asDict? with
            | some d =>
              for (k, v) in d.toList do
                IO.println s!"  /{String.fromUTF8! k} = {v}"
            | none => IO.println "  (not a dict)"
            -- Resolve /Resources (might be inherited but here check direct)
            match page.getKey "Resources" with
            | none => IO.println "no /Resources directly on page"
            | some res =>
              match doc.derefDeep res with
              | Except.error e => IO.println s!"deref Resources: {e}"
              | Except.ok (resObj, doc) =>
                IO.println s!"Resources keys:"
                match resObj.asDict? with
                | some d =>
                  for (k, _) in d.toList do
                    IO.println s!"  /{String.fromUTF8! k}"
                | none => IO.println "  (not a dict)"
                -- Now walk /Font
                match resObj.getKey "Font" with
                | none => IO.println "no /Font"
                | some fObj =>
                  match doc.derefDeep fObj with
                  | Except.error e => IO.println s!"deref Font: {e}"
                  | Except.ok (fontDict, doc) =>
                    match fontDict.asDict? with
                    | some es =>
                      IO.println s!"Font dict has {es.toList.length} entries"
                      for (k, v) in es.toList do
                        IO.println s!"  font /{String.fromUTF8! k} = {v}"
                        match doc.derefDeep v with
                        | Except.error _ => pure ()
                        | Except.ok (font, _) =>
                          match font.getKey "ToUnicode" with
                          | some _ => IO.println "    has ToUnicode!"
                          | none => IO.println "    NO ToUnicode"
                          match font.getKey "Encoding" with
                          | some e => IO.println s!"    Encoding: {e}"
                          | none => IO.println "    no Encoding"
                    | none => IO.println "Font not a dict"
            -- Now also show what loadFontCMaps produces
            IO.println "--- loadFontCMaps ---"
            match loadFontCMaps doc page with
            | Except.error e => IO.println s!"failed: {e}"
            | Except.ok (cmaps, _) =>
              IO.println s!"loaded {cmaps.size} font CMaps"
              for (k, m) in cmaps.toList do
                IO.println s!"  /{k}: codeBytes={m.codeBytes}, mappings={m.table.size}"
                let entries := m.table.toList.take 8
                for (code, bytes) in entries do
                  let s := String.fromUTF8! bytes
                  IO.println s!"    {code} -> {repr s}"
            return 0
  | _ => IO.println "usage: inspect <pdf> <pageNum>"; return 64
