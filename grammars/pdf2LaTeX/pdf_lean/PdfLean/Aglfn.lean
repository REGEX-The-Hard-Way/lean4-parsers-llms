/-
  PdfLean.Aglfn
  -------------
  Adobe Glyph List for New Fonts (AGLFN) — mapping from PDF glyph names
  to Unicode codepoints.  Split into several smaller functions to avoid
  exceeding clang's match-bracket nesting limit.
-/

namespace PdfLean

/-- ASCII letters and digits. -/
def aglAscii (name : String) : Nat :=
  match name with
  | "zero" => 0x30 | "one" => 0x31 | "two" => 0x32 | "three" => 0x33
  | "four" => 0x34 | "five" => 0x35 | "six" => 0x36 | "seven" => 0x37
  | "eight" => 0x38 | "nine" => 0x39
  | "A" => 0x41 | "B" => 0x42 | "C" => 0x43 | "D" => 0x44 | "E" => 0x45
  | "F" => 0x46 | "G" => 0x47 | "H" => 0x48 | "I" => 0x49 | "J" => 0x4A
  | "K" => 0x4B | "L" => 0x4C | "M" => 0x4D | "N" => 0x4E | "O" => 0x4F
  | "P" => 0x50 | "Q" => 0x51 | "R" => 0x52 | "S" => 0x53 | "T" => 0x54
  | "U" => 0x55 | "V" => 0x56 | "W" => 0x57 | "X" => 0x58 | "Y" => 0x59
  | "Z" => 0x5A
  | "a" => 0x61 | "b" => 0x62 | "c" => 0x63 | "d" => 0x64 | "e" => 0x65
  | "f" => 0x66 | "g" => 0x67 | "h" => 0x68 | "i" => 0x69 | "j" => 0x6A
  | "k" => 0x6B | "l" => 0x6C | "m" => 0x6D | "n" => 0x6E | "o" => 0x6F
  | "p" => 0x70 | "q" => 0x71 | "r" => 0x72 | "s" => 0x73 | "t" => 0x74
  | "u" => 0x75 | "v" => 0x76 | "w" => 0x77 | "x" => 0x78 | "y" => 0x79
  | "z" => 0x7A
  | _ => 0

/-- Common ASCII punctuation. -/
def aglPunct (name : String) : Nat :=
  match name with
  | "space" | "nbspace" | "nonbreakingspace" => 0x20
  | "exclam" => 0x21 | "quotedbl" => 0x22 | "numbersign" => 0x23
  | "dollar" => 0x24 | "percent" => 0x25 | "ampersand" => 0x26
  | "quotesingle" => 0x27
  | "parenleft" => 0x28 | "parenright" => 0x29
  | "asterisk" => 0x2A | "plus" => 0x2B | "comma" => 0x2C
  | "hyphen" | "hyphenminus" => 0x2D | "period" => 0x2E
  | "slash" => 0x2F | "colon" => 0x3A | "semicolon" => 0x3B
  | "less" => 0x3C | "equal" => 0x3D | "greater" => 0x3E
  | "question" => 0x3F | "at" => 0x40
  | "bracketleft" => 0x5B | "backslash" => 0x5C | "bracketright" => 0x5D
  | "asciicircum" => 0x5E | "underscore" => 0x5F | "grave" => 0x60
  | "braceleft" => 0x7B | "bar" => 0x7C | "braceright" => 0x7D
  | "asciitilde" => 0x7E
  | _ => 0

/-- Latin-1 supplement. -/
def aglLatin1 (name : String) : Nat :=
  match name with
  | "exclamdown" => 0xA1 | "cent" => 0xA2 | "sterling" => 0xA3
  | "currency" => 0xA4 | "yen" => 0xA5 | "brokenbar" => 0xA6
  | "section" => 0xA7 | "dieresis" => 0xA8 | "copyright" => 0xA9
  | "ordfeminine" => 0xAA | "guillemotleft" => 0xAB | "logicalnot" => 0xAC
  | "registered" => 0xAE | "macron" => 0xAF | "degree" => 0xB0
  | "plusminus" => 0xB1 | "twosuperior" => 0xB2 | "threesuperior" => 0xB3
  | "acute" => 0xB4 | "mu" => 0xB5 | "paragraph" => 0xB6
  | "periodcentered" => 0xB7 | "cedilla" => 0xB8 | "onesuperior" => 0xB9
  | "ordmasculine" => 0xBA | "guillemotright" => 0xBB
  | "onequarter" => 0xBC | "onehalf" => 0xBD | "threequarters" => 0xBE
  | "questiondown" => 0xBF
  | _ => 0

/-- Latin-1 capital letters with diacritics. -/
def aglLatinCaps (name : String) : Nat :=
  match name with
  | "Agrave" => 0xC0 | "Aacute" => 0xC1 | "Acircumflex" => 0xC2
  | "Atilde" => 0xC3 | "Adieresis" => 0xC4 | "Aring" => 0xC5 | "AE" => 0xC6
  | "Ccedilla" => 0xC7 | "Egrave" => 0xC8 | "Eacute" => 0xC9
  | "Ecircumflex" => 0xCA | "Edieresis" => 0xCB | "Igrave" => 0xCC
  | "Iacute" => 0xCD | "Icircumflex" => 0xCE | "Idieresis" => 0xCF
  | "Eth" => 0xD0 | "Ntilde" => 0xD1 | "Ograve" => 0xD2 | "Oacute" => 0xD3
  | "Ocircumflex" => 0xD4 | "Otilde" => 0xD5 | "Odieresis" => 0xD6
  | "multiply" => 0xD7 | "Oslash" => 0xD8 | "Ugrave" => 0xD9
  | "Uacute" => 0xDA | "Ucircumflex" => 0xDB | "Udieresis" => 0xDC
  | "Yacute" => 0xDD | "Thorn" => 0xDE | "germandbls" => 0xDF
  | _ => 0

/-- Latin-1 lowercase letters with diacritics. -/
def aglLatinLower (name : String) : Nat :=
  match name with
  | "agrave" => 0xE0 | "aacute" => 0xE1 | "acircumflex" => 0xE2
  | "atilde" => 0xE3 | "adieresis" => 0xE4 | "aring" => 0xE5 | "ae" => 0xE6
  | "ccedilla" => 0xE7 | "egrave" => 0xE8 | "eacute" => 0xE9
  | "ecircumflex" => 0xEA | "edieresis" => 0xEB | "igrave" => 0xEC
  | "iacute" => 0xED | "icircumflex" => 0xEE | "idieresis" => 0xEF
  | "eth" => 0xF0 | "ntilde" => 0xF1 | "ograve" => 0xF2 | "oacute" => 0xF3
  | "ocircumflex" => 0xF4 | "otilde" => 0xF5 | "odieresis" => 0xF6
  | "divide" => 0xF7 | "oslash" => 0xF8 | "ugrave" => 0xF9
  | "uacute" => 0xFA | "ucircumflex" => 0xFB | "udieresis" => 0xFC
  | "yacute" => 0xFD | "thorn" => 0xFE | "ydieresis" => 0xFF
  | _ => 0

/-- Ligatures, accents, dotless variants. -/
def aglLigaturesAccents (name : String) : Nat :=
  match name with
  | "OE" => 0x152 | "oe" => 0x153 | "fi" => 0xFB01 | "fl" => 0xFB02
  | "ff" => 0xFB00 | "ffi" => 0xFB03 | "ffl" => 0xFB04
  | "Lslash" => 0x141 | "lslash" => 0x142 | "Scaron" => 0x160
  | "scaron" => 0x161 | "Zcaron" => 0x17D | "zcaron" => 0x17E
  | "Ydieresis" => 0x178 | "florin" => 0x192
  | "circumflex" => 0x2C6 | "caron" => 0x2C7 | "breve" => 0x2D8
  | "dotaccent" => 0x2D9 | "ring" => 0x2DA | "ogonek" => 0x2DB
  | "tilde" => 0x2DC | "hungarumlaut" => 0x2DD | "dotlessi" => 0x131
  | _ => 0

/-- General punctuation block. -/
def aglGeneralPunct (name : String) : Nat :=
  match name with
  | "endash" => 0x2013 | "emdash" => 0x2014
  | "quoteleft" => 0x2018 | "quoteright" => 0x2019
  | "quotedblleft" => 0x201C | "quotedblright" => 0x201D
  | "quotedblbase" => 0x201E | "quotesinglbase" => 0x201A
  | "guilsinglleft" => 0x2039 | "guilsinglright" => 0x203A
  | "bullet" => 0x2022 | "ellipsis" => 0x2026 | "trademark" => 0x2122
  | "perthousand" => 0x2030 | "fraction" => 0x2044
  | "Euro" => 0x20AC | "dagger" => 0x2020 | "daggerdbl" => 0x2021
  | _ => 0

/-- Math symbols, arrows. -/
def aglMath (name : String) : Nat :=
  match name with
  | "minus" => 0x2212 | "infinity" => 0x221E | "summation" => 0x2211
  | "product" => 0x220F | "integral" => 0x222B | "partialdiff" => 0x2202
  | "radical" => 0x221A | "approxequal" => 0x2248
  | "notequal" => 0x2260 | "lessequal" => 0x2264 | "greaterequal" => 0x2265
  | "arrowleft" => 0x2190 | "arrowup" => 0x2191
  | "arrowright" => 0x2192 | "arrowdown" => 0x2193
  | "arrowboth" => 0x2194 | "arrowdblboth" => 0x21D4
  | "arrowdblleft" => 0x21D0 | "arrowdblright" => 0x21D2
  | "logicaland" => 0x2227 | "logicalor" => 0x2228
  | "element" => 0x2208 | "notelement" => 0x2209
  | "intersection" => 0x2229 | "union" => 0x222A
  | _ => 0

/-- Greek letters (lowercase + uppercase). -/
def aglGreek (name : String) : Nat :=
  match name with
  | "alpha" => 0x3B1 | "beta" => 0x3B2 | "gamma" => 0x3B3
  | "delta" => 0x3B4 | "epsilon" => 0x3B5 | "zeta" => 0x3B6
  | "eta" => 0x3B7 | "theta" => 0x3B8 | "iota" => 0x3B9
  | "kappa" => 0x3BA | "lambda" => 0x3BB | "nu" => 0x3BD
  | "xi" => 0x3BE | "omicron" => 0x3BF | "pi" => 0x3C0
  | "rho" => 0x3C1 | "sigma" => 0x3C3 | "tau" => 0x3C4
  | "upsilon" => 0x3C5 | "phi" => 0x3C6 | "chi" => 0x3C7
  | "psi" => 0x3C8 | "omega" => 0x3C9
  | "Alpha" => 0x391 | "Beta" => 0x392 | "Gamma" => 0x393
  | "Delta" => 0x394 | "Epsilon" => 0x395 | "Zeta" => 0x396
  | "Eta" => 0x397 | "Theta" => 0x398 | "Iota" => 0x399
  | "Kappa" => 0x39A | "Lambda" => 0x39B | "Mu" => 0x39C
  | "Nu" => 0x39D | "Xi" => 0x39E | "Omicron" => 0x39F
  | "Pi" => 0x3A0 | "Rho" => 0x3A1 | "Sigma" => 0x3A3
  | "Tau" => 0x3A4 | "Upsilon" => 0x3A5 | "Phi" => 0x3A6
  | "Chi" => 0x3A7 | "Psi" => 0x3A8 | "Omega" => 0x3A9
  | _ => 0

/-- Parse a hex digit string. -/
def parseHex (s : String) : Nat := Id.run do
  let mut v : Nat := 0
  for c in s.toList do
    if c.isDigit then
      v := v * 16 + (c.toNat - '0'.toNat)
    else if c ≥ 'A' ∧ c ≤ 'F' then
      v := v * 16 + (c.toNat - 'A'.toNat + 10)
    else if c ≥ 'a' ∧ c ≤ 'f' then
      v := v * 16 + (c.toNat - 'a'.toNat + 10)
    else
      return 0
  return v

/-- Parse the `uniXXXX` / `uXXXXXX` glyph-name fallbacks defined by AGLFN. -/
def aglUniFallback (name : String) : Nat :=
  if name.startsWith "uni" ∧ name.length = 7 then
    parseHex ((name.drop 3).toString)
  else if name.startsWith "u" ∧ name.length ≥ 5 ∧ name.length ≤ 7 then
    parseHex ((name.drop 1).toString)
  else
    0

/-- Top-level glyph-name → Unicode lookup; tries all the chunked tables
    above and returns 0 if nothing matched. -/
def aglToUnicode (name : String) : Nat :=
  let r := aglAscii name
  if r ≠ 0 then r else
  let r := aglPunct name
  if r ≠ 0 then r else
  let r := aglLatin1 name
  if r ≠ 0 then r else
  let r := aglLatinCaps name
  if r ≠ 0 then r else
  let r := aglLatinLower name
  if r ≠ 0 then r else
  let r := aglLigaturesAccents name
  if r ≠ 0 then r else
  let r := aglGeneralPunct name
  if r ≠ 0 then r else
  let r := aglMath name
  if r ≠ 0 then r else
  let r := aglGreek name
  if r ≠ 0 then r else
  aglUniFallback name

end PdfLean
