/-
XML Test Suite — Tests against grammars-v4 examples.
-/
import Lexer
import Parser

open XmlParser

namespace XmlTest

def assertParse (label : String) (input : String) : IO Bool :=
  match parse input with
  | .error msg => do IO.eprintln s!"  FAIL: {label}: {msg}"; return false
  | .ok doc =>
    match doc.root with
    | none => do IO.eprintln s!"  FAIL: {label}: empty document"; return false
    | some root => do
      IO.println s!"  PASS: {label} (<{XmlNode.toString root}>)"
      return true

def assertParseError (label : String) (input : String) : IO Bool :=
  match parse input with
  | .error _ => do IO.println s!"  PASS: {label} (correctly rejected)"; return true
  | .ok _ => do IO.eprintln s!"  FAIL: {label}: should have failed"; return false

def testSimple : IO Bool :=
  assertParse "simple" "<root><child>hello</child></root>"

def testSelfClosing : IO Bool :=
  assertParse "self-closing" "<root><item name=\"x\" value=\"1\"/></root>"

def testAttributes : IO Bool :=
  assertParse "attributes" "<root><person name=\"Alice\" age=\"30\">text</person></root>"

def testComment : IO Bool :=
  assertParse "comment" "<root><!-- a comment --><child>text</child></root>"

def testErrorUnclosed : IO Bool :=
  assertParseError "unclosed" "<root><child>text</root>"

def testExample (filename : String) : IO Bool := do
  try
    let content ← IO.FS.readFile filename
    match parse content with
    | .error msg => do IO.eprintln s!"  FAIL: {filename}: {msg}"; return false
    | .ok doc =>
      match doc.root with
      | none => do IO.eprintln s!"  FAIL: {filename}: empty"; return false
      | some _ => do IO.println s!"  PASS: {filename}"; return true
  catch e =>
    IO.eprintln s!"  FAIL: cannot read {filename}: {e}"
    return false

def main : IO Unit := do
  IO.println "=== XML Parser Test Suite ==="
  let tests : List (String × IO Bool) := [
    ("simple", testSimple),
    ("self-closing", testSelfClosing),
    ("attributes", testAttributes),
    ("comment", testComment),
    ("ERROR: unclosed", testErrorUnclosed)
  ]
  let mut passed := 0
  let mut failed := 0
  for (label, test) in tests do
    IO.println s!"[{label}]"
    match ← test with
    | true => passed := passed + 1
    | false => failed := failed + 1

  IO.println "\n--- Example Files ---"
  let examples := ["examples/books.xml", "examples/underscore.xml", "examples/web.xml"]
  for ex in examples do
    match ← testExample ex with
    | true => passed := passed + 1
    | false => failed := failed + 1

  IO.println s!"\nResults: {passed + failed} tests, {passed} passed, {failed} failed"
  if failed > 0 then IO.Process.exit 1

end XmlTest

def main : IO Unit := XmlTest.main
