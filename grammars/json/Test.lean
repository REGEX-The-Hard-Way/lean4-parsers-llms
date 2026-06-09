/-
JSON Test Suite — Tests the JSON lexer and parser against example files.
-/
import Lexer
import JsonParser

namespace JsonTest

-- ============================================================
-- Test utilities
-- ============================================================

/-- Assert that two values are equal; print pass/fail. -/
def assertEq [BEq α] [ToString α] (label : String) (expected : α) (actual : α) : IO Bool := do
  if expected == actual then
    IO.println s!"  ✓ {label}"
    return true
  else
    IO.eprintln s!"  ✗ {label}: expected {expected}, got {actual}"
    return false

/-- Assert that a parse succeeds. -/
def assertParse (label : String) (input : String) (expected : JsonParser.JsonValue) : IO Bool :=
  match JsonParser.parse input with
  | .error msg => do
    IO.eprintln s!"  ✗ {label}: parse error: {msg}"
    return false
  | .ok val =>
    assertEq label expected val

/-- Assert that a parse fails (for error tests). -/
def assertParseError (label : String) (input : String) : IO Bool :=
  match JsonParser.parse input with
  | .error _ => do IO.println s!"  ✓ {label} (correctly rejected)"; return true
  | .ok val => do IO.eprintln s!"  ✗ {label}: should have failed but got: {val}"; return false

-- ============================================================
-- Unit tests
-- ============================================================

def testNull : IO Bool :=
  assertParse "null" "null" JsonParser.JsonValue.null_

def testTrue : IO Bool :=
  assertParse "true" "true" JsonParser.JsonValue.true_

def testFalse : IO Bool :=
  assertParse "false" "false" JsonParser.JsonValue.false_

def testString : IO Bool :=
  assertParse "simple string" "\"hello\"" (JsonParser.JsonValue.string "hello")

def testEmptyString : IO Bool :=
  assertParse "empty string" "\"\"" (JsonParser.JsonValue.string "")

def testInteger : IO Bool :=
  assertParse "integer" "42" (JsonParser.JsonValue.number "42")

def testNegativeNumber : IO Bool :=
  assertParse "negative" "-17" (JsonParser.JsonValue.number "-17")

def testFloat : IO Bool :=
  assertParse "float" "3.14" (JsonParser.JsonValue.number "3.14")

def testScientific : IO Bool :=
  assertParse "scientific" "1.5e10" (JsonParser.JsonValue.number "1.5e10")

def testEmptyArray : IO Bool :=
  assertParse "empty array" "[]" (JsonParser.JsonValue.array [])

def testSimpleArray : IO Bool :=
  assertParse "simple array" "[1, 2, 3]"
    (JsonParser.JsonValue.array [
      JsonParser.JsonValue.number "1",
      JsonParser.JsonValue.number "2",
      JsonParser.JsonValue.number "3"
    ])

def testNestedArray : IO Bool :=
  assertParse "nested array" "[[1, 2], [3, 4]]"
    (JsonParser.JsonValue.array [
      JsonParser.JsonValue.array [
        JsonParser.JsonValue.number "1",
        JsonParser.JsonValue.number "2"
      ],
      JsonParser.JsonValue.array [
        JsonParser.JsonValue.number "3",
        JsonParser.JsonValue.number "4"
      ]
    ])

def testEmptyObject : IO Bool :=
  assertParse "empty object" "{}" (JsonParser.JsonValue.object [])

def testSimpleObject : IO Bool :=
  assertParse "simple object" "{\"a\": 1}"
    (JsonParser.JsonValue.object [("a", JsonParser.JsonValue.number "1")])

def testMultiObject : IO Bool :=
  assertParse "multi object" "{\"a\": 1, \"b\": true}"
    (JsonParser.JsonValue.object [
      ("a", JsonParser.JsonValue.number "1"),
      ("b", JsonParser.JsonValue.true_)
    ])

def testNestedObject : IO Bool :=
  assertParse "nested object" "{\"x\": {\"y\": 2}}"
    (JsonParser.JsonValue.object [
      ("x", JsonParser.JsonValue.object [("y", JsonParser.JsonValue.number "2")])
    ])

def testComplex : IO Bool :=
  assertParse "complex" "{\"a\": [1, 2], \"b\": {\"c\": true}}"
    (JsonParser.JsonValue.object [
      ("a", JsonParser.JsonValue.array [
        JsonParser.JsonValue.number "1",
        JsonParser.JsonValue.number "2"
      ]),
      ("b", JsonParser.JsonValue.object [
        ("c", JsonParser.JsonValue.true_)
      ])
    ])

-- ============================================================
-- Error tests
-- ============================================================

def testErrorTrailingComma : IO Bool :=
  assertParseError "trailing comma" "[1,]"

def testErrorUnquotedKey : IO Bool :=
  assertParseError "unquoted key" "{a: 1}"

def testErrorSingleQuote : IO Bool :=
  assertParseError "single quotes" "'hello'"

-- ============================================================
-- Example file tests
-- ============================================================

def testExampleFile (filename : String) : IO Bool := do
  try
    let content ← IO.FS.readFile filename
    match JsonParser.parse content with
    | .error msg => do
      IO.eprintln s!"  FAIL: {filename}: parse error: {msg}"
      return false
    | .ok _ => do
      IO.println s!"  PASS: {filename} parsed successfully"
      return true
  catch e =>
    IO.eprintln s!"  FAIL: Cannot read {filename}: {e}"
    return false

-- ============================================================
-- Run all tests
-- ============================================================

def runAll : IO Unit := do
  IO.println "=== JSON Parser Test Suite ==="
  let tests : List (String × IO Bool) := [
    ("null literal", testNull),
    ("true literal", testTrue),
    ("false literal", testFalse),
    ("simple string", testString),
    ("empty string", testEmptyString),
    ("integer", testInteger),
    ("negative number", testNegativeNumber),
    ("float", testFloat),
    ("scientific notation", testScientific),
    ("empty array", testEmptyArray),
    ("simple array", testSimpleArray),
    ("nested array", testNestedArray),
    ("empty object", testEmptyObject),
    ("simple object", testSimpleObject),
    ("multi object", testMultiObject),
    ("nested object", testNestedObject),
    ("complex", testComplex),
    ("ERROR: trailing comma", testErrorTrailingComma),
    ("ERROR: unquoted key", testErrorUnquotedKey),
    ("ERROR: single quotes", testErrorSingleQuote)
  ]

  let mut passed := 0
  let mut failed := 0
  for (label, test) in tests do
    IO.print s!"[{label}] "
    match ← test with
    | true => passed := passed + 1
    | false => failed := failed + 1

  IO.println ""
  IO.println "--- Example Files ---"
  let examples := ["examples/example1.json", "examples/numbers.json"]
  for ex in examples do
    match ← testExampleFile ex with
    | true => passed := passed + 1
    | false => failed := failed + 1

  IO.println ""
  IO.println s!"Results: {passed + failed} tests, {passed} passed, {failed} failed"
  if failed > 0 then
    IO.Process.exit 1

end JsonTest

def main : IO Unit := JsonTest.runAll
