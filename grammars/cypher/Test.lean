/-
Cypher Lexer Test — Validates tokenization against example queries.
-/
import Lexer

open CypherLexer

def main : IO Unit := do
  IO.println "=== Cypher Lexer Test ===\n"

  let tests : List (String × String) := [
    ("simple match", "MATCH (n) RETURN n"),
    ("where clause", "MATCH (n:Person) WHERE n.age > 30 RETURN n.name"),
    ("create", "CREATE (n:Person {name: 'Alice', age: 30})"),
    ("merge", "MERGE (n:Person {name: 'Bob'}) ON CREATE SET n.created = timestamp()"),
    ("delete detach", "MATCH (n) DETACH DELETE n"),
    ("order limit skip", "MATCH (n) RETURN n ORDER BY n.name ASC SKIP 10 LIMIT 5"),
    ("optional match", "OPTIONAL MATCH (n)-[r]->(m) RETURN n, r, m"),
    ("with unwind", "WITH [1, 2, 3] AS list UNWIND list AS item RETURN item"),
    ("case when", "MATCH (n) RETURN CASE WHEN n.age > 18 THEN 'adult' ELSE 'child' END"),
    ("exists", "MATCH (n) WHERE EXISTS { MATCH (n)-[:KNOWS]->(m) } RETURN n"),
    ("backtick ident", "MATCH (`my node`) RETURN `my node`"),
    ("string literal", "RETURN \"hello world\", 'single quoted'"),
    ("math ops", "RETURN 1 + 2 * 3 - 4 / 5 % 6 ^ 2"),
    ("comparisons", "RETURN 1 < 2 AND 3 <= 4 AND 5 > 6 AND 7 >= 8 AND 9 <> 10")
  ]

  for (label, input) in tests do
    let tokens := tokenize input
    let kinds := String.intercalate " " (tokens.map Prod.snd)
    IO.println s!"[{label}]"
    IO.println s!"  Input: {input}"
    IO.println s!"  Tokens: {kinds}"
    IO.println ""

  IO.println "\nDone!"
