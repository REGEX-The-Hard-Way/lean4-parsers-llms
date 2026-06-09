import JsonParser

open JsonParser

namespace JsonQuery

def MatchPred : Type := JsonValue → Bool

def strEq (s : String) : MatchPred := fun | .string v => v == s | _ => false
def strPre (pre : String) : MatchPred := fun | .string v => v.startsWith pre | _ => false
def strSuf (suf : String) : MatchPred := fun | .string v => v.endsWith suf | _ => false
def strHas (sub : String) : MatchPred := fun | .string v => v.contains sub | _ => false
def numEq (s : String) : MatchPred := fun | .number v => v == s | _ => false
def isTrue : MatchPred := fun | .true_ => true | _ => false
def isFalse : MatchPred := fun | .false_ => true | _ => false
def isNull : MatchPred := fun | .null_ => true | _ => false
def any : MatchPred := fun _ => true
def both (m1 m2 : MatchPred) : MatchPred := fun v => m1 v && m2 v
def either (m1 m2 : MatchPred) : MatchPred := fun v => m1 v || m2 v
def notMatch (m : MatchPred) : MatchPred := fun v => !(m v)

inductive PathSeg where | key : String → PathSeg | star | dstar
deriving Repr, BEq

abbrev Path : Type := List PathSeg

def Path.ofString (s : String) : Path :=
  let parts := s.splitOn "."
  parts.map fun p =>
    if p == "*" then PathSeg.star
    else if p == "**" then PathSeg.dstar
    else PathSeg.key p

inductive Selector where
  | val | field (name : String) | index (n : Nat) | at (p : Path)
  | allFields | allElements | where_ (m : MatchPred)
  | pipe (s1 s2 : Selector)

structure Hit where
  value : JsonValue
  path  : List String
deriving Repr, BEq

instance : ToString Hit where
  toString h := s!"{String.intercalate "." h.path.reverse}: {h.value}"

def enumFrom (n : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (n, x) :: enumFrom (n+1) xs

def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

def mapFilter {α β : Type} (f : α → Option β) : List α → List β
  | [] => []
  | x :: xs => match f x with
    | none => mapFilter f xs
    | some y => y :: mapFilter f xs

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => listGet? xs n

mutual

partial def selectPath (p : Path) (val : JsonValue) (path : List String) : List Hit :=
  match p with
  | [] => [{ value := val, path := path }]
  | seg :: rest =>
    match seg with
    | .key name =>
      match val with
      | .object kvs =>
        match List.lookup name kvs with
        | none => []
        | some v => selectPath rest v (name :: path)
      | _ => []
    | .star =>
      match val with
      | .object kvs =>
        listBind kvs fun (k, v) => selectPath rest v (k :: path)
      | .array vs =>
        listBind (enumFrom 0 vs) fun (i, v) =>
          selectPath rest v (s!"[{i}]" :: path)
      | _ => []
    | .dstar =>
      let here := selectPath rest val path
      let deeper :=
        match val with
        | .object kvs =>
          listBind kvs fun (k, v) => selectPath (seg :: rest) v (k :: path)
        | .array vs =>
          listBind (enumFrom 0 vs) fun (i, v) =>
            selectPath (seg :: rest) v (s!"[{i}]" :: path)
        | _ => []
      here ++ deeper

partial def select (s : Selector) (val : JsonValue) (path : List String) : List Hit :=
  match s with
  | .val => [{ value := val, path := path }]
  | .field name =>
    match val with
    | .object kvs =>
      mapFilter (fun (k, v) =>
        if k == name then some { value := v, path := k :: path }
        else none) kvs
    | _ => []
  | .index n =>
    match val with
    | .array vs =>
      match listGet? vs n with
      | none => []
      | some v => [{ value := v, path := s!"[{n}]" :: path }]
    | _ => []
  | .at p => selectPath p val path
  | .allFields =>
    match val with
    | .object kvs => kvs.map fun (k, v) => { value := v, path := k :: path }
    | _ => []
  | .allElements =>
    match val with
    | .array vs =>
      (enumFrom 0 vs).map fun (i, v) => { value := v, path := s!"[{i}]" :: path }
    | _ => []
  | .where_ m =>
    if m val then [{ value := val, path := path }] else []
  | .pipe s1 s2 =>
    let hits := select s1 val path
    listBind hits fun h => select s2 h.value h.path

end

partial def searchField (name : String) (val : JsonValue) : List Hit :=
  let matchCurrent :=
    match val with
    | .object kvs =>
      mapFilter (fun (k, v) =>
        if k == name then some { value := v, path := [k] }
        else none) kvs
    | _ => []
  let recurse :=
    match val with
    | .object kvs =>
      listBind kvs fun (k, v) =>
        (searchField name v).map fun h => { h with path := k :: h.path }
    | .array vs =>
      listBind (enumFrom 0 vs) fun (i, v) =>
        (searchField name v).map fun h => { h with path := s!"[{i}]" :: h.path }
    | _ => []
  matchCurrent ++ recurse

partial def searchMatch (m : MatchPred) (val : JsonValue) : List Hit :=
  let here := if m val then [{ value := val, path := [] }] else []
  let deeper :=
    match val with
    | .object kvs =>
      listBind kvs fun (k, v) =>
        (searchMatch m v).map fun h => { h with path := k :: h.path }
    | .array vs =>
      listBind (enumFrom 0 vs) fun (i, v) =>
        (searchMatch m v).map fun h => { h with path := s!"[{i}]" :: h.path }
    | _ => []
  here ++ deeper

inductive Schema where
  | any | string | number | bool | null
  | arrayOf : Schema → Schema
  | objectOf : List (String × Schema) → Schema
  | orElse : Schema → Schema → Schema
deriving Repr, BEq

partial def validate (schema : Schema) (val : JsonValue) : List String :=
  match schema, val with
  | .any, _ => []
  | .string, .string _ => []
  | .number, .number _ => []
  | .bool, .true_ => []
  | .bool, .false_ => []
  | .null, .null_ => []
  | .arrayOf elemS, .array vs =>
    listBind (enumFrom 0 vs) fun (i, v) =>
      (validate elemS v).map fun err => s!"[{i}]: {err}"
  | .objectOf fields, .object kvs =>
    listBind fields fun (fieldName, fieldS) =>
      match List.lookup fieldName kvs with
      | none => [s!"missing field \"{fieldName}\""]
      | some v => (validate fieldS v).map fun err => s!"\"{fieldName}\": {err}"
  | .orElse a b, v =>
    let errsA := validate a v
    let errsB := validate b v
    if errsA.isEmpty || errsB.isEmpty then [] else ["neither alternative matched"]
  | _, _ => ["type mismatch"]

def query (selector : Selector) (input : String) : Except String (List Hit) :=
  match JsonParser.parse input with
  | .error msg => .error msg
  | .ok val => .ok (select selector val [])

def atPath (path : String) (input : String) : Except String (List Hit) :=
  query (.at (Path.ofString path)) input

def findAll (fieldName : String) (input : String) : Except String (List Hit) :=
  match JsonParser.parse input with
  | .error msg => .error msg
  | .ok val => .ok (searchField fieldName val)

def findMatching (m : MatchPred) (input : String) : Except String (List Hit) :=
  match JsonParser.parse input with
  | .error msg => .error msg
  | .ok val => .ok (searchMatch m val)

def checkSchema (schema : Schema) (input : String) : Except String (List String) :=
  match JsonParser.parse input with
  | .error msg => .error msg
  | .ok val =>
    let errs := validate schema val
    if errs.isEmpty then .ok [] else .error (String.intercalate "\n" errs)

end JsonQuery
