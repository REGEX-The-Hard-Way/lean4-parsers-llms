/-
  PdfLean.Ast
  -----------
  Abstract syntax tree for PDF objects (§7.3).
-/

namespace PdfLean

inductive StringKind where
  | literal
  | hex
  deriving Repr, Inhabited

mutual

inductive PDFObject where
  | null
  | bool   (b : Bool)
  | int    (n : Int)
  | real   (s : String)
  | str    (bs : ByteArray) (kind : StringKind)
  | name   (bs : ByteArray)
  | array  (xs : Array PDFObject)
  | dict   (entries : DictEntries)
  | stream (d : DictEntries) (raw : ByteArray)
  | ref    (objNum : Nat) (gen : Nat)

inductive DictEntries where
  | nil
  | cons (key : ByteArray) (val : PDFObject) (rest : DictEntries)

end

instance : Inhabited PDFObject := ⟨PDFObject.null⟩
instance : Inhabited DictEntries := ⟨DictEntries.nil⟩

namespace DictEntries

def toList : DictEntries → List (ByteArray × PDFObject)
  | nil          => []
  | cons k v rs  => (k, v) :: toList rs

def ofList : List (ByteArray × PDFObject) → DictEntries
  | []           => nil
  | (k, v) :: rs => cons k v (ofList rs)

partial def find? (k : ByteArray) : DictEntries → Option PDFObject
  | nil          => none
  | cons k' v r  =>
      if k' = k then some v else find? k r

end DictEntries

namespace PDFObject

partial def repr : PDFObject → String
  | null            => "null"
  | bool true       => "true"
  | bool false      => "false"
  | int n           => toString n
  | real s          => s
  | str bs StringKind.literal =>
      let s := String.fromUTF8! bs
      s!"({s})"
  | str bs StringKind.hex =>
      s!"<hex:{bs.size}B>"
  | name bs         => "/" ++ String.fromUTF8! bs
  | array xs        =>
      let ss := xs.map repr
      "[" ++ String.intercalate " " ss.toList ++ "]"
  | dict es         =>
      let parts := es.toList.map (fun (k, v) =>
        "/" ++ String.fromUTF8! k ++ " " ++ repr v)
      "<<" ++ String.intercalate " " parts ++ ">>"
  | stream d _      => "<<stream " ++ repr (dict d) ++ ">>"
  | ref o g         => s!"{o} {g} R"

instance : Repr PDFObject := ⟨fun o _ => repr o⟩
instance : ToString PDFObject := ⟨repr⟩

/-- Get a dict entry by name (string form). -/
def getKey (o : PDFObject) (key : String) : Option PDFObject :=
  match o with
  | dict es => es.find? key.toUTF8
  | stream d _ => d.find? key.toUTF8
  | _ => none

/-- Treat as integer if possible. -/
def asInt? : PDFObject → Option Int
  | int n => some n
  | _     => none

def asNat? (o : PDFObject) : Option Nat :=
  o.asInt?.bind (fun n => if n ≥ 0 then some n.toNat else none)

def asName? : PDFObject → Option ByteArray
  | name bs => some bs
  | _       => none

def asNameStr? (o : PDFObject) : Option String :=
  o.asName?.map String.fromUTF8!

def asString? : PDFObject → Option ByteArray
  | str bs _ => some bs
  | _        => none

def asArray? : PDFObject → Option (Array PDFObject)
  | array xs => some xs
  | _        => none

def asDict? : PDFObject → Option DictEntries
  | dict es     => some es
  | stream d _  => some d
  | _           => none

end PDFObject
end PdfLean
