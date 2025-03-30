import Std.Data.HashMap
import Std.Data.HashSet
import cvc5.Sql
open Std

-- List intersection function
def listIntersect [DecidableEq α] (l1 l2 : List α) : List α :=
  l1.filter (fun x => x ∈ l2)

-- Example usage
def list1 := [1, 2, 3,3, 4]
def list2 := [3, 4, 5, 6]

#eval listIntersect list1 list2

inductive DBValue
 | boolValue (v: Bool)
 | intValue (v: Int)
 | stringValue (v: String)
deriving BEq, Repr

instance : Inhabited DBValue where
  default := DBValue.boolValue false

def less (a b : DBValue) : Bool :=
  match a, b with
  | .boolValue v1, .boolValue v2 => v1 ≤ v2
  | .intValue v1, .intValue v2 => v1 ≤ v2
  | .stringValue v1, .stringValue v2 => v1 ≤ v2
  | _, _ => false

-- def DBTable (n:Nat) := String × List (Vector DBValue n)

-- def v := Array.toVector #[1,2,3]

-- def List.toVector {α : Type} (xs : List α) : Vector α (xs.length):=
--   Array.toVector (List.toArray xs)

-- def students : DBTable 3 := ("students", [
--   List.toVector [.boolValue false, .intValue 5,.stringValue "a"],
--   List.toVector [.boolValue true, .intValue 6, .stringValue "b"],
--   List.toVector [.intValue 6, .intValue 6, .intValue 6]
-- ]
-- )

-- def DatabaseInstance (tupleLengths: List Nat) := tupleLengths.map (fun x => DBTable x)


def DBRow := List DBValue deriving BEq, Repr
def DBTable := List DBRow deriving BEq, Repr


def lessThan (a b : DBRow) : Bool :=
 match a,b with
 | [],[] => true
 | a::as,b::bs => (less a b) && lessThan as bs
 | [],_ => true
 | _,[] => false


instance : ToString (DBValue) where
  toString
    | .boolValue v => toString v
    | .intValue v => toString v
    | .stringValue v => v

instance : ToString DBRow where
  toString lst := List.toString lst

instance : ToString (DBTable) where
  toString table := match table with
  | [] => "[]"
  | rows => rows.map toString |> String.intercalate "\n"

partial def List.inter (as bs: DBTable) : DBTable :=
  let as' := List.mergeSort as lessThan
  let bs' := List.mergeSort bs lessThan
  match as', bs' with
  | [], _ => []
  | _, [] => []
  | x :: xs, y:: ys =>
    if x == y then x :: List.inter xs ys
    else if lessThan x y then List.inter xs bs'
    else List.inter as' ys

partial def List.minus (as bs: DBTable) : DBTable :=
  let as' := List.mergeSort as lessThan
  let bs' := List.mergeSort bs lessThan
  match as', bs' with
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y:: ys =>
    if x == y then List.minus xs ys
    else if lessThan x y then x::List.minus xs bs'
    else List.minus as' ys

def t1 : DBTable := [[.intValue 100],[.intValue 10],[.intValue 10],[.intValue 10],[.intValue 15]]
def t2 : DBTable := [[.intValue 100],[.intValue 10],[.intValue 10],[.intValue 15]]

#eval List.inter t1 t2
#eval List.minus t1 t2

def DatabaseInstance := HashMap String DBTable


instance : Inhabited DBTable where
  default := []

instance : BEq (DBRow) where
  beq l1 l2 := l1 == l2
instance : Inhabited DBTable where
  default := []


instance : Hashable DBValue where
  hash
    | .boolValue v => hash v
    | .intValue v => hash v
    | .stringValue v => hash v

instance : Hashable DBRow where
  hash lst := lst.foldl (fun acc x => mixHash acc (hash x)) 0


-- Function to remove duplicates
def removeDuplicates {α : Type} [BEq α] [Hashable α] (lst : List α) : List α :=
  let hashSet := lst.foldl (fun acc x => acc.insert x) HashSet.empty
  hashSet.toList

-- Example usage
def myList : List Nat := [1, 2, 2, 3, 4, 4, 5]
def uniqueList := removeDuplicates myList

#eval uniqueList -- Outputs: [1, 2, 3, 4, 5]

#eval Substring.mk "123456789" (String.Pos.mk 0) (String.Pos.mk 4)

def semanticsQueryOp (s : SQLSemantics) (op: QueryOp) (l r : DBTable) : DBTable :=
match op with
| .unionAll  =>
  let result := List.append l r
  match s with
  | .bag => result
  | .set => removeDuplicates (result)
| .union  => removeDuplicates (List.append l r)
| .intersectAll  =>
  let result := List.inter l r
  match s with
  | .bag => result
  | .set => removeDuplicates (result)
| .intersect  => removeDuplicates (List.inter l r)
| .except  => List.minus (removeDuplicates l) r
| .exceptAll  =>
  match s with
  | .bag => List.minus l r
  | .set => List.minus (removeDuplicates l) r

instance : ToString BoolExpr where
  toString expr :=
    match expr with
    | .column i => s!"column {i}"
    | .nullBool => "nullBool"
    | .boolLiteral v => s!"boolLiteral {v}"
    -- | .exists q => s!"exists {q}"
    -- | .case c t e => s!"case {c} {t} {e}"
    | _ => "unknown"

mutual
partial def translateBoolExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: BoolExpr) : DBRow → Option Bool :=
  fun x : DBRow =>
  match expr with
  | .column i => match x.get! i with
    | .boolValue v => some v
    | _ => none
  | .nullBool => none
  | .boolLiteral v => v
  | .exists q => !(semantics s d q).isEmpty
  | .case c t e =>
    let c' := translateBoolExpr s d c
    let t' := translateBoolExpr s d t
    let e' := translateBoolExpr s d e
    let isTrue := fun y : DBRow =>
      let result := (c' y)
      result.isSome && result.get!
    let ite := if isTrue x then t' x else e' x
    ite
  | .stringEqual a b => (translateStringExpr s d a x) == (translateStringExpr s d b x)
  | _ => none

partial def translateStringExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: StringExpr) : DBRow → Option String :=
 fun x : DBRow =>
 match expr with
 | .column i => match x.get! i with
    | .stringValue v => v
    | _ => none
 | .nullString => none
 | .stringLiteral v => v
 | .upper a =>
    match translateStringExpr s d a x with
    | some str => str.toUpper
    | none => none
 | .lower a =>
    match translateStringExpr s d a x with
    | some str => str.toLower
    | none => none
 | .concat a b =>
    let (a', b') := (translateStringExpr s d a x, translateStringExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c.append d
 | .substring a start length =>
    match translateStringExpr s d a x with
    | some str => Substring.mk str (String.Pos.mk (start - 1)) (String.Pos.mk length) |>.toString
    | _ => none
 | .case c t e =>
    let c' := translateBoolExpr s d c
    let t' := translateStringExpr s d t
    let e' := translateStringExpr s d e
    let isTrue := fun y : DBRow =>
      let result := (c' y)
      result.isSome && result.get!
    let ite := if isTrue x then t' x else e' x
    ite


partial def semantics (s : SQLSemantics) (d: DatabaseInstance) (q : Query) : DBTable :=

  match q with
  | .baseTable name =>
    d.get! name
  | .project exprs q => []
  | .join l r join condition => []
  | .filter condition q =>
   let q' := (semantics s d q)
   let p := translateBoolExpr s d condition
   let q'' := List.filter (fun x => (p x).isSome ∧ (p x).get!) q'
   q''

  | .queryOperation op l r => semanticsQueryOp s op (semantics s d l) (semantics s d r)
  | .values rows types => []

end


def table : DBTable := [
  [.boolValue true, .intValue 10, .stringValue "5"],
  [.boolValue true, .intValue 15, .stringValue "5"],
  [.boolValue false, .intValue 08, .stringValue "5"]
  ]

#eval List.mergeSort table lessThan

def d: DatabaseInstance := HashMap.empty.insert "table" table

def q: Query := .filter (BoolExpr.column 0) (.baseTable "table")
#eval q

#eval semantics .bag d q
