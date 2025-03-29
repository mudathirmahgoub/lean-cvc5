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

def DBTable := List (List DBValue) deriving BEq, Repr

def table : DBTable := [
  [.boolValue true, .intValue 10, .stringValue "5"],
  [.boolValue true, .intValue 15, .stringValue "5"],
  [.boolValue true, .intValue 08, .stringValue "5"]
  ]

def lessThan (a b : List DBValue) : Bool :=
 match a,b with
 | [],[] => true
 | a::as,b::bs => (less a b) && lessThan as bs
 | [],_ => true
 | _,[] => false


#eval List.mergeSort table lessThan

instance : ToString (DBValue) where
  toString
    | .boolValue v => toString v
    | .intValue v => toString v
    | .stringValue v => v

instance : ToString (List DBValue) where
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

instance : BEq (List DBValue) where
  beq l1 l2 := l1 == l2
instance : Inhabited DBTable where
  default := []


instance : Hashable DBValue where
  hash
    | .boolValue v => hash v
    | .intValue v => hash v
    | .stringValue v => hash v

instance : Hashable (List DBValue) where
  hash lst := lst.foldl (fun acc x => mixHash acc (hash x)) 0


-- Function to remove duplicates
def removeDuplicates {α : Type} [BEq α] [Hashable α] (lst : List α) : List α :=
  let hashSet := lst.foldl (fun acc x => acc.insert x) HashSet.empty
  hashSet.toList

-- Example usage
def myList : List Nat := [1, 2, 2, 3, 4, 4, 5]
def uniqueList := removeDuplicates myList

#eval uniqueList -- Outputs: [1, 2, 3, 4, 5]

def semanticsQueryOp (s : Semantics) (op: QueryOp) (l r : DBTable) : DBTable :=
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
| .intersect  => removeDuplicates (l.filter (fun x => List.elem x r))
| .except  => (removeDuplicates l).filter (fun x => ¬(List.elem x r))
| .exceptAll  =>
  match s with
  | .bag => List.minus l r
  | .set => (removeDuplicates l).filter (fun x => ¬(List.elem x r))

def semantics (s : Semantics) (d: DatabaseInstance) (q : Query) : DBTable :=
  match q with
  | .baseTable name => d.get! name
  | .project exprs q => sorry
  | .join l r join condition => sorry
  | .filter condition query => sorry
  | .queryOperation op l r => semanticsQueryOp s op (semantics s d l) (semantics s d r)
  | .values rows types => sorry
