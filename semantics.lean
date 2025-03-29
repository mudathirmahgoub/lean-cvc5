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
deriving BEq

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

def DBTable := List (List DBValue)

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
  let result := l.filter (fun x => List.elem x r)
  match s with
  | .bag => result
  | .set => removeDuplicates (result)
| .intersect  => removeDuplicates (l.filter (fun x => List.elem x r))
| .exceptAll  => removeDuplicates (List.append l r)
| .except  => (removeDuplicates l).filter (fun x => ¬(List.elem x r))

def semantics (s : Semantics) (d: DatabaseInstance) (q : Query) : DBTable :=
  match q with
  | .baseTable name => d.get! name
  | .project exprs q => sorry
  | .join l r join condition => sorry
  | .filter condition query => sorry
  | .queryOperation op l r => semanticsQueryOp s d op (semantics d l) (semantics d r)
  | .values rows types => sorry
