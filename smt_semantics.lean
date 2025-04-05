import Std.Data.HashMap
import Std.Data.HashSet
import cvc5.Sql
import cvc5
import cvc5.Sql

open cvc5 (TermManager Solver Kind)
open Std

def hashSet : HashSet Nat := HashSet.empty.insert 42 |>.insert 7

#eval hashSet

inductive DBValue
 | boolValue (v: Option Bool)
 | intValue (v: Option Int)
 | stringValue (v: Option String)
deriving BEq

instance : Inhabited DBValue where
  default := DBValue.boolValue false

def less (a b : DBValue) : Bool :=
  match a, b with
  | .boolValue (some v1), .boolValue (some v2) => v1 ≤ v2
  | .intValue (some v1), .intValue (some v2) => v1 ≤ v2
  | .stringValue (some v1), .stringValue (some v2) => v1 ≤ v2
  | _, _ => false

def DBRow := List DBValue deriving BEq, Inhabited
instance : Inhabited DBRow where
  default := []

instance : Hashable DBValue where
  hash
    | .boolValue (some v) => hash v
    | .boolValue none => 0
    | .intValue (some v) => hash v
    | .intValue none => 0
    | .stringValue (some v) => hash v
    | .stringValue none => 0

instance : Hashable DBRow where
  hash row := row.foldl (fun acc x => mixHash acc (hash x)) 0

def DBTable := HashMap DBRow Nat deriving Inhabited

instance : Inhabited DBTable where
  default := HashMap.empty

instance : Hashable DBRow where
  hash row := row.foldl (fun acc x => mixHash acc (hash x)) 0

instance : Repr DBValue where
  reprPrec v _ := match v with
  | .boolValue v => s!"{v}"
  | .intValue v => s!"{v}"
  | .stringValue v => s!"{v}"

def lessThan (a b : DBRow) : Bool :=
 match a,b with
 | [],[] => false
 | a::as,b::bs => (less a b) && lessThan as bs
 | [],_ => false
 | _,[] => false


namespace DBTable

def mapRow (table: DBTable) (f: DBRow → DBRow) : DBTable :=
  table.fold (fun acc x n => acc.insert (f x) n) HashMap.empty

def mul (table: DBTable) (row: DBRow) : Nat :=
  let value : Option Nat := table.get? row
  match value with
  | some n => n
  | none => 0

def insert (table: DBTable) (row: DBRow) (n : Nat) : DBTable :=
  match table.mul row with
  | 0 => HashMap.insert table row n
  | m => HashMap.insert table row (m+n)

def inter (t1 t2: DBTable) : DBTable :=
  t1.fold
    (fun acc x n1 =>
     let n2 := DBTable.mul t2 x
     let n := if n1 <= n2 then n1 else n2
     if n > 0 then acc.insert x n else acc)
    HashMap.empty

def unionDisjoint (t1 t2: DBTable) : DBTable :=
  t1.fold
    (fun acc x n1 =>
     let n2 := DBTable.mul t2 x
     let n := n1 + n2
     acc.insert x n)
    t2

def unionMax (t1 t2: DBTable) : DBTable :=
  t1.fold
    (fun acc x n1 =>
     let n2 := DBTable.mul t2 x
     let n := if n1 >= n2 then n1 else n2
     acc.insert x  n)
    t2

def differenceSubtract (t1 t2: DBTable) : DBTable :=
  t1.fold
    (fun acc x n1 =>
     let n2 := DBTable.mul t2 x
     let n := if n1 >= n2 then n1-n2 else n2 - n1
     if n > 0 then acc.insert x  n else acc)
    HashMap.empty

def differenceRemove (t1 t2: DBTable) : DBTable :=
  t1.fold
    (fun acc x n1 =>
     let n2 := DBTable.mul t2 x
     if n2 > 0 then acc else acc.insert x  n1)
    HashMap.empty

def setof (t : DBTable) : DBTable :=
  t.map (fun _ _ => 1)


def getAnyRow (t: DBTable) : Option DBRow :=
  t.fold (fun _ row _ => some row) none

end DBTable

def List.toMap (lst : List (DBRow × Nat)) : DBTable :=
  lst.foldl (fun acc (x,n) => acc.insert x n) HashMap.empty

instance : ToString DBValue where
  toString
    | .boolValue (some v) => toString v
    | .boolValue none => "none"
    | .intValue (some v) => toString v
    | .intValue none => "none"
    | .stringValue (some v) => toString v
    | .stringValue none => "none"

instance : ToString DBRow where
  toString lst := List.toString lst

instance : ToString (DBTable) where
  toString table := toString  (table.toList.map (fun (x,n) => s! "({x},{n})"))

def DatabaseInstance := HashMap String DBTable

instance : BEq (DBRow) where
  beq l1 l2 := l1 == l2

instance : Hashable DBValue where
  hash
    | .boolValue (some v) => hash v
    | .boolValue none => 0
    | .intValue (some v) => hash v
    | .intValue none => 0
    | .stringValue (some v) => hash v
    | .stringValue none => 0

instance : Hashable DBRow where
  hash lst := lst.foldl (fun acc x => mixHash acc (hash x)) 0

def row1: DBRow := [.boolValue false,.intValue (some 30),.stringValue "Mixed"]
def row2:DBRow := [.boolValue true, .intValue (some 15),.stringValue "lower"]
def row3:DBRow := [.boolValue true, .intValue (some 10),.stringValue "UPPER"]
def as' : DBTable := [(row1,1), (row2,1), (row3,1)].toMap
def bs' : DBTable := [(row2,1), (row3,1)].toMap

#eval DBTable.differenceSubtract as' bs'

def DBTable.product (xs : DBTable) (ys : DBTable) : DBTable :=
  xs.fold
    (fun acc1 x n1 =>
     ys.fold
       (fun acc2 y n2 =>
        let n := n1 * n2
        let row := List.append x y
        acc2.insert row n)
       acc1)
    HashMap.empty



def r1 : DBRow := [.intValue (some 100)]
def r2 : DBRow := [.intValue (some 10)]
def r3 : DBRow := [.intValue (some 15)]
def t1 : DBTable := [(r1, 1), (r2, 3),(r3,1)].toMap
def t2 : DBTable := [(r1, 1), (r2, 2),(r3,1)].toMap

#eval DBTable.inter t1 t2
#eval DBTable.differenceSubtract t1 t2
#eval DBTable.product t1 t2


#eval Substring.mk "123456789" (String.Pos.mk 0) (String.Pos.mk 4)

def semanticsQueryOp (s : SQLSemantics) (op: QueryOp) (l r : DBTable) : DBTable :=
match op with
| .unionAll  =>
  let result := l.unionDisjoint r
  match s with
  | .bag => result
  | .set => result.setof
| .union  => (l.unionDisjoint r).setof
| .intersectAll  =>
  let result := l.inter r
  match s with
  | .bag => result
  | .set => result.setof
| .intersect  => (l.inter r).setof
| .except  => l.setof.differenceSubtract r
| .exceptAll  =>
  match s with
  | .bag => l.differenceSubtract r
  | .set => l.setof.differenceSubtract r

instance : ToString BoolExpr where
  toString expr :=
    match expr with
    | .column i => s!"column {i}"
    | .null => "null"
    | .literal v => s!"literal {v}"
    -- | .exists q => s!"exists {q}"
    -- | .case c t e => s!"case {c} {t} {e}"
    | _ => "unknown"


#eval [1,2,3].take 2

def semanticsTuple (s : SQLSemantics) (d: DatabaseInstance) (t : cvc5.Term) : DBRow :=
  sorry


def semantics (s : SQLSemantics) (d: DatabaseInstance) (t : cvc5.Term) : DBTable :=
  match t.getKind with
  | .SET_EMPTY => HashMap.empty
  | .BAG_EMPTY => HashMap.empty
  | .SET_SINGLETON =>
    let row := semanticsTuple s d t[0]!
    [(row ,1)].toMap
  | .BAG_MAKE =>
    let row := semanticsTuple s d t[0]!
    [(row ,t[1]!.getIntegerValue!.toNat)].toMap
  | .SET_UNION =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.unionMax t2).setof
  | .BAG_UNION_DISJOINT =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.unionDisjoint t2)
  | .BAG_UNION_MAX =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.unionMax t2)
  | .SET_INTER =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.inter t2).setof
  | .BAG_INTER_MIN =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.inter t2)
  | .SET_MINUS =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    t1.setof.differenceSubtract t2
  | .BAG_DIFFERENCE_SUBTRACT =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.differenceSubtract t2)
  | .BAG_DIFFERENCE_REMOVE =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.differenceRemove t2)
  | .BAG_SETOF =>
    let t := semantics s d t[0]!
    t.setof
  | .RELATION_PRODUCT =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.product t2)
  | .TABLE_PRODUCT =>
    let t1 := semantics s d t[0]!
    let t2 := semantics s d t[0]!
    (t1.product t2)
  | _ => HashMap.empty
