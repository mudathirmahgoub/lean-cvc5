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
 | boolValue (v: Option Bool)
 | intValue (v: Option Int)
 | stringValue (v: Option String)
deriving BEq, Repr

instance : Inhabited DBValue where
  default := DBValue.boolValue false

def less (a b : DBValue) : Bool :=
  match a, b with
  | .boolValue (some v1), .boolValue (some v2) => v1 ≤ v2
  | .intValue (some v1), .intValue (some v2) => v1 ≤ v2
  | .stringValue (some v1), .stringValue (some v2) => v1 ≤ v2
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
    | .stringValue v => toString v

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

def t1 : DBTable := [[.intValue (some 100)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 15)]]
def t2 : DBTable := [[.intValue (some 100)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 15)]]

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
partial def semanticsBoolExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: BoolExpr) : DBRow → Option Bool :=
  fun x : DBRow =>
  match expr with
  | .column i => match x.get! i with
    | .boolValue v => v
    | _ => none
  | .nullBool => none
  | .boolLiteral v => v
  | .exists q => !(semantics s d q).isEmpty
  | .case c t e =>
    let c' := semanticsBoolExpr s d c
    let t' := semanticsBoolExpr s d t
    let e' := semanticsBoolExpr s d e
    let isTrue := fun y : DBRow =>
      let result := (c' y)
      result.isSome && result.get!
    let ite := if isTrue x then t' x else e' x
    ite
  | .boolEqual a b =>
    let (a', b') :=  (semanticsBoolExpr s d a x, semanticsBoolExpr s d b x)
    match a', b' with
    | some x, some y => x == y
    | _, _ => none
  | .stringEqual a b =>
    let (a', b') :=  (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | some x, some y => x == y
    | _, _ => none
  | .intEqual a b =>
    let (a', b') :=  (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | some x, some y => x == y
    | _, _ => none
  | .lsInt a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | some x, some y => some (x < y)
    | _, _ => none
  | .leqInt a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | some x, some y => some (x <= y)
    | _, _ => none
  | .gtInt a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | some x, some y => some (x > y)
    | _, _ => none
  | .geqInt a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | some x, some y => some (x >= y)
    | _, _ => none
  | .lsString a b =>
    let (a', b') := (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | some x, some y => some (x < y)
    | _, _ => none
  | .leqString a b =>
    let (a', b') := (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | some x, some y => some (x <= y)
    | _, _ => none
  | .gtString a b =>
    let (a', b') := (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | some x, some y => some (x > y)
    | _, _ => none
  | .geqString a b =>
    let (a', b') := (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | some x, some y => some (x >= y)
    | _, _ => none
  | .isNullBool a =>
    let a' := semanticsBoolExpr s d a x
    a' == none
  | .isNotNullBool a =>
    let a' := semanticsBoolExpr s d a x
    a' != none
  | .isNullString a =>
    let a' := semanticsStringExpr s d a x
    a' == none
  | .isNotNullString a =>
    let a' := semanticsStringExpr s d a x
    a' != none
  | .isNullInt a =>
    let a' := semanticsIntExpr s d a x
    a' == none
  | .isNotNullInt a =>
    let a' := semanticsIntExpr s d a x
    a' != none
  | .isTrue a =>
    let a' := semanticsBoolExpr s d a x
    a' == some true
  | .isNotTrue a =>
    let a' := semanticsBoolExpr s d a x
    a' != some true


partial def semanticsIntExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: IntExpr) : DBRow → Option Int :=
 fun x : DBRow =>
 match expr with
 | .column i => match x.get! i with
    | .intValue v => v
    | _ => none
 | .nullInt => none
 | .intLiteral v => v
 | .plus a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c + d
 | .minus a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c - d
 | .multiplication a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c * d
 | .division a b =>
    let (a', b') := (semanticsIntExpr s d a x, semanticsIntExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c / d
 | .case c t e =>
    let c' := semanticsBoolExpr s d c
    let t' := semanticsIntExpr s d t
    let e' := semanticsIntExpr s d e
    let isTrue := fun y : DBRow =>
      let result := (c' y)
      result.isSome && result.get!
    let ite := if isTrue x then t' x else e' x
    ite

partial def semanticsStringExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: StringExpr) : DBRow → Option String :=
 fun x : DBRow =>
 match expr with
 | .column i => match x.get! i with
    | .stringValue v => v
    | _ => none
 | .nullString => none
 | .stringLiteral v => v
 | .upper a =>
    match semanticsStringExpr s d a x with
    | some str => str.toUpper
    | none => none
 | .lower a =>
    match semanticsStringExpr s d a x with
    | some str => str.toLower
    | none => none
 | .concat a b =>
    let (a', b') := (semanticsStringExpr s d a x, semanticsStringExpr s d b x)
    match a', b' with
    | none, _ => none
    | _, none => none
    | some c, some d => c.append d
 | .substring a start length =>
    match semanticsStringExpr s d a x with
    | some str => Substring.mk str (String.Pos.mk (start - 1)) (String.Pos.mk length) |>.toString
    | _ => none
 | .case c t e =>
    let c' := semanticsBoolExpr s d c
    let t' := semanticsStringExpr s d t
    let e' := semanticsStringExpr s d e
    let isTrue := fun y : DBRow =>
      let result := (c' y)
      result.isSome && result.get!
    let ite := if isTrue x then t' x else e' x
    ite

partial def semanticsExpr (s : SQLSemantics) (d: DatabaseInstance) (e : Expr): DBRow → DBValue :=
  fun x =>
  match e with
  |.boolExpr e' => .boolValue (semanticsBoolExpr s d e' x)
  |.stringExpr e' => .stringValue (semanticsStringExpr s d e' x)
  |.intExpr e' => .intValue (semanticsIntExpr s d e' x)

partial def semantics (s : SQLSemantics) (d: DatabaseInstance) (q : Query) : DBTable :=
  match q with
  | .baseTable name =>
    d.get! name
  | .project exprs q =>
   let q' := semantics s d q
   let f := exprs.map (semanticsExpr s d) |>.toList
   let f' := fun x : DBRow => f.map (fun g => g x)
   let q'' := List.map f' q'
   q''
  | .join l r join condition => []
  | .filter condition q =>
   let q' := semantics s d q
   let p := semanticsBoolExpr s d condition
   let q'' := List.filter (fun x => (p x).isSome ∧ (p x).get!) q'
   q''

  | .queryOperation op l r => semanticsQueryOp s op (semantics s d l) (semantics s d r)
  | .values rows types => []

end


def table : DBTable := [
  [.boolValue true, .intValue (some 10), .stringValue "UPPER"],
  [.boolValue true, .intValue (some 15), .stringValue "lower"],
  [.boolValue false, .intValue (some 08), .stringValue "Mixed"]
  ]

#eval List.mergeSort table lessThan

def d: DatabaseInstance := HashMap.empty.insert "table" table

def q1: Query := .filter (BoolExpr.column 0) (.baseTable "table")
def q2: Query :=
  let project := .project #[.stringExpr (.upper (.column 2)), .intExpr (.multiplication (.column 1) (.intLiteral 2))] (.baseTable "table")
  let filter := .filter (.lsInt (.column 1) (.intLiteral 25)) project
  filter
#eval q1

#eval semantics .bag d q1
#eval semantics .bag d q2
