import Std.Data.HashMap
import Std.Data.HashSet
import cvc5.Sql
open Std

def removeDuplicates {a : Type} [BEq a] [Hashable a] (lst : List a) : List a :=
  let hashSet := lst.foldl (fun acc x => acc.insert x) HashSet.empty
  hashSet.toList

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
def DBTable := List DBRow deriving BEq, Inhabited

instance : Repr DBValue where
  reprPrec v _ := match v with
  | .boolValue v => s!"{v}"
  | .intValue v => s!"{v}"
  | .stringValue v => s!"{v}"

instance : Inhabited DBRow where
  default := []

instance : Inhabited DBTable where
  default := []


def lessThan (a b : DBRow) : Bool :=
 match a,b with
 | [],[] => false
 | a::as,b::bs => (less a b) && lessThan as bs
 | [],_ => false
 | _,[] => false


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

partial def List.minus {a : Type} [BEq a] [Hashable a] (as bs: List a) : List a :=
  let pairs := as.map (fun x => (x, as.count x - bs.count x))
  let filter := pairs.filter (fun (_,n) => n > 0)
  let distinct := removeDuplicates filter
  let result := distinct.flatMap (fun (x,n) => List.replicate n x)
  result

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


#eval List.minus [1,2,2,2,2,2,4] [1,2]

def as' : DBTable := [[.boolValue false,.intValue (some 30),.stringValue "Mixed"], [.boolValue true, .intValue (some 15),.stringValue "lower"], [.boolValue true, .intValue (some 10),.stringValue "UPPER"]]
def bs' : DBTable := [[.boolValue true, .intValue (some 15),.stringValue "lower"], [.boolValue true, .intValue (some 10),.stringValue "UPPER"]]

#eval List.minus as' bs'

def List.product (xs : DBTable) (ys : DBTable) : DBTable :=
  xs.flatMap (fun x => ys.map (fun y => List.append x y))


def t1 : DBTable := [[.intValue (some 100)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 15)]]
def t2 : DBTable := [[.intValue (some 100)],[.intValue (some 10)],[.intValue (some 10)],[.intValue (some 15)]]

#eval List.inter t1 t2
#eval List.minus t1 t2
#eval List.product t1 t2





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
    | .null => "null"
    | .literal v => s!"literal {v}"
    -- | .exists q => s!"exists {q}"
    -- | .case c t e => s!"case {c} {t} {e}"
    | _ => "unknown"


#eval [1,2,3].take 2

mutual
partial def semanticsBoolExpr (s : SQLSemantics) (d: DatabaseInstance) (expr: BoolExpr) : DBRow → Option Bool :=
  fun x : DBRow =>
  match expr with
  | .column i => match x.get! i with
    | .boolValue v => v
    | _ => none
  | .null => none
  | .literal v => v
  | .exists q => !(semantics s d q).isEmpty
  | .case c t e =>
    let (c',t', e'):= (semanticsBoolExpr s d c, semanticsBoolExpr s d t, semanticsBoolExpr s d e)
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
  |.and a b =>
    let (a', b') :=  (semanticsBoolExpr s d a x, semanticsBoolExpr s d b x)
    match a', b' with
    | some x, some y => x && y
    | some false, none => false
    | none, some false => false
    | _, _ => none
  |.or a b =>
    let (a', b') :=  (semanticsBoolExpr s d a x, semanticsBoolExpr s d b x)
    match a', b' with
    | some x, some y => x || y
    | some true, none => true
    | none, some true => true
    | _, _ => none
  |.not a =>
    let a' := semanticsBoolExpr s d a x
    match a' with
    | some x => not x
    | none => none
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
 | .null => none
 | .literal v => v
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
 | .null => none
 | .literal v => v
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
   let f := exprs.map (semanticsExpr s d)
   let f' := fun x : DBRow => f.map (fun g => g x)
   let q'' := List.map f' q'
   q''
  | .join l r join condition =>
    let (l', r') := (semantics s d l, semantics s d r)
    let product := List.product l' r'
    let p := semanticsBoolExpr s d condition
    let result := List.filter (fun x => (p x).isSome && (p x).get!) product
    if product.isEmpty then product
    else
    let nulls (t : DBTable) : List DBValue :=
      (List.range t.length).map
        (fun i => match (t.get! 0).get! i with
          | .boolValue _ => .boolValue (none : Option Bool)
          | .intValue _ => .intValue (none : Option Int)
          | .stringValue _ => .stringValue (none : Option String)
        )
    match join with
     | .inner => result
     | .left =>
      let minus := List.minus l' (result.map (fun x => x.take l'.length))
      let nullsRight := nulls r'
      let minusNulls := minus.map (fun x => x ++ nullsRight)
      List.append result minusNulls
     | .right =>
      let minus := List.minus r' (result.map (fun x => x.drop l'.length))
      let nullsLeft := nulls l'
      let minusNulls := minus.map (fun x => nullsLeft ++ x)
      List.append result minusNulls
     | .full =>
      let leftProject := result.map (fun x => x.take l'.length)
      let minus1 := List.minus l' leftProject
      let nullsRight := nulls r'
      let nulls1 := minus1.map (fun x => x ++ nullsRight)
      let rightProject := result.map (fun x => x.drop l'.length)
      let minus2 := List.minus r' rightProject
      let nullsLeft := nulls l'
      let nulls2 := minus2.map (fun x => nullsLeft ++ x)
      List.append (List.append result nulls1) nulls2
  | .filter condition q =>
    let q' := semantics s d q
    let p := semanticsBoolExpr s d condition
    let q'' := List.filter (fun x => (p x).isSome && (p x).get!) q'
    q''
  | .queryOperation op l r => semanticsQueryOp s op (semantics s d l) (semantics s d r)
  | .values rows _ => rows.map (fun row => row.map (fun e =>
    match e with
    | .boolExpr e' => .boolValue (semanticsBoolExpr s d e' [])
    | .stringExpr e' => .stringValue (semanticsStringExpr s d e' [])
    | .intExpr e' => .intValue (semanticsIntExpr s d e' [])
  ))

end


def table1 : DBTable := [
  [.boolValue true, .intValue (some 10), .stringValue "UPPER"],
  [.boolValue true, .intValue (some 15), .stringValue "lower"],
  [.boolValue false, .intValue (some 08), .stringValue "Mixed"]
  ]

def table2 : DBTable := [
  [.boolValue true, .intValue (some 10), .stringValue "UPPER"],
  [.boolValue true, .intValue (some 15), .stringValue "lower"],
  [.boolValue false, .intValue (some 30), .stringValue "Mixed"]
  ]

#eval List.mergeSort table1 lessThan

def d: DatabaseInstance := (HashMap.empty.insert "table1" table1).insert "table2" table2

def q1: Query := .filter (BoolExpr.column 0) (.baseTable "table1")
def q2: Query :=
  let project := .project [.stringExpr (.upper (.column 2)), .intExpr (.multiplication (.column 1) (.literal 2))] (.baseTable "table1")
  let filter := .filter (.lsInt (.column 1) (.literal 25)) project
  filter

def q3 : Query := .join (.baseTable "table1") (.baseTable "table2") .full (.intEqual (.column 1) (.column 4))

def q4 : Query := .values [[.boolExpr (.null), .intExpr (.null), .stringExpr (.null)]]
                          [.sqlType .boolean true, .sqlType .integer true, .sqlType .text true ]

#eval semantics .bag d q1
#eval semantics .bag d q2
#eval semantics .bag d q3
#eval semantics .bag d q4


def q:Query :=
  .queryOperation .unionAll
    (.queryOperation .exceptAll q1 q2)
    (.queryOperation .exceptAll q1 q2)
