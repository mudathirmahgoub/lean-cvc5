import Std.Data.HashMap
import Std.Data.HashSet
import cvc5.Sql
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
 | .substring2 a b =>
 let a' := semanticsStringExpr s d a x
 let b' := semanticsIntExpr s d b x
 match (a', b') with
    | (some str, some i) =>
      Substring.mk str (String.Pos.mk ((i - 1).toNat)) (String.Pos.mk (String.length str)) |>.toString
    | _ => none
 | .substring3 a b c=>
 let a' := semanticsStringExpr s d a x
 let b' := semanticsIntExpr s d b x
 let c' := semanticsIntExpr s d c x
 match (a', b', c') with
    | (some str, some i, some j) =>
      Substring.mk str (String.Pos.mk ((i - 1).toNat)) (String.Pos.mk j.toNat) |>.toString
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
   let f' : DBRow → DBRow := fun x : DBRow => f.map (fun g => g x)
   let q'' := q'.mapRow f'
   q''
  | .join l r join condition =>
    let (l', r') := (semantics s d l, semantics s d r)
    let product := DBTable.product l' r'
    let p := semanticsBoolExpr s d condition
    let result : DBTable := product.filter (fun x _ => (p x).isSome && (p x).get!)
    if product.isEmpty then product
    else
    let leftLength := l'.getAnyRow.get!.length
    let nullsRow (t : DBRow) : DBRow :=
      t.map (fun x => match x with
          | .boolValue _ => .boolValue (none : Option Bool)
          | .intValue _ => .intValue (none : Option Int)
          | .stringValue _ => .stringValue (none : Option String)
        )
    match join with
     | .inner => result
     | .left =>
      let minus := l'.differenceSubtract  (result.mapRow (fun x => x.take leftLength))
      let nullsRight := nullsRow r'.getAnyRow.get!
      let minusNulls := minus.mapRow (fun x => List.append x nullsRight)
      result.unionDisjoint minusNulls
     | .right =>
      let minus := r'.differenceSubtract (result.mapRow (fun x => x.drop leftLength))
      let nullsLeft := nullsRow l'.getAnyRow.get!
      let minusNulls := minus.mapRow (fun x => List.append nullsLeft  x)
      result.unionDisjoint minusNulls
     | .full =>
      let leftProject := result.mapRow (fun x => x.take leftLength)
      let minus1 := l'.differenceSubtract leftProject
      let nullsRight := nullsRow r'.getAnyRow.get!
      let nulls1 := minus1.mapRow (fun x => List.append x nullsRight)
      let rightProject := result.mapRow (fun x => x.drop leftLength)
      let minus2 := r'.differenceSubtract rightProject
      let nullsLeft := nullsRow l'.getAnyRow.get!
      let nulls2 := minus2.mapRow (fun x => List.append nullsLeft x)
      (result.unionDisjoint nulls1).unionDisjoint nulls2
  | .filter condition q =>
    let q' := semantics s d q
    let p := semanticsBoolExpr s d condition
    let q'' := q'.filter (fun x _ => (p x).isSome && (p x).get!)
    q''
  | .queryOperation op l r => semanticsQueryOp s op (semantics s d l) (semantics s d r)
  | .values rows _ =>
    let result : DBTable := rows.foldl
      (fun acc row =>
       let row' := row.map (fun e => match e with
         | .boolExpr e' => .boolValue (semanticsBoolExpr s d e' [])
         | .stringExpr e' => .stringValue (semanticsStringExpr s d e' [])
         | .intExpr e' => .intValue (semanticsIntExpr s d e' []))
       acc.insert row' 1)
      HashMap.empty
    match s with
    | .bag => result
    | .set => result.setof

end


def r1' : DBRow × Nat := ([.boolValue true, .intValue (some 10), .stringValue "UPPER"],1)
def r2' : DBRow × Nat := ([.boolValue true, .intValue (some 15), .stringValue "lower"],1)
def r3' : DBRow × Nat := ([.boolValue false, .intValue (some 08), .stringValue "Mixed"],1)
def r4' : DBRow × Nat := ([.boolValue false, .intValue (some 30), .stringValue "Mixed"], 1)
def table1 : DBTable := [r1', r2', r3'].toMap


def table2 : DBTable := [r1', r2', r4'].toMap

def d: DatabaseInstance := (HashMap.empty.insert "table1" table1).insert "table2" table2

#eval d

def q1': Query := .filter (BoolExpr.column 0) (.baseTable "table1")
def q2': Query :=
  let project := .project [.stringExpr (.upper (.column 2)), .intExpr (.multiplication (.column 1) (.literal 2))] (.baseTable "table1")
  let filter := .filter (.lsInt (.column 1) (.literal 25)) project
  filter

def q3' : Query := .join (.baseTable "table1") (.baseTable "table2") .full (.intEqual (.column 1) (.column 4))

def q4' : Query := .values [[.boolExpr (.null), .intExpr (.null), .stringExpr (.null)],
                           [.boolExpr (.null), .intExpr (.null), .stringExpr (.null)]]
                          [.sqlType .boolean true, .sqlType .integer true, .sqlType .text true ]

#eval semantics .bag d q1'
#eval semantics .bag d q2'
#eval semantics .bag d q3'
#eval semantics .bag d q4'
#eval semantics .set d q4'


def q:Query :=
  .queryOperation .unionAll
    (.queryOperation .exceptAll q1' q2)
    (.queryOperation .exceptAll q1' q2)
