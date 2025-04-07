-- Abdo: This is the library to include if you decide to use `PlainDateTime`.
--       It handles simple time arithmatic according to the standard.
-- import Std.Time

-- Abdo: should this be an inductive or a structure?
--       consider using `PlainDateTime`. Though, it's more precise (includes nanoseconds)

inductive TimePart where | Year | Month  | Day
  | Hour
  | Minute
  | Second
  deriving Repr

inductive Basetype where
  | boolean
  | text
  | integer
  deriving Repr, BEq

inductive SqlType where
  | sqlType (basetype : Basetype) (isNull : Bool)
  deriving Repr

instance : Inhabited SqlType where
  default := .sqlType .boolean false

structure BaseTable where
  name : String
  columns : List SqlType
  deriving Repr

instance : Inhabited BaseTable where
  default := { name := "", columns := [] }

inductive SQLSemantics where | bag | set


inductive QueryOp where
  | union
  | unionAll
  | intersect
  | intersectAll
  | except
  | exceptAll
  deriving Repr

inductive Join where
  | inner
  | left
  | right
  | full
  deriving Repr

mutual
inductive Query where
  | baseTable (name : String) : Query
  | project (expr: List Expr) (query: Query) : Query
  | join (l: Query) (r: Query) (join : Join) (condition: BoolExpr) : Query
  | filter (condition: BoolExpr) (query: Query) : Query
  | queryOperation (op: QueryOp) (l: Query) (r: Query) : Query
  | values (rows: List (List Expr)) (sqlTypes: List SqlType): Query
  deriving Repr

inductive StringExpr : Type where
  | column (index : Nat) : StringExpr
  | literal (value : String) : StringExpr
  | null : StringExpr
  | case (condition : BoolExpr) (thenExpr elseExpr: StringExpr) : StringExpr
  | upper (a : StringExpr) : StringExpr
  | lower (a : StringExpr) : StringExpr
  | concat (a b : StringExpr) : StringExpr
  | substring (a : StringExpr) (start length : Nat) : StringExpr
  deriving Repr

inductive IntExpr : Type where
  | column (index : Nat) : IntExpr
  | literal (value : Int) : IntExpr
  | null : IntExpr
  | case (condition : BoolExpr) (thenExpr elseExpr: IntExpr) : IntExpr
  | plus (a b : IntExpr) : IntExpr
  | minus (a b : IntExpr) : IntExpr
  | multiplication (a b : IntExpr) : IntExpr
  | division (a b : IntExpr) : IntExpr
  deriving Repr

inductive BoolExpr : Type where
  | column (index : Nat) : BoolExpr
  | null : BoolExpr
  | literal (value : Bool) : BoolExpr
  | exists (Query : Query) : BoolExpr
  | case (condition thenExpr elseExpr: BoolExpr) : BoolExpr
  | stringEqual (a b : StringExpr) : BoolExpr
  | intEqual (a b : IntExpr) : BoolExpr
  | boolEqual (a b : BoolExpr) : BoolExpr
  | and (a b : BoolExpr) : BoolExpr
  | or (a b : BoolExpr) : BoolExpr
  | not (a : BoolExpr) : BoolExpr
  | isNullString (a : StringExpr) : BoolExpr
  | isNotNullString (a : StringExpr) : BoolExpr
  | isNullInt (a : IntExpr) : BoolExpr
  | isNotNullInt (a : IntExpr) : BoolExpr
  | isNullBool (a : BoolExpr) : BoolExpr
  | isNotNullBool (a : BoolExpr) : BoolExpr
  | isTrue (a : BoolExpr) : BoolExpr
  | isNotTrue (a : BoolExpr) : BoolExpr
  | lsInt (a b : IntExpr) : BoolExpr
  | leqInt (a b : IntExpr) : BoolExpr
  | gtInt (a b : IntExpr) : BoolExpr
  | geqInt (a b : IntExpr) : BoolExpr
  | lsString (a b : StringExpr) : BoolExpr
  | leqString (a b : StringExpr) : BoolExpr
  | gtString (a b : StringExpr) : BoolExpr
  | geqString (a b : StringExpr) : BoolExpr
  deriving Repr

inductive Expr : Type where
  | boolExpr (e: BoolExpr) : Expr
  | stringExpr (e : StringExpr) : Expr
  | intExpr (e: IntExpr) : Expr
  deriving Repr

end

inductive Constraint where
  | unique (name baseTable : String) (columns :List Nat) : Constraint
  | primaryKey  (name baseTable : String) (columns :List Nat) : Constraint
  | foreignKey (name child parent : String) (childColumns parentColumns :List Nat) : Constraint
  | check (name baseTable : String) (expr :Expr) : Constraint
   deriving Repr

structure DatabaseSchema where
  baseTables : List BaseTable
  constraints : List Constraint := []
  deriving Repr


instance : ToString Basetype where
  toString
    | .boolean => "boolean"
    | .text => s!"text"
    | .integer => s!"integer"

instance : ToString Expr where
  toString
    | _ => s!"Expr not supported yet"


instance : ToString (List Expr) where
  toString arr :=
    "[" ++ String.intercalate ", " (arr.map toString) ++ "]"


partial def columnsMatch (xs ys : List SqlType) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (_, []) => false
  | ([], _) => false
  | (.sqlType a _::as, .sqlType b _::bs) => a == b && columnsMatch as bs

partial def liftTypes (xs ys : List SqlType) : List SqlType:=
match (xs, ys) with
  | ([], []) => []
  | (.sqlType a1 b1::as, .sqlType a2 b2::bs) =>
    if a1 != a2 then panic! "Types do not match"
    else if b1 == b2 then .sqlType a1 b1 :: liftTypes as bs
    else .sqlType a1 true :: liftTypes as bs
  | _ => panic! "Types do not match"

mutual

partial def checkQuery (d : DatabaseSchema) (q : Query) : Bool × List SqlType :=
  match q with
| .baseTable name =>
  match d.baseTables.find? (fun t => t.name == name) with
  | some t => (true, t.columns)
  | none => (false, [])
| .project exprs query =>
  let (v, columns) := checkQuery d query
  if v == false then (false, [])
  else
    let types := exprs.map (fun expr => checkExpr d columns expr)
    if types.any (fun (x,_) => !x) then (false, [])
    else
      let sqlTypes := types.map (fun (_, t) => t)
      (true, sqlTypes)
| .filter condition query =>
  let (v, columns) := checkQuery d query
  if v == false then (false, [])
  else
    let (v, t) := checkBoolExpr d columns condition
    if v == false then (false, [])
    else (true, columns)
| .queryOperation op l r =>
  let (v1, columns1) := checkQuery d l
  let (v2, columns2) := checkQuery d r
  if v1 == false || v2 == false then (false, [])
  else
    if columnsMatch columns1 columns2 then (true, liftTypes columns1 columns2)
    else (false, [])
| .join l r join condition =>
  let (v1, columns1) := checkQuery d l
  let (v2, columns2) := checkQuery d r
  if v1 == false || v2 == false then (false, [])
  else
    let columns := columns1 ++ columns2
    let (v, t) := checkBoolExpr d columns condition
    if v == false then (false, [])
    else (true, columns)
| .values rows columns =>
  let results : List (List (Bool × SqlType)) := rows.map (fun row =>
      row.map (fun expr => checkExpr d columns expr))
  if results.any (fun x => x.any (fun (y, _) => !y)) then
    (false, [])
  else
    let types := results.map (fun row => row.map (fun (_, t) => t))
    if types.any (fun x => !columnsMatch x columns) then
      (false, [])
    else
      let ret := types.foldl (fun acc x => liftTypes acc x) columns
      (true, ret)

partial def checkExpr (d : DatabaseSchema) (columns : List SqlType) (expr : Expr) : Bool × SqlType :=
  match expr with
  | .boolExpr e => checkBoolExpr d columns e
  | .stringExpr e => checkStringExpr d columns e
  | .intExpr e => checkIntExpr d columns e

partial def checkBoolExpr (d : DatabaseSchema) (columns : List SqlType) (expr : BoolExpr) : Bool × SqlType :=
  match expr with
  | .column index =>
    if index < columns.length then (false, .sqlType .boolean false)
    else match columns.get! index with
    | .sqlType .boolean x => (true, .sqlType .boolean x)
    | _ => (false, .sqlType .boolean false)
  | .null => (true, .sqlType .boolean true)
  | .literal _ => (true, .sqlType .boolean false)
  | .exists query =>
    let (v, _) := checkQuery d query
    (v, .sqlType .boolean false)
  | .case condition thenExpr elseExpr =>
    let (v1, t1) := checkBoolExpr d columns condition
    let (v2, t2) := checkBoolExpr d columns thenExpr
    let (v3, t3) := checkBoolExpr d columns elseExpr
    if v1 && v2 && v3 then (true, t2) -- fix this
    else (false, .sqlType .boolean false)
  | .stringEqual a b =>
    let (v1, t1) := checkStringExpr d columns a
    let (v2, t2) := checkStringExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .intEqual a b =>
    let (v1, t1) := checkIntExpr d columns a
    let (v2, t2) := checkIntExpr d columns b
    if v1 && v2  then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .boolEqual a b =>
    let (v1, t1) := checkBoolExpr d columns a
    let (v2, t2) := checkBoolExpr d columns b
    if v1 && v2  then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .and a b =>
    let (v1, t1) := checkBoolExpr d columns a
    let (v2, t2) := checkBoolExpr d columns b
    if v1 && v2 then (true, t1)
    else (false, .sqlType .boolean false)
  | .or a b =>
    let (v1, t1) := checkBoolExpr d columns a
    let (v2, t2) := checkBoolExpr d columns b
    if v1 && v2 then (true, t1)
    else (false, .sqlType .boolean false)
  | .not a =>
    let (v, t) := checkBoolExpr d columns a
    if v then (true, t)
    else (false, .sqlType .boolean false)
  | .isNullString a =>
    let (v, _) := checkStringExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isNotNullString a =>
    let (v, _) := checkStringExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isNullInt a =>
    let (v, _) := checkIntExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isNotNullInt a =>
    let (v, _) := checkIntExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isNullBool a =>
    let (v, _) := checkBoolExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isNotNullBool a =>
    let (v, _) := checkBoolExpr d columns a
    if v then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .isTrue a =>
    let (v, t) := checkBoolExpr d columns a
    if v && t == .sqlType .boolean false then (true, t)
    else (false, .sqlType .boolean false)
  | .isNotTrue a =>
    let (v, t) := checkBoolExpr d columns a
    if v && t == .sqlType .boolean false then (true, t)
    else (false, .sqlType .boolean false)
  | .lsInt a b =>
    let (v1, t1) := checkIntExpr d columns a
    let (v2, t2) := checkIntExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .leqInt a b =>
    let (v1, t1) := checkIntExpr d columns a
    let (v2, t2) := checkIntExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .gtInt a b =>
    let (v1, t1) := checkIntExpr d columns a
    let (v2, t2) := checkIntExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .geqInt a b =>
    let (v1, t1) := checkIntExpr d columns a
    let (v2, t2) := checkIntExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .lsString a b =>
    let (v1, t1) := checkStringExpr d columns a
    let (v2, t2) := checkStringExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .leqString a b =>
    let (v1, t1) := checkStringExpr d columns a
    let (v2, t2) := checkStringExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .gtString a b =>
    let (v1, t1) := checkStringExpr d columns a
    let (v2, t2) := checkStringExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)
  | .geqString a b =>
    let (v1, t1) := checkStringExpr d columns a
    let (v2, t2) := checkStringExpr d columns b
    if v1 && v2 then (true, .sqlType .boolean false)
    else (false, .sqlType .boolean false)

partial def checkIntExpr (d : DatabaseSchema) (columns : List SqlType) (expr : IntExpr) : Bool × SqlType :=
  sorry

partial def checkStringExpr (d : DatabaseSchema) (columns : List SqlType) (expr : StringExpr) : Bool × SqlType :=
  sorry

end
