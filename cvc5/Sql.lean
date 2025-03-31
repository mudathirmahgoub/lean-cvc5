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
  | bit (size: Nat)
  | boolean
  | varchar (size: Nat)
  | integer
  deriving Repr

inductive SqlType where
  | sqlType (basetype : Basetype) (isNull : Bool)
  deriving Repr


structure Column where
  index : Nat
  sqlType : SqlType
  deriving Repr

structure BaseTable where
  name : String
  columns : List Column
  deriving Repr


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
  | values (rows: List (List Expr)) : Query
  deriving Repr

inductive StringExpr : Type where
  | column (index : Nat) : StringExpr
  | stringLiteral (value : String) : StringExpr
  | nullString : StringExpr
  | case (condition : BoolExpr) (thenExpr elseExpr: StringExpr) : StringExpr
  | upper (a : StringExpr) : StringExpr
  | lower (a : StringExpr) : StringExpr
  | concat (a b : StringExpr) : StringExpr
  | substring (a : StringExpr) (start length : Nat) : StringExpr
  deriving Repr

inductive IntExpr : Type where
  | column (index : Nat) : IntExpr
  | intLiteral (value : Int) : IntExpr
  | nullInt : IntExpr
  | case (condition : BoolExpr) (thenExpr elseExpr: IntExpr) : IntExpr
  | plus (a b : IntExpr) : IntExpr
  | minus (a b : IntExpr) : IntExpr
  | multiplication (a b : IntExpr) : IntExpr
  | division (a b : IntExpr) : IntExpr
  deriving Repr

inductive BoolExpr : Type where
  | column (index : Nat) : BoolExpr
  | nullBool : BoolExpr
  | boolLiteral (value : Bool) : BoolExpr
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
    | .bit size => s!"bit({size})"
    | .boolean => "boolean"
    | .varchar size => s!"varchar({size})"
    | .integer => s!"integer"

instance : ToString Expr where
  toString
    | _ => s!"Expr not supported yet"


instance : ToString (List Expr) where
  toString arr :=
    "[" ++ String.intercalate ", " (arr.map toString) ++ "]"


def sqlType (e : Expr) : SqlType :=
match e with
| .boolExpr _ => SqlType.sqlType Basetype.boolean true
| .stringExpr _ => SqlType.sqlType (Basetype.varchar 255) true
| .intExpr _ => SqlType.sqlType Basetype.integer true
