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
  | bigint
  | bigserial
  | bit (size: Nat)
  | bitVarying (size: Nat)
  | boolean
  | box
  | bytea
  | character (size: Nat)
  | varchar (size: Nat)
  | cidr
  | circle
  | date
  | doublePrecision
  | inet
  | integer
  | interval (fields : List TimePart) (precision: Nat)
  | json
  | jsonb
  | line
  | lseg
  | macaddr
  | macaddr8
  | money
  | numeric (precision significand: Nat)
  | path
  | pg_lsn
  | pg_snapshot
  | point
  | polygon
  | real
  | smallint
  | smallserial
  | serial
  | text
  | timeWithoutTimeZone (precision : Nat)
  | timeWithTimeZone (precision : Nat)
  | timestampWithoutTimeZone (precision : Nat)
  | timestampWithTimeZone (precision : Nat)
  | tsQuery
  | tsvector
  | txid_snapshot
  | uuid
  | xml
  deriving Repr

inductive Datatype where
  | datatype (basetype : Basetype) (isNull : Bool)
  deriving Repr


structure Column where
  index : Nat
  datatype : Datatype
  deriving Repr

structure BaseTable where
  name : String
  columns : Array Column
  deriving Repr


inductive Semantics where | bag | set


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
  | project (expr: Array Expr) (query: Query) : Query
  | join (l: Query) (r: Query) (join : Join) (condition: Expr) : Query
  | filter (condition: Expr) (query: Query) : Query
  | queryOperation (op: QueryOp) (l: Query) (r: Query) : Query
  | values (rows: Array (Array Expr)) (types: Array Datatype) : Query
  deriving Repr

inductive Expr : Type where
  | column (index : Nat) : Expr
  | stringLiteral (value : String) : Expr
  | intLiteral (value : Int) : Expr
  | boolLiteral (value : Bool) : Expr
  | nullLiteral (type : Basetype) : Expr
  | exists (Query : Query) : Expr
  | case (condition thenExpr elseExpr: Expr) : Expr
  | application (function : String) (args : Array Expr) : Expr
  deriving Repr

end

inductive Constraint where
  | unique (name baseTable : String) (columns :Array Nat) : Constraint
  | primaryKey  (name baseTable : String) (columns :Array Nat) : Constraint
  | foreignKey (name child parent : String) (childColumns parentColumns :Array Nat) : Constraint
  | check (name baseTable : String) (expr :Expr) : Constraint
   deriving Repr

structure DatabaseSchema where
  baseTables : Array BaseTable
  constraints : Array Constraint := #[]
  deriving Repr


instance : ToString Basetype where
  toString
    | .bigint => "bigint"
    | .bigserial => "bigserial"
    | .bit size => s!"bit({size})"
    | .bitVarying size => s!"bit varying({size})"
    | .boolean => "boolean"
    | .box => "box"
    | .bytea => "bytea"
    | .character size => s!"character({size})"
    | .varchar size => s!"varchar({size})"
    | .cidr => "cidr"
    | .circle => "circle"
    | .date => "date"
    | _ => s!"sql type"

instance : ToString Expr where
  toString
    | .column index => s!"column({index})"
    | .stringLiteral value => s!"stringLiteral(\"{value}\")"
    | .intLiteral value => s!"intLiteral({value})"
    | .boolLiteral value => s!"boolLiteral({value})"
    | .nullLiteral type => s!"nullLiteral({type})"
    | _ => s!"not supported yet"


instance : ToString (Array Expr) where
  toString arr :=
    "[" ++ String.intercalate ", " (arr.toList.map toString) ++ "]"
