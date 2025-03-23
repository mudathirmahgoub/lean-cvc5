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

structure DatabaseSchema where
  baseTables : Array BaseTable
  deriving Repr

inductive Semantics where | bag | set


inductive QueryOp where
  | union
  | unionAll
  | intersect
  | intersectAll
  | minus
  | minusAll
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
  | project (expr: Array ScalarExpr) (query: Query) : Query
  | join (l: Query) (r: Query) (join : Join) (condition: ScalarExpr) : Query
  | filter (condition: ScalarExpr) (query: Query) : Query
  | queryOperation (op: QueryOp) (l: Query) (r: Query) : Query
  | values (rows: Array (Array ScalarExpr)) (types: Array Datatype) : Query
  deriving Repr

inductive ScalarExpr : Type where
  | column (index : Nat) : ScalarExpr
  | stringLiteral (value : String) : ScalarExpr
  | intLiteral (value : Int) : ScalarExpr
  | boolLiteral (value : Bool) : ScalarExpr
  | nullLiteral (type : Basetype) : ScalarExpr
  | exists (Query : Query) : ScalarExpr
  | application (function : String) (args : Array ScalarExpr) : ScalarExpr
  deriving Repr

end



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

instance : ToString ScalarExpr where
  toString
    | .column index => s!"column({index})"
    | .stringLiteral value => s!"stringLiteral(\"{value}\")"
    | .intLiteral value => s!"intLiteral({value})"
    | .boolLiteral value => s!"boolLiteral({value})"
    | .nullLiteral type => s!"nullLiteral({type})"
    | _ => s!"not supported yet"


instance : ToString (Array ScalarExpr) where
  toString arr :=
    "[" ++ String.intercalate ", " (arr.toList.map toString) ++ "]"
