-- Abdo: This is the library to include if you decide to use `PlainDateTime`.
--       It handles simple time arithmatic according to the standard.
-- import Std.Time

-- Abdo: should this be an inductive or a structure?
--       consider using `PlainDateTime`. Though, it's more precise (includes nanoseconds)

inductive TimePart where
  | Year
  | Month
  | Day
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
  | tsTableExpr
  | tsvector
  | txid_snapshot
  | uuid
  | xml
  deriving Repr

inductive Datatype where
  | datatype (basetype : Basetype) (isNull : Bool)
  deriving Repr


structure Column where
  name : String
  datatype : Datatype
  deriving Repr

structure Table where
  name : String
  columns : Array Column
  deriving Repr

structure DatabaseSchema where
  tables : Array Table
  deriving Repr

def DatabaseSchema.getTable? (schema : DatabaseSchema) (tableName : String) : Option Table :=
  schema.tables.find? (fun t => t.name == tableName)


inductive Semantics where
  | bag : Semantics
  | set : Semantics


inductive TableOp where
  | union
  | unionAll
  | intersect
  | intersectAll
  | minus
  | minusAll
  deriving Repr

mutual
inductive TableExpr where
  | baseTable (name : String) : TableExpr
  | project (expr: ScalarExpr) (query: TableExpr) : TableExpr
  | join (l: TableExpr) (r: TableExpr) (condition: ScalarExpr) : TableExpr
  | filter (query: TableExpr) (condition: ScalarExpr) : TableExpr
  | tableOperation (op: TableOp) (l: TableExpr) (r: TableExpr) : TableExpr
  | values (rows: Array RowExpr) : TableExpr

inductive ScalarExpr : Type where
  | column (name : String) : ScalarExpr
  | stringLiteral (value : String) : ScalarExpr
  | intLiteral (value : Int) : ScalarExpr
  | boolLiteral (value : Bool) : ScalarExpr
  | nullLiteral (type : Basetype) : ScalarExpr
  | exists (tableExpr : TableExpr) : ScalarExpr
  | application (function : String) (args : Array ScalarExpr) : ScalarExpr
  deriving Repr

inductive RowExpr : Type where
  | row (elements : Array ScalarExpr) : RowExpr
  deriving Repr
end
