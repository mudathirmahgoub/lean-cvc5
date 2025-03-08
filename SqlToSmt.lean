import Std.Data.HashMap
import cvc5
import cvc5.Sql

open cvc5 (TermManager Solver)
open Std

structure Env where
  tm: TermManager
  s: Solver
  map: HashMap String cvc5.Term
  semantics : Semantics

def printHashMap (map : HashMap String cvc5.Term) : String :=
  map.fold (fun acc key value =>
    acc ++ s!"{toString key}: {toString value} {toString value.getSort}\n"
  ) ""

instance : ToString Env where
  toString e := printHashMap e.map

instance : ToString (HashMap String cvc5.Term) where
  toString e := printHashMap e


def translateBasetype? (e: Env) (b: Basetype) : Option cvc5.Sort :=
  match b with
  | .bigint => e.tm.getIntegerSort
  | .integer => e.tm.getIntegerSort
  | .boolean => e.tm.getBooleanSort
  | .varchar (_: Nat) => e.tm.getStringSort
  | _ => none

def translateDatatype (e: Env) (d: Datatype) : Option cvc5.Sort :=
  let .datatype base isNullable := d
  let s := translateBasetype? e base
  match isNullable with
  | false => s
  | true => match s with
    | none => none
    | some s => e.tm.mkNullableSort? s


def mkTableSort (e: Env) (tupleSort: cvc5.Sort) : cvc5.Sort :=
  match e.semantics with
  |.bag => e.tm.mkBagSort! tupleSort
  |.set => e.tm.mkSetSort! tupleSort

def declareTable (e: Env) (table: Table) : Env :=
  let sorts := table.columns.map (fun c => translateDatatype e c.datatype)
  let tupleSort := e.tm.mkTupleSort! (sorts.filterMap id)
  let tableSort := mkTableSort e tupleSort
  let tableTerm := e.s.declareFun table.name #[] tableSort
  match tableTerm with
  | none => e
  | some (except, _) => match except with
    | .error _ => e
    | .ok t => { e with map := e.map.insert table.name t }

def translateSchema (e: Env) (d: DatabaseSchema) : Env :=
  d.tables.foldl declareTable e


def translateTableExpr (e: Env) (tableExpr: TableExpr) : Option cvc5.Term :=
  match tableExpr with
  | .baseTable name => e.map[name]?
  | _ => none

def test1 := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e := Env.mk tm s HashMap.empty .bag
  let x := translateDatatype e (.datatype .boolean true)
  let y := tm.mkTupleSort! #[x.get!]
  let tTuple := tm.mkNullableSome! (tm.mkBoolean true)
  let fTuple := tm.mkNullableSome! (tm.mkBoolean false)
  let k := cvc5.Kind.AND
  let lift := tm.mkNullableLift k #[tTuple,fTuple]
  return lift


def schema : DatabaseSchema :=
  { tables := #[
      { name := "users", columns := #[
          { name := "id", datatype := Datatype.datatype Basetype.integer false },
          { name := "name", datatype := Datatype.datatype Basetype.text false },
          { name := "email", datatype := Datatype.datatype Basetype.text false },
          { name := "created_at", datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) false }
        ]
      },
      { name := "posts", columns := #[
          { name := "id", datatype := Datatype.datatype Basetype.integer false },
          { name := "user_id", datatype := Datatype.datatype Basetype.integer true },
          { name := "title", datatype := Datatype.datatype (Basetype.varchar 10) false },
          { name := "content", datatype := Datatype.datatype (Basetype.varchar 20) true },
          { name := "created_at", datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) false }
        ]
      }
    ]
  }

instance : Inhabited Table where
  default := { name := "", columns := #[] }

def test2 (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e := Env.mk tm s HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  return z.map

#eval test2 true
#eval test2 false


def test3 (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e := Env.mk tm s HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let w := translateTableExpr z (.baseTable ("users"))
  return w

#eval test3 true
#eval test3 false
