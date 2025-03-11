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


def isIntegerOrNullableInteger (t: cvc5.Term) : Bool :=
  t.getSort.isInteger ||
  (t.getSort.isNullable && t.getSort.getNullableElementSort!.isInteger)


def liftIfNullable (e: Env) (needsLifting: Bool) (k: cvc5.Kind) (terms: Array cvc5.Term) : cvc5.Term :=
  if needsLifting then e.tm.mkNullableLift! k terms
  else e.tm.mkTerm! k terms

mutual
partial def translateTableExpr (e: Env) (tableExpr: TableExpr) : Option cvc5.Term :=
  match tableExpr with
  | .baseTable name => e.map[name]?
  | .tableOperation op l r => translateTableOperation e op l r
  | _ => none


partial def translateTableOperation (e: Env) (op: TableOp) (l r: TableExpr) : Option cvc5.Term :=
  let l' := translateTableExpr e l
  let r' := translateTableExpr e r
  match op, e.semantics with
  | .union, .bag => e.tm.mkTerm! .BAG_SETOF #[(e.tm.mkTerm! .BAG_UNION_DISJOINT  #[l'.get!, r'.get!])]
  | .unionAll,.bag => e.tm.mkTerm! .BAG_UNION_DISJOINT  #[l'.get!, r'.get!]
  | .union, .set => e.tm.mkTerm! .SET_UNION  #[l'.get!, r'.get!]
  | .unionAll,.set => e.tm.mkTerm! .SET_UNION  #[l'.get!, r'.get!]
  | .minus, .bag => e.tm.mkTerm! .BAG_DIFFERENCE_SUBTRACT  #[e.tm.mkTerm! .BAG_SETOF #[l'.get!], r'.get!]
  | .minusAll,.bag => e.tm.mkTerm! .BAG_DIFFERENCE_SUBTRACT  #[l'.get!, r'.get!]
  | .minus, .set => e.tm.mkTerm! .SET_MINUS  #[l'.get!, r'.get!]
  | .minusAll,.set => e.tm.mkTerm! .SET_MINUS  #[l'.get!, r'.get!]
  | .intersect,.bag => e.tm.mkTerm! .BAG_SETOF #[(e.tm.mkTerm! .BAG_INTER_MIN  #[l'.get!, r'.get!])]
  | .intersectAll, .bag => e.tm.mkTerm! .BAG_INTER_MIN  #[l'.get!, r'.get!]
  | .intersect, .set => e.tm.mkTerm! .SET_INTER  #[l'.get!, r'.get!]
  | .intersectAll, .set => e.tm.mkTerm! .SET_INTER  #[l'.get!, r'.get!]

end

partial def traslateScalarExpr (e: Env) (s: ScalarExpr) : Option cvc5.Term :=
  match s with
  | .column name => e.map[name]?
  --| .stringLiteral v => e.tm.mkString v
  | .intLiteral v => e.tm.mkInteger v
  | .boolLiteral v => e.tm.mkBoolean v
  | .exists tableExpr => translateTableExpr e tableExpr
  | .application op args =>
    let terms := ((args.map (traslateScalarExpr e)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    match op with
    | "=" => e.tm.mkTerm! .EQUAL terms
    | "<>" => e.tm.mkTerm! .DISTINCT terms
    | "+" => liftIfNullable e needsLifting .ADD nullableTerms
    | "-" => liftIfNullable e needsLifting .SUB nullableTerms
    | "*" => liftIfNullable e needsLifting .DIVISION nullableTerms
    | ">" => if isIntegerOrNullableInteger nullableTerms[0]!
             then liftIfNullable e needsLifting .GT nullableTerms
             else liftIfNullable e needsLifting .STRING_LT #[nullableTerms[1]!, nullableTerms[0]!]
    | "<" => if isIntegerOrNullableInteger nullableTerms[0]!
             then liftIfNullable e needsLifting .LT nullableTerms
             else liftIfNullable e needsLifting .STRING_LT nullableTerms
    | ">=" => if isIntegerOrNullableInteger nullableTerms[0]!
              then liftIfNullable e needsLifting .GEQ nullableTerms
              else liftIfNullable e needsLifting .STRING_LEQ #[nullableTerms[1]!, nullableTerms[0]!]
    | "<=" => if isIntegerOrNullableInteger nullableTerms[0]!
              then liftIfNullable e needsLifting .LEQ nullableTerms
              else liftIfNullable e needsLifting .STRING_LEQ nullableTerms
    | "UPPER" => liftIfNullable e needsLifting .STRING_TO_UPPER nullableTerms
    | "||" => liftIfNullable e needsLifting .STRING_CONCAT nullableTerms
    | "IS NULL" => if needsLifting
                   then e.tm.mkNullableIsNull! nullableTerms[0]!
                   else e.tm.mkBoolean false
    | "IS NOT NULL" => if needsLifting
                   then e.tm.mkNullableIsSome! nullableTerms[0]!
                   else e.tm.mkBoolean true
    | _ => none
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
  let t : TableExpr := .tableOperation .unionAll  (.baseTable "users") (.baseTable "users")
  let w := translateTableExpr z t
  return w

#eval test3 true
#eval test3 false
