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


def mkTupleSelect (e: Env) (tupleSort: cvc5.Sort) (t: cvc5.Term) (index: Nat) : cvc5.Term :=
  let datatype := tupleSort.getDatatype
  let constructor := datatype.toOption.get![0]!
  let selectorTerm := constructor[index]!
  let selectorTerm := selectorTerm.getTerm.toOption.get!
  e.tm.mkTerm! .APPLY_SELECTOR #[selectorTerm, t]

def testTupleSelect := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty .bag
  let s := e.tm.mkString! "hello" false
  let t := e.tm.mkTuple! #[e.tm.mkInteger 1, s]
  let s := mkTupleSelect e t.getSort t 1
  let z ← e.s.simplify s false
  return z.fst

#check testTupleSelect
#eval testTupleSelect

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


def translateAnd (e: Env) (needsLifting: Bool) (terms: Array cvc5.Term) : cvc5.Term :=
  if needsLifting then
    let falseTerm := e.tm.mkNullableSome! (e.tm.mkBoolean false)
    let fstIsSome := e.tm.mkNullableIsSome! terms[0]!
    let sndIsSome := e.tm.mkNullableIsSome! terms[1]!
    let fstVal := e.tm.mkNullableVal! terms[0]!
    let sndVal := e.tm.mkNullableVal! terms[1]!
    let fstValFalse := e.tm.mkTerm! .NOT #[fstVal]
    let sndValFalse := e.tm.mkTerm! .NOT #[sndVal]
    let isFirstFalse := e.tm.mkTerm! .AND #[fstIsSome, fstValFalse]
    let isSecondFalse := e.tm.mkTerm! .AND #[sndIsSome, sndValFalse]
    e.tm.mkTerm! .ITE #[isFirstFalse, falseTerm,
                        e.tm.mkTerm! .ITE #[isSecondFalse, falseTerm, e.tm.mkNullableLift! .AND terms]]
  else
    e.tm.mkTerm! .AND terms


def translateOr (e: Env) (needsLifting: Bool) (terms: Array cvc5.Term) : cvc5.Term :=
  if needsLifting then
    let trueTerm := e.tm.mkNullableSome! (e.tm.mkBoolean true)
    let fstIsSome := e.tm.mkNullableIsSome! terms[0]!
    let sndIsSome := e.tm.mkNullableIsSome! terms[1]!
    let fstVal := e.tm.mkNullableVal! terms[0]!
    let sndVal := e.tm.mkNullableVal! terms[1]!
    let isFirstTrue := e.tm.mkTerm! .AND #[fstIsSome, fstVal]
    let isSecondTrue := e.tm.mkTerm! .AND #[sndIsSome, sndVal]
    e.tm.mkTerm! .ITE #[isFirstTrue, trueTerm,
                        e.tm.mkTerm! .ITE #[isSecondTrue, trueTerm, e.tm.mkNullableLift! .OR terms]]
  else
    e.tm.mkTerm! .OR terms


def defineFun (e: Env) : cvc5.Term :=
  let x := e.tm.mkVar e.tm.getIntegerSort "x"
  let one := e.tm.mkInteger 1
  let xPlus1 := e.tm.mkTerm! .ADD #[x.toOption.get!, one]
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[x.toOption.get!]
  e.tm.mkTerm! .LAMBDA #[boundList, xPlus1]


def testDefineFun := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty .bag
  let z := defineFun e
  return z

#eval testDefineFun

mutual
partial def translateTableExpr (e: Env) (tableExpr: TableExpr) : Option cvc5.Term :=
  match tableExpr with
  | .baseTable name => dbg_trace s!" .baseTable name: {name} and e: {e}, e.map[name]: {e.map[name]?}"; e.map[name]?
  | .project exprs query =>  dbg_trace s!" .project exprs:  query: "; translateProject e exprs query
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

partial def translateProject (e: Env) (exprs: Array ScalarExpr) (query: TableExpr) : Option cvc5.Term :=
  let query' := translateTableExpr e query |>.get!
  dbg_trace s!"query': {query'} exprs: {exprs}";
  let tupleSort : cvc5.Sort := match e.semantics with
    | .bag =>  query'.getSort.getBagElementSort!
    | .set =>  query'.getSort.getSetElementSort!
  dbg_trace s!"tupleSort: {tupleSort}";
  let isTableProject := exprs.all (fun x => match x with
    | .column _ => true
    | _ => false)
  dbg_trace s!"isTableProject: {isTableProject}";
  let (projectKind, mapKind) : cvc5.Kind × cvc5.Kind := match e.semantics with
    | .bag => (.TABLE_PROJECT, .BAG_MAP)
    | .set => (.RELATION_PROJECT, .SET_MAP)
  dbg_trace s!"(projectKind, mapKind): {projectKind}, {mapKind}";
  if isTableProject then
  let indices := exprs.map (fun x => match x with
    | .column i => i
    | _ => panic! "not an indexed column")
  dbg_trace s!"indices: {indices}";
  let op := e.tm.mkOpOfIndices projectKind indices |>.toOption.get!
  dbg_trace s!"op: {op}";
  let projection := e.tm.mkTermOfOp op  #[query'] |>.toOption.get!
  projection
  else
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let lambda := translateTupleExpr e exprs t |>.get!
  dbg_trace s!"lambda: {lambda}";
  e.tm.mkTerm! mapKind #[lambda, query']

partial def translateTupleExpr (e: Env) (exprs: Array ScalarExpr) (t : cvc5.Term) : Option cvc5.Term :=
  let terms := exprs.map (fun expr => translateScalarExpr e t expr)
  if terms.any (fun t => t.isNone) then none
  else
  let
  tuple := e.tm.mkTuple! (terms.filterMap id)
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  lambda


partial def translateScalarExpr (e: Env) (t: cvc5.Term) (s: ScalarExpr): Option cvc5.Term :=
  match s with
  | .column index => mkTupleSelect e t.getSort t index
  | .stringLiteral v => e.tm.mkString v |>.toOption
  | .intLiteral v => e.tm.mkInteger v
  | .boolLiteral v => e.tm.mkBoolean v
  | .nullLiteral b => match b with
    | .bigint => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getIntegerSort)
    | .integer => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getIntegerSort)
    | .boolean => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getBooleanSort)
    | .varchar _ => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getStringSort)
    | _ => none
  | .exists tableExpr => translateTableExpr e tableExpr
  | .application op args =>
    let terms := ((args.map (translateScalarExpr e t)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    match op with
    | "=" => e.tm.mkTerm! .EQUAL terms
    | "<>" => e.tm.mkTerm! .DISTINCT terms
    | "+" => liftIfNullable e needsLifting .ADD nullableTerms
    | "-" => liftIfNullable e needsLifting .SUB nullableTerms
    | "*" => liftIfNullable e needsLifting .MULT nullableTerms
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
    | "IS TRUE" => if needsLifting
                   then e.tm.mkNullableVal! nullableTerms[0]!
                   else nullableTerms[0]!
    | "IS NOT TRUE" => if needsLifting
                   then e.tm.mkTerm! .NOT #[(e.tm.mkNullableVal! nullableTerms[0]!)]
                   else e.tm.mkTerm! .NOT #[nullableTerms[0]!]
    | "NOT" => liftIfNullable e needsLifting .NOT nullableTerms
    | "AND" => translateAnd e needsLifting nullableTerms
    | "OR" => translateOr e needsLifting nullableTerms
    | _ => none

end

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


def test4 (simplify: Bool) (value: Bool) (op: String) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty .bag
  let nullLiteral := ScalarExpr.nullLiteral .boolean
  let x := ScalarExpr.boolLiteral value
  let andExpr := ScalarExpr.application op #[nullLiteral, x]
  let query := (e.tm.mkBoolean true)
  let z : Option cvc5.Term := translateScalarExpr e query andExpr
  let z' := z.get!
  if simplify then
    let z'' ← e.s.simplify z' false
    return z''.fst
  else
    return .ok z'



#eval test4 true true "AND"
#eval test4 false true "AND"
#eval test4 true true "OR"
#eval test4 false true "OR"

#eval test4 true false "AND"
#eval test4 false false "AND"
#eval test4 true false "OR"
#eval test4 false false "OR"


def test5 (simplify: Bool) (value: Bool) (op: String) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty .bag
  let x := ScalarExpr.boolLiteral value
  let expr := ScalarExpr.application op #[x]
  let query := (e.tm.mkBoolean true)
  let z : Option cvc5.Term := translateScalarExpr e query expr
  let z' := z.get!
  if simplify then
    let z'' ← e.s.simplify z' false
    return z''.fst
  else
    return .ok z'

#eval test5 false false "NOT"
#eval test5 true false "NOT"
#eval test5 false true "NOT"
#eval test5 true true "NOT"


def testProjection (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .project #[.column 0, .column 1,
  .stringLiteral "hello", .application "+" #[.intLiteral 1, .application "+" #[.column 0, .column 1]]] (.baseTable "posts")
  let w := translateTableExpr z t
  return w

#eval testProjection true
#eval testProjection false
