import Std.Data.HashMap
import cvc5
import cvc5.Sql

open cvc5 (TermManager Solver Kind)
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


def getMapKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => .BAG_MAP
  | .set => .SET_MAP

def getProjectKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => .TABLE_PROJECT
  | .set => .RELATION_PROJECT

def getFilterKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => .BAG_FILTER
  | .set => .SET_FILTER

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
--#eval testTupleSelect

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

--#eval testDefineFun

def mkEmptyTable (e: Env) (s: cvc5.Sort): cvc5.Term :=
  match e.semantics with
  | .bag => e.tm.mkEmptyBag! s
  | .set => e.tm.mkEmptySet! s

def mkSingleton (e: Env) (tuple: cvc5.Term) : cvc5.Term :=
  match e.semantics with
  | .bag => e.tm.mkTerm! .BAG_MAKE #[tuple, e.tm.mkInteger 1]
  | .set => e.tm.mkTerm! .SET_SINGLETON #[tuple]

def getIndices (n : Nat) : Array Nat :=
  Array.mkArray n 0 |>.mapIdx (fun i _ => i)

--#eval getIndices 5

def mkNullableSort (e: Env) (s: cvc5.Sort) : cvc5.Sort :=
  if s.isNullable then s else e.tm.mkNullableSort! s

def mkLeft (e: Env) (a product: cvc5.Term) : cvc5.Term :=
  let (aSort, productSort, projectKind, differenceKind , mapKind) := match e.semantics with
    | .bag => (a.getSort.getBagElementSort!, product.getSort.getBagElementSort!, Kind.TABLE_PROJECT, Kind.BAG_DIFFERENCE_REMOVE, Kind.BAG_MAP)
    | .set => (a.getSort.getSetElementSort!, product.getSort.getSetElementSort!, Kind.RELATION_PROJECT, Kind.SET_MINUS, Kind.SET_MAP)
  let (aTupleLength, productTupleLength) := (aSort.getTupleLength!.toNat, productSort.getTupleLength!.toNat)
  let aIndices := getIndices aTupleLength
-- dbg_trace s!"aIndices: {aIndices}";
  let op := e.tm.mkOpOfIndices projectKind aIndices |>.toOption.get!
-- dbg_trace s!"op: {op}";
  let projection := e.tm.mkTermOfOp op #[product] |>.toOption.get!
-- dbg_trace s!"projection: {projection}";
  let difference := e.tm.mkTerm! differenceKind #[a, projection]
-- dbg_trace s!"difference: {difference}";
  let aVar := e.tm.mkVar aSort "t" |>.toOption.get!
-- dbg_trace s!"t: {t}";
  let aTerms := aIndices.map (fun i => mkTupleSelect e aSort aVar i)
-- dbg_trace s!"aTerms: {aTerms}";
  let bIndices := getIndices (productTupleLength - aTupleLength) |>.map (fun i => i + aTupleLength)
-- dbg_trace s!"bIndices: {bIndices}";
  let productSorts := productSort.getTupleSorts!.map (fun s => mkNullableSort e s)
-- dbg_trace s!"productSorts: {productSorts}";
  let bTerms := bIndices.map (fun i => e.tm.mkNullableNull productSorts[i]! |>.toOption.get!)
-- dbg_trace s!"bTerms: {bTerms}";
  let tuple := e.tm.mkTuple! (aTerms ++ bTerms)
-- dbg_trace s!"tuple: {tuple}";
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[aVar]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  -- dbg_trace s!"lambda: {lambda}";
  let map := e.tm.mkTerm! mapKind #[lambda, difference]
  -- dbg_trace s!"map: {map}";
  map


def liftTupleElements (e: Env) (t query: cvc5.Term) (targetSorts tupleSorts: Array cvc5.Sort) : cvc5.Term :=
  let zip := targetSorts.zip tupleSorts
  let tupleSort := t.getSort
  let terms := zip.mapIdx (fun i (targetSort, querySort) =>
    let term := mkTupleSelect e tupleSort t i
    if targetSort == querySort then term
    else e.tm.mkNullableSome! term)
  let tuple := e.tm.mkTuple terms |>.toOption.get!
--dbg_trace s!"tuple: {tuple}";
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  e.tm.mkTerm! (getMapKind e) #[lambda, query]


def mkTableOp (e: Env) (op: cvc5.Kind) (a b: cvc5.Term) : cvc5.Term :=
  let (aElementSort, bElementSort, mapKind) := match e.semantics with
    | .bag => (a.getSort.getBagElementSort!, b.getSort.getBagElementSort!, Kind.BAG_MAP)
    | .set => (a.getSort.getSetElementSort!, b.getSort.getSetElementSort!, Kind.SET_MAP)
--dbg_trace s!"op: {op}";
  let aSorts := aElementSort.getTupleSorts!
  let bSorts := bElementSort.getTupleSorts!
  if aSorts == bSorts then
  let ret := e.tm.mkTerm! op #[a, b]
  ret
  else
  let zip := aSorts.zip bSorts
--dbg_trace s!"zip: {zip}";
  let sorts := zip.map (fun (aSort, bSort) => if aSort == bSort then aSort
                        else if aSort.isNullable then aSort else bSort)
  let aVar := e.tm.mkVar aElementSort "t" |>.toOption.get!
  let bVar := e.tm.mkVar bElementSort "t" |>.toOption.get!
  let a' := if aSorts == sorts then a else liftTupleElements e aVar a sorts aSorts
  let b' := if bSorts == sorts then b else liftTupleElements e bVar b sorts bSorts
--dbg_trace s!"aSorts == sorts: {aSorts == sorts}";
--dbg_trace s!"bSorts == sorts: {bSorts == sorts}";
--dbg_trace s!"a': {a'}";
--dbg_trace s!"b': {b'}";
  e.tm.mkTerm! op #[a', b']


mutual
partial def translateTableExpr (e: Env) (tableExpr: TableExpr) : Option cvc5.Term :=
  match tableExpr with
  | .baseTable name =>
    -- dbg_trace s!" .baseTable name: {name} and e: {e}, e.map[name]: {e.map[name]?}";
    e.map[name]?
  | .project exprs query =>
    -- dbg_trace s!" .project exprs:  query: ";
    translateProject e exprs query
  | .join l r j c => translateJoin e l r j c
  | .filter condition query  => translateFilter e condition query
  | .tableOperation op l r => translateTableOperation e op l r
  | .values rows types => translateValues e rows types

partial def translateValues (e: Env) (rows: Array (Array ScalarExpr)) (types: Array Datatype): Option cvc5.Term :=
  let tuples := rows.map (fun row =>
  let elements := row.map (fun expr => translateScalarExpr e (e.tm.mkInteger 0) expr) |>.filterMap id
  e.tm.mkTuple! elements)
  let sorts := types.map (fun t => translateDatatype e t) |>.filterMap id
  let tupleSort := e.tm.mkTupleSort! sorts
  let tableSort := mkTableSort e tupleSort
  let emptyTable := mkEmptyTable e tableSort
  let unionKind := match e.semantics with
    | .bag => Kind.BAG_UNION_DISJOINT
    | .set => Kind.SET_UNION
  tuples.foldl (fun table tuple =>
    let singleton := mkSingleton e tuple
    e.tm.mkTerm! unionKind #[table.get!, singleton]
  ) emptyTable

partial def translateFilter (e: Env) (condition: ScalarExpr) (query: TableExpr) : Option cvc5.Term :=
  let query' := translateTableExpr e query |>.get!
  let (tupleSort,filterKind) := match e.semantics with
    | .bag =>  (query'.getSort.getBagElementSort!, Kind.BAG_FILTER)
    | .set =>  (query'.getSort.getSetElementSort!, Kind.SET_FILTER)
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let condition' := translateScalarExpr e t condition |>.get!
  let predicate := if condition'.getSort.isNullable
                then
                let isSome := e.tm.mkNullableIsSome! condition'
                let val := e.tm.mkNullableVal! condition'
                e.tm.mkTerm! .AND #[isSome, val]
                else condition'
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, predicate]
  e.tm.mkTerm! filterKind #[lambda, query']

partial def translateTableOperation (e: Env) (op: TableOp) (l r: TableExpr) : Option cvc5.Term :=
  let l' := translateTableExpr e l
  let r' := translateTableExpr e r
  match op, e.semantics with
  | .union, .bag => e.tm.mkTerm! .BAG_SETOF #[(e.tm.mkTerm! .BAG_UNION_DISJOINT  #[l'.get!, r'.get!])]
  | .unionAll,.bag => mkTableOp e .BAG_UNION_DISJOINT  l'.get! r'.get!
  | .union, .set => mkTableOp e .SET_UNION  l'.get! r'.get!
  | .unionAll,.set => mkTableOp e .SET_UNION  l'.get! r'.get!
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
--dbg_trace s!"query': {query'} exprs: {exprs}";
  let (tupleSort,projectKind, mapKind) := match e.semantics with
    | .bag =>  (query'.getSort.getBagElementSort!, Kind.TABLE_PROJECT, Kind.BAG_MAP)
    | .set =>  (query'.getSort.getSetElementSort!, Kind.RELATION_PROJECT, Kind.SET_MAP)
--dbg_trace s!"tupleSort: {tupleSort}";
  let isTableProject := exprs.all (fun x => match x with
    | .column _ => true
    | _ => false)
--dbg_trace s!"isTableProject: {isTableProject}";
--dbg_trace s!"(projectKind, mapKind): {projectKind}, {mapKind}";
  if isTableProject then
  let indices := exprs.map (fun x => match x with
    | .column i => i
    | _ => panic! "not an indexed column")
--dbg_trace s!"indices: {indices}";
  let op := e.tm.mkOpOfIndices projectKind indices |>.toOption.get!
--dbg_trace s!"op: {op}";
--dbg_trace s!"query: {repr query}";
--dbg_trace s!"query': {query'}";
--dbg_trace s!"query: {query'.getSort} I am here";
  let projection := e.tm.mkTermOfOp op  #[query'] |>.toOption.get!
--dbg_trace s!"projection: {projection}";
  projection
  else
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let lambda := translateTupleExpr e exprs t |>.get!
--dbg_trace s!"lambda: {lambda}";
  e.tm.mkTerm! mapKind #[lambda, query']

partial def translateJoin (e: Env) (l: TableExpr) (r: TableExpr) (join: Join) (condition: ScalarExpr) : Option cvc5.Term :=
  let l' := translateTableExpr e l |>.get!
  let r' := translateTableExpr e r |>.get!
  let (productKind, filterKind, unionKind) := match e.semantics with
    | .bag => (Kind.TABLE_PRODUCT, Kind.BAG_FILTER, Kind.BAG_UNION_DISJOINT)
    | .set => (Kind.RELATION_PRODUCT, Kind.SET_FILTER, Kind.SET_UNION)
  let product := e.tm.mkTerm! productKind #[l', r']
  let tupleSort := match e.semantics with
    | .bag => product.getSort.getBagElementSort!
    | .set => product.getSort.getSetElementSort!
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let condition' := translateScalarExpr e t condition |>.get!
  -- let simplified := e.s.simplifyTerm condition' false |>.toOption.get!
  -- let value := simplified.getBooleanValue!
  -- let product' :=
  -- if value then product
  -- else
  let predicate := if condition'.getSort.isNullable
                then
                let isSome := e.tm.mkNullableIsSome! condition'
                let val := e.tm.mkNullableVal! condition'
                e.tm.mkTerm! .AND #[isSome, val]
                else condition'
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, predicate]
  let product' := e.tm.mkTerm! filterKind #[lambda, product]
  match join with
  | .inner => product'
  | .left =>
    let left := mkLeft e l' product'
  --dbg_trace s!"left: {left}";
    -- let join := e.tm.mkTerm! unionKind #[product', left]
    let join := mkTableOp e unionKind product' left
    join
  | .right => none
  | .full => none


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
          { name := "id", datatype := Datatype.datatype Basetype.integer true },
          { name := "name", datatype := Datatype.datatype Basetype.integer true },
          { name := "email", datatype := Datatype.datatype Basetype.text true },
          { name := "created_at", datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) true }
        ]
      },
      { name := "posts", columns := #[
          { name := "id", datatype := Datatype.datatype Basetype.integer false },
          { name := "user_id", datatype := Datatype.datatype Basetype.integer false },
          { name := "title", datatype := Datatype.datatype (Basetype.varchar 10) true },
          { name := "content", datatype := Datatype.datatype (Basetype.varchar 20) true },
          { name := "created_at", datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) true }
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

--#eval test2 true
--#eval test2 false


def test3 (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e := Env.mk tm s HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .tableOperation .unionAll  (.baseTable "users") (.baseTable "users")
  let w := translateTableExpr z t
  return w

--#eval test3 true
--#eval test3 false


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



--#eval test4 true true "AND"
--#eval test4 false true "AND"
--#eval test4 true true "OR"
--#eval test4 false true "OR"

--#eval test4 true false "AND"
--#eval test4 false false "AND"
--#eval test4 true false "OR"
--#eval test4 false false "OR"


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

--#eval test5 false false "NOT"
--#eval test5 true false "NOT"
--#eval test5 false true "NOT"
--#eval test5 true true "NOT"


def testValues (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .values #[#[.intLiteral 1, .stringLiteral "hello", .stringLiteral "world", .intLiteral 1],
                                #[.intLiteral 2, .stringLiteral "hello", .stringLiteral "world", .intLiteral 1]]
                                #[.datatype .integer false,
                                .datatype (.varchar 20) false,
                                .datatype (.varchar 20) false,
                                .datatype .integer false]
  let w := translateTableExpr z t
  return w

--#eval testValues true
--#eval testValues false

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

--#eval testProjection true
--#eval testProjection false


def testFilter (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .filter (.application ">" #[.column 0, .column 0]) (.baseTable "posts")
  let w := translateTableExpr z t
  return w

--#eval testFilter true
--#eval testFilter false


def testProduct (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .join (.baseTable "posts") (.baseTable "posts") .inner (.boolLiteral true)
  let w := translateTableExpr z t
  return w

--#eval testProduct true
--#eval testProduct false


def testLeftJoin (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .join (.baseTable "users") (.baseTable "posts") .left (.boolLiteral true)
  let w := translateTableExpr z t
  return w

--#eval testLeftJoin true
--#eval testLeftJoin false



def testProjectUnion (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e := Env.mk tm s2.snd HashMap.empty (if isBag then .bag else .set)
  let z := translateSchema e schema
  let t : TableExpr := .tableOperation
    .unionAll
    (.project #[.column 0, .column 1] (.baseTable "users"))
    (.project #[.column 0, .column 1] (.baseTable "posts"))

  let w := translateTableExpr z t
  return w


#eval testProjectUnion true
#eval testProjectUnion false
