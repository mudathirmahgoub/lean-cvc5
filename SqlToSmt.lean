import Std.Data.HashMap
import cvc5
import cvc5.Sql


open cvc5 (TermManager Solver Kind)
open Std

structure Env where
  tm: TermManager
  s: Solver
  map: HashMap String cvc5.Term := HashMap.empty
  semantics : SQLSemantics
  n : (Option Nat) := none
  constraints: Array cvc5.Term := #[]




def mkEmptyTable (e: Env) (s: cvc5.Sort): cvc5.Term :=
  match e.semantics with
  | .bag => e.tm.mkEmptyBag! s
  | .set => e.tm.mkEmptySet! s

def mkSingleton (e: Env) (tuple: cvc5.Term) : cvc5.Term :=
  match e.semantics with
  | .bag => e.tm.mkTerm! .BAG_MAKE #[tuple, e.tm.mkInteger 1]
  | .set => e.tm.mkTerm! .SET_SINGLETON #[tuple]

def printHashMap (map : HashMap String cvc5.Term) : String :=
  map.fold (fun acc key value =>
    acc ++ s!"{toString key}: {toString value} {toString value.getSort}\n"
  ) ""

instance : ToString Env where
  toString e := printHashMap e.map

instance : ToString (HashMap String cvc5.Term) where
  toString e := printHashMap e


def getTupleSort (e : Env) (tableSort : cvc5.Sort) : cvc5.Sort :=
  match e.semantics with
  | .bag => tableSort.getBagElementSort!
  | .set => tableSort.getSetElementSort!

def getUnionAllKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => Kind.BAG_UNION_DISJOINT
  | .set => Kind.SET_UNION

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

def getProductKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => .TABLE_PRODUCT
  | .set => .RELATION_PRODUCT

def getDifferenceRemoveKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => Kind.BAG_DIFFERENCE_REMOVE
  | .set => Kind.SET_MINUS

def getSubsetKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .bag => Kind.BAG_SUBBAG
  | .set => Kind.SET_SUBSET

def getAllKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .set => .SET_ALL
  | .bag => panic s!"BAG_ALL is not implemented in cvc5"

def getSomeKind (e: Env) : cvc5.Kind :=
  match e.semantics with
  | .set => .SET_SOME
  | .bag => panic s!"BAG_ALL is not implemented in cvc5"


def trBasetype (e: Env) (b: Basetype) : Option cvc5.Sort :=
  match b with
  | .integer => e.tm.getIntegerSort
  | .boolean => e.tm.getBooleanSort
  | .varchar (_: Nat) => e.tm.getStringSort

def trSqlType (e: Env) (d: SqlType) : Option cvc5.Sort :=
  let .sqlType base isNullable := d
  let s := trBasetype e base
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
  let e: Env := {tm:= tm, s := s2.snd, semantics := .bag}
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

def declareTable (e: Env) (table: BaseTable) : Env :=
  let sorts := table.columns.map (fun c => trSqlType e c.sqlType)
  let tupleSort := e.tm.mkTupleSort! (sorts.filterMap id).toArray
  let tableSort := mkTableSort e tupleSort
  let tableTerm := e.s.declareFun table.name #[] tableSort
  let t := match tableTerm with
    | some (except, _) => except.toOption.get!
    | none => panic! "tableTerm is none"
  dbg_trace s!"(declare-const {t} {t.getSort})";
  let bound := match e.n with
  | none => e.tm.mkBoolean true
  | some m =>
   let indices := List.range m
   let elements := indices.mapIdx (fun i x =>
     let const := e.s.declareFun s!"{table.name}_{i}" #[] tupleSort
     match const with
     | some (except, _) =>
       let z := except.toOption.get!
       dbg_trace s!"(declare-const {z} {z.getSort})";
       z
     | none => panic! "tableTerm is none"
     )
   let unionAll := elements.foldl
                  (fun a b => e.tm.mkTerm! (getUnionAllKind e) #[a, mkSingleton e b])
                  (mkEmptyTable e t.getSort)
   let subset := e.tm.mkTerm! (getSubsetKind e) #[t, unionAll]
   let distinct := e.tm.mkTerm! .DISTINCT elements.toArray
   distinct.and! subset
  dbg_trace s!"(assert {bound})";
  { e with map := e.map.insert table.name t }



def isIntegerOrNullableInteger (t: cvc5.Term) : Bool :=
  t.getSort.isInteger ||
  (t.getSort.isNullable && t.getSort.getNullableElementSort!.isInteger)


def liftIfNullable (e: Env) (needsLifting: Bool) (k: cvc5.Kind) (terms: List cvc5.Term) : cvc5.Term :=
  if needsLifting then e.tm.mkNullableLift! k terms.toArray
  else e.tm.mkTerm! k terms.toArray


def trAnd (e: Env) (needsLifting: Bool) (terms: List cvc5.Term) : cvc5.Term :=
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
                        e.tm.mkTerm! .ITE #[isSecondFalse, falseTerm,
                                            e.tm.mkNullableLift! .AND terms.toArray]]
  else
    e.tm.mkTerm! .AND terms.toArray


def trOr (e: Env) (needsLifting: Bool) (terms: List cvc5.Term) : cvc5.Term :=
  if needsLifting then
    let trueTerm := e.tm.mkNullableSome! (e.tm.mkBoolean true)
    let fstIsSome := e.tm.mkNullableIsSome! terms[0]!
    let sndIsSome := e.tm.mkNullableIsSome! terms[1]!
    let fstVal := e.tm.mkNullableVal! terms[0]!
    let sndVal := e.tm.mkNullableVal! terms[1]!
    let isFirstTrue := e.tm.mkTerm! .AND #[fstIsSome, fstVal]
    let isSecondTrue := e.tm.mkTerm! .AND #[sndIsSome, sndVal]
    e.tm.mkTerm! .ITE #[isFirstTrue, trueTerm,
                        e.tm.mkTerm! .ITE #[isSecondTrue,
                        trueTerm, e.tm.mkNullableLift! .OR terms.toArray]]
  else
    e.tm.mkTerm! .OR terms.toArray


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
  let e: Env := {tm:= tm, s := s, semantics := .bag}
  let z := defineFun e
  return z

--#eval testDefineFun



--#eval List.range 5

def mkNullableSort (e: Env) (s: cvc5.Sort) : cvc5.Sort :=
  if s.isNullable then s else e.tm.mkNullableSort! s

def mkLeft (e: Env) (a product: cvc5.Term) : cvc5.Term :=
  let aSort := getTupleSort e a.getSort
  let productSort := getTupleSort e product.getSort
  let differenceKind := getDifferenceRemoveKind e
  let (aTupleLength, productTupleLength) := (aSort.getTupleLength!.toNat, productSort.getTupleLength!.toNat)
  let aIndices := List.range aTupleLength
-- dbg_trace s!"aIndices: {aIndices}";
  let op := e.tm.mkOpOfIndices (getProjectKind e) aIndices.toArray |>.toOption.get!
-- dbg_trace s!"op: {op}";
  let projection := e.tm.mkTermOfOp op #[product] |>.toOption.get!
-- dbg_trace s!"projection: {projection}";
  let difference := e.tm.mkTerm! differenceKind #[a, projection]
-- dbg_trace s!"difference: {difference}";
  let aVar := e.tm.mkVar aSort "t" |>.toOption.get!
-- dbg_trace s!"t: {t}";
  let aTerms := aIndices.map (fun i => mkTupleSelect e aSort aVar i)
-- dbg_trace s!"aTerms: {aTerms}";
  let bIndices := List.range (productTupleLength - aTupleLength) |>.map (fun i => i + aTupleLength)
-- dbg_trace s!"bIndices: {bIndices}";
  let productSorts := productSort.getTupleSorts!.map (fun s => mkNullableSort e s)
-- dbg_trace s!"productSorts: {productSorts}";
  let bTerms := bIndices.map (fun i => e.tm.mkNullableNull productSorts[i]! |>.toOption.get!)
-- dbg_trace s!"bTerms: {bTerms}";
  let tuple := e.tm.mkTuple! (aTerms ++ bTerms).toArray
-- dbg_trace s!"tuple: {tuple}";
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[aVar]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  -- dbg_trace s!"lambda: {lambda}";
  let map := e.tm.mkTerm! (getMapKind e) #[lambda, difference]
  -- dbg_trace s!"map: {map}";
  map


def mkRight (e: Env) (b product: cvc5.Term) : cvc5.Term :=
  let bSort := getTupleSort e b.getSort
  let productSort := getTupleSort e product.getSort
  let differenceKind := getDifferenceRemoveKind e
-- dbg_trace s!"b: {b}";
  let (bTupleLength, productTupleLength) := (bSort.getTupleLength!.toNat, productSort.getTupleLength!.toNat)
  let aTupleLength := productTupleLength - bTupleLength;
  let bIndices := List.range bTupleLength |>.map (fun x => x + aTupleLength)
-- dbg_trace s!"bIndices: {bIndices}";
  let op := e.tm.mkOpOfIndices (getProjectKind e) bIndices.toArray |>.toOption.get!
-- dbg_trace s!"op: {op}";
  let projection := e.tm.mkTermOfOp op #[product] |>.toOption.get!
-- dbg_trace s!"projection: {projection}";
  let difference := e.tm.mkTerm! differenceKind #[b, projection]
-- dbg_trace s!"difference: {difference}";
  let bVar := e.tm.mkVar bSort "t" |>.toOption.get!
-- dbg_trace s!"bVar: {bVar}";
  let bTerms := bIndices.map (fun i => mkTupleSelect e bSort bVar (i - aTupleLength))
-- dbg_trace s!"bTerms: {bTerms}";
  let aIndices := List.range (aTupleLength)
-- dbg_trace s!"aIndices: {aIndices}";
  let productSorts := productSort.getTupleSorts!.map (fun s => mkNullableSort e s)
-- dbg_trace s!"productSorts: {productSorts}";
  let aTerms := aIndices.map (fun i => e.tm.mkNullableNull productSorts[i]! |>.toOption.get!)
  let tuple := e.tm.mkTuple! (aTerms ++ bTerms).toArray
-- dbg_trace s!"tuple: {tuple}";
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[bVar]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  -- dbg_trace s!"lambda: {lambda}";
  let map := e.tm.mkTerm! (getMapKind e) #[lambda, difference]
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


def mkQueryOp (e: Env) (op: cvc5.Kind) (a b: cvc5.Term) : cvc5.Term :=
  let aElementSort := getTupleSort e a.getSort
  let bElementSort := getTupleSort e b.getSort
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

def isNotEmpty (e: Env) (t : cvc5.Term) : Option cvc5.Term :=
  let empty := match e.semantics with
  | .bag => e.tm.mkEmptyBag! t.getSort
  | .set => e.tm.mkEmptySet! t.getSort
  let notEmpty := e.tm.mkTerm! .DISTINCT #[t,empty]
  notEmpty

def trUnique (e: Env) (name baseTable: String) (columns : Array Nat) : cvc5.Term :=
  dbg_trace s!";; {name}";
  let table := e.map[baseTable]!
  let sort := getTupleSort e table.getSort
  let x := e.tm.mkVar sort "x" |>.toOption.get!
  let y := e.tm.mkVar sort "y" |>.toOption.get!
  let equalities := columns.map (fun i =>
    let xElement := mkTupleSelect e sort x i
    let yElement := mkTupleSelect e sort y i
    let xSort := xElement.getSort
    let equal := e.tm.mkTerm! .EQUAL #[xElement,yElement]
    if xSort.isNullable then
      let xSome := e.tm.mkNullableIsSome! xElement
      let ySome := e.tm.mkNullableIsSome! yElement
      (xSome.and! ySome).and! equal
    else equal
    )
  let premise := equalities.foldl (fun a b => a.and! b) (e.tm.mkBoolean true)
  let conclusion := e.tm.mkTerm! .EQUAL #[x,y]
  let implies := e.tm.mkTerm! .IMPLIES #[premise, conclusion]
  let yList := e.tm.mkTerm! .VARIABLE_LIST #[y]
  let yLambda := e.tm.mkTerm! .LAMBDA #[yList, implies]
  let yAll := e.tm.mkTerm! (getAllKind e) #[yLambda, table]
  let xList := e.tm.mkTerm! .VARIABLE_LIST #[x]
  let xLambda := e.tm.mkTerm! .LAMBDA #[xList, yAll]
  let xAll := e.tm.mkTerm! (getAllKind e) #[xLambda, table]
  dbg_trace s!"(assert {xAll})";
  xAll

def trPrimary (e: Env) (name baseTable: String) (columns : Array Nat) : cvc5.Term :=
  dbg_trace s!";; {name}";
  let table := e.map[baseTable]!
  let sort := getTupleSort e table.getSort
  let x := e.tm.mkVar sort "x" |>.toOption.get!
  let y := e.tm.mkVar sort "y" |>.toOption.get!
  let equalities := columns.map (fun i =>
    let xElement := mkTupleSelect e sort x i
    let yElement := mkTupleSelect e sort y i
    let equal := e.tm.mkTerm! .EQUAL #[xElement,yElement]
    (equal, xElement)) |>.unzip
  let premise := equalities.fst.foldl (fun a b => a.and! b) (e.tm.mkBoolean true)
  let notNull := equalities.snd.foldl (fun a b =>
    if b.getSort.isNullable
    then a.and! (e.tm.mkNullableIsSome! b)
    else a) (e.tm.mkBoolean true)
  let conclusion := e.tm.mkTerm! .EQUAL #[x,y]
  let implies := e.tm.mkTerm! .IMPLIES #[premise, conclusion]
  let yList := e.tm.mkTerm! .VARIABLE_LIST #[y]
  let yLambda := e.tm.mkTerm! .LAMBDA #[yList, implies]
  let yAll := e.tm.mkTerm! (getAllKind e) #[yLambda, table]
  let xList := e.tm.mkTerm! .VARIABLE_LIST #[x]
  let xLambda := e.tm.mkTerm! .LAMBDA #[xList, yAll]
  let xAll := e.tm.mkTerm! (getAllKind e) #[xLambda, table]
  let xNotNull := e.tm.mkTerm! .LAMBDA #[xList, notNull]
  let xAllNotNull := e.tm.mkTerm! (getAllKind e) #[xNotNull, table]
  let and := xAllNotNull.and! xAll
  dbg_trace s!"(assert {and})";
  and

def trForeign (e : Env) (name child parent : String) (childColumns parentColumns :Array Nat): cvc5.Term :=
  dbg_trace s!";; {name}";
  let (childTerm, parentTerm) := (e.map[child]!,e.map[parent]!)
  let filter : Array Nat → cvc5.Term → cvc5.Term :=
    fun indices table =>
    let sort := getTupleSort e table.getSort
    let t := e.tm.mkVar sort "t" |>.toOption.get!
    let sorts := t.getSort.getTupleSorts!
    let keySorts := indices.map (fun i => sorts[i]!)
    if keySorts.any (fun s => s.isNullable)
    then
      let terms := indices.map (fun i =>
          let select := mkTupleSelect e sort t i
          if sorts[i]!.isNullable then
            e.tm.mkNullableIsSome! select
          else e.tm.mkBoolean true)
      let body := terms.foldl (fun a b => a.and! b) (e.tm.mkBoolean true)
      let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
      let lambda := e.tm.mkTerm! .LAMBDA #[boundList, body]
      e.tm.mkTerm! (getFilterKind e) #[lambda, table]
    else table
  let childFilter := filter childColumns childTerm
  let parentFilter := filter parentColumns parentTerm
  let childOp := e.tm.mkOpOfIndices (getProjectKind e) childColumns |>.toOption.get!
  let parentOp := e.tm.mkOpOfIndices (getProjectKind e) parentColumns |>.toOption.get!
  let childProject := e.tm.mkTermOfOp childOp #[childFilter] |>.toOption.get!
  let parentProject := e.tm.mkTermOfOp parentOp #[parentFilter] |>.toOption.get!
  let subset := mkQueryOp e (getSubsetKind e) childProject parentProject
  dbg_trace s!"(assert {subset})"
  subset


def getNullableTerms (e : Env) (terms: List cvc5.Term) :=
 let needsLifting := terms.any (fun t => t.getSort.isNullable)
 let nullableTerms :=
   if needsLifting
   then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
   else terms
 (needsLifting, nullableTerms)

mutual
partial def trQuery (e: Env) (Query: Query) : Option cvc5.Term :=
  match Query with
  | .baseTable name =>
    -- dbg_trace s!" .baseTable name: {name} and e: {e}, e.map[name]: {e.map[name]?}";
    e.map[name]?
  | .values rows => trValues e rows
  | .project exprs query =>
    -- dbg_trace s!" .project exprs:  query: ";
    trProject e exprs query
  | .filter condition query  => trFilter e condition query
  | .queryOperation op l r => trQueryOperation e op l r
  | .join l r j c => trJoin e l r j c

partial def trValues (e: Env) (rows: List (List Expr)): Option cvc5.Term :=
  let tuples := rows.map (fun row =>
    let null:= (cvc5.Term.null .unit)
    let f := (fun expr => trExpr e null expr)
                          let elements := row.map f |>.filterMap id
                          e.tm.mkTuple! elements)
  let sorts := types.map (fun t => trSqlType e t) |>.filterMap id
  let tupleSort := e.tm.mkTupleSort! sorts
  let tableSort := mkTableSort e tupleSort
  let emptyTable := mkEmptyTable e tableSort
  let combine := fun (table : Option cvc5.Term) (tuple : cvc5.Term)  =>
    let singleton := mkSingleton e tuple
    some (e.tm.mkTerm! (getUnionAllKind e) #[table.get!, singleton])
  tuples.foldl combine emptyTable

partial def trFilter (e: Env) (condition: BoolExpr) (query: Query) : Option cvc5.Term :=
  let query' := trQuery e query |>.get!
  let tupleSort := getTupleSort e query'.getSort
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let condition' := trExpr e t condition |>.get!
  let predicate := if condition'.getSort.isNullable
                then
                let isSome := e.tm.mkNullableIsSome! condition'
                let val := e.tm.mkNullableVal! condition'
                e.tm.mkTerm! .AND #[isSome, val]
                else condition'
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, predicate]
  e.tm.mkTerm! (getFilterKind e) #[lambda, query']

partial def trQueryOperation (e: Env) (op: QueryOp) (l r: Query) : Option cvc5.Term :=
  let l' := trQuery e l
  let r' := trQuery e r
  match op, e.semantics with
  | .union, .bag => e.tm.mkTerm! .BAG_SETOF #[(mkQueryOp e .BAG_UNION_DISJOINT  l'.get! r'.get!)]
  | .unionAll,.bag => mkQueryOp e .BAG_UNION_DISJOINT  l'.get! r'.get!
  | .union, .set => mkQueryOp e .SET_UNION  l'.get! r'.get!
  | .unionAll,.set => mkQueryOp e .SET_UNION  l'.get! r'.get!
  | .except, .bag => mkQueryOp e .BAG_DIFFERENCE_SUBTRACT  (e.tm.mkTerm! .BAG_SETOF #[l'.get!]) r'.get!
  | .exceptAll,.bag => mkQueryOp e .BAG_DIFFERENCE_SUBTRACT  l'.get! r'.get!
  | .except, .set => mkQueryOp e .SET_MINUS  l'.get! r'.get!
  | .exceptAll,.set => mkQueryOp e .SET_MINUS  l'.get! r'.get!
  | .intersect,.bag => e.tm.mkTerm! .BAG_SETOF #[(mkQueryOp e .BAG_INTER_MIN  l'.get! r'.get!)]
  | .intersectAll, .bag => mkQueryOp e .BAG_INTER_MIN  l'.get! r'.get!
  | .intersect, .set => mkQueryOp e .SET_INTER  l'.get! r'.get!
  | .intersectAll, .set => mkQueryOp e .SET_INTER  l'.get! r'.get!

partial def trProject (e: Env) (exprs: List Expr) (query: Query) : Option cvc5.Term :=
  let query' := trQuery e query |>.get!
--dbg_trace s!"query': {query'} exprs: {exprs}";
  let tupleSort := getTupleSort e query'.getSort
--dbg_trace s!"tupleSort: {tupleSort}";
  let isProject := exprs.all (fun x => match x with
    | .column _ => true
    | _ => false)
--dbg_trace s!"isProject: {isProject}";
--dbg_trace s!"(projectKind, mapKind): {projectKind}, {mapKind}";
  if isProject then
  let indices := exprs.map (fun x => match x with
    | .column i => i
    | _ => panic! "not an indexed column")
--dbg_trace s!"indices: {indices}";
  let op := e.tm.mkOpOfIndices (getProjectKind e) indices |>.toOption.get!
--dbg_trace s!"op: {op}";
--dbg_trace s!"query: {repr query}";
--dbg_trace s!"query': {query'}";
--dbg_trace s!"query: {query'.getSort} I am here";
  let projection := e.tm.mkTermOfOp op  #[query'] |>.toOption.get!
--dbg_trace s!"projection: {projection}";
  projection
  else
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let lambda := trTupleExpr e exprs t |>.get!
--dbg_trace s!"lambda: {lambda}";
  e.tm.mkTerm! (getMapKind e) #[lambda, query']

partial def trJoin (e: Env) (l: Query) (r: Query) (join: Join) (condition: BoolExpr) : Option cvc5.Term :=
  let l' := trQuery e l |>.get!
  let r' := trQuery e r |>.get!
  let unionKind := getUnionAllKind e
  let product := e.tm.mkTerm! (getProductKind e) #[l', r']
  let tupleSort := getTupleSort e product.getSort
  let t := e.tm.mkVar tupleSort "t" |>.toOption.get!
  let condition' := trExpr e t condition |>.get!
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
  let product' := e.tm.mkTerm! (getFilterKind e) #[lambda, product]
  match join with
  | .inner => product'
  | .left =>
    let left := mkLeft e l' product'
  --dbg_trace s!"left: {left}";
    -- let join := e.tm.mkTerm! unionKind #[product', left]
    let join := mkQueryOp e unionKind product' left
    join
  | .right =>
    let right := mkRight e r' product'
    let join := mkQueryOp e unionKind product' right
    join
  | .full =>
    let left := mkLeft e l' product'
    let right:= mkRight e r' product'
    let join := mkQueryOp e unionKind left right
    let join' := mkQueryOp e unionKind product' join
    join'


partial def trTupleExpr (e: Env) (exprs: Array Expr) (t : cvc5.Term) : Option cvc5.Term :=
  let terms := exprs.map (fun expr => trExpr e t expr)
  if terms.any (fun t => t.isNone) then none
  else
  let
  tuple := e.tm.mkTuple! (terms.filterMap id)
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, tuple]
  lambda

partial def trBoolArgs (e: Env) (k: cvc5.Kind) (t: cvc5.Term) (args : List BoolExpr) : cvc5.Term :=
  let terms := ((args.map (trBoolExpr e t)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    let arg0 := nullableTerms[0]!
    liftIfNullable e needsLifting k nullableTerms

partial def trStringArgs (e: Env) (k: cvc5.Kind) (t: cvc5.Term) (args : List StringExpr) : cvc5.Term :=
  let terms := ((args.map (trStringExpr e t)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    let arg0 := nullableTerms[0]!
    liftIfNullable e needsLifting k nullableTerms

partial def trIntArgs (e: Env) (k: cvc5.Kind) (t: cvc5.Term) (args : List IntExpr) : cvc5.Term :=
  let terms := ((args.map (trIntExpr e t)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    let arg0 := nullableTerms[0]!
    liftIfNullable e needsLifting k nullableTerms

partial def trBoolExpr (e: Env) (t: cvc5.Term) (s: BoolExpr): Option cvc5.Term :=
match s with
  | .column index => mkTupleSelect e t.getSort t index
  | .boolLiteral v => e.tm.mkBoolean v
  | .nullBool => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getBooleanSort)
  | .exists query =>
    let query' := (trQuery e query) |>.get!
    isNotEmpty e query'
  | .case condition thenExpr elseExpr  =>
    let terms := ((#[condition, thenExpr, elseExpr].map (trBoolExpr e t)).filterMap id)
    let thenTerm := terms[1]!
    let elseTerm := terms[2]!
    let thenElse := #[thenTerm, elseTerm]
    let needsLifting := thenElse.any (fun x => x.getSort.isNullable)
    let nullableTerms := if needsLifting
      then thenElse.map (fun x => if x.getSort.isNullable then x else e.tm.mkNullableSome! x)
      else thenElse
    let condition' := if terms[0]!.getSort.isNullable then
                       (e.tm.mkNullableIsSome! terms[0]!).and! (e.tm.mkNullableVal! terms[0]!)
                      else  terms[0]!
    e.tm.mkTerm! .ITE (#[condition'] ++ nullableTerms)
  | .boolEqual a b => trBoolArgs e .EQUAL t [a,b]
  | .intEqual a b => trIntArgs e .EQUAL t [a,b]
  | .stringEqual a b => trStringArgs e .EQUAL t [a,b]
  | .not a =>
    let a' := trBoolExpr e t a |>.get!
    liftIfNullable e a'.getSort.isNullable .NOT [a']
  | .and a b =>
    let (a', b') := (trBoolExpr e t a |>.get!, trBoolExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    trAnd e needsLifting nullableTerms
  | .or a b =>
    let (a', b') := (trBoolExpr e t a |>.get!, trBoolExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    trOr e needsLifting nullableTerms
  | .lsInt a b =>
    let (a', b') := (trIntExpr e t a |>.get!, trIntExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .LT nullableTerms
  | .leqInt a b =>
    let (a', b') := (trIntExpr e t a |>.get!, trIntExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .LEQ nullableTerms
  | .gtInt a b =>
    let (a', b') := (trIntExpr e t a |>.get!, trIntExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .GT nullableTerms
  | .geqInt a b =>
    let (a', b') := (trIntExpr e t a |>.get!, trIntExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .GEQ nullableTerms
  | .lsString a b =>
    let (a', b') := (trStringExpr e t a |>.get!, trStringExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .STRING_LT nullableTerms
  | .leqString a b =>
    let (a', b') := (trStringExpr e t a |>.get!, trStringExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .STRING_LEQ nullableTerms
  | .gtString a b =>
    let (a', b') := (trStringExpr e t a |>.get!, trStringExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [b', a']
    liftIfNullable e needsLifting .STRING_LT nullableTerms
  | .geqString a b =>
    let (a', b') := (trStringExpr e t a |>.get!, trStringExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [b', a']
    liftIfNullable e needsLifting .STRING_LEQ nullableTerms
  | .isNullBool a =>
    let a' := trBoolExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsNull! a'
    else e.tm.mkBoolean false
  | .isNotNullBool a =>
    let a' := trBoolExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsSome! a'
    else e.tm.mkBoolean true
  | .isNullInt a =>
    let a' := trIntExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsNull! a'
    else e.tm.mkBoolean false
  | .isNotNullInt a =>
    let a' := trIntExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsSome! a'
    else e.tm.mkBoolean true
  | .isNullString a =>
    let a' := trStringExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsNull! a'
    else e.tm.mkBoolean false
  | .isNotNullString a =>
    let a' := trStringExpr e t a |>.get!
    if a'.getSort.isNullable
    then e.tm.mkNullableIsSome! a'
    else e.tm.mkBoolean true
  | .isTrue a =>
    let a' := trBoolExpr e t a |>.get!
    if a'.getSort.isNullable
    then (e.tm.mkNullableIsSome! a').and! (e.tm.mkNullableVal! a')
    else a'
  | .isNotTrue a =>
    let a' := trBoolExpr e t a |>.get!
    if a'.getSort.isNullable
    then (e.tm.mkNullableIsNull! a').or! (e.tm.mkNullableVal! a').not!
    else e.tm.mkTerm! .NOT #[a']

partial def trStringExpr (e: Env) (t: cvc5.Term) (s: StringExpr): Option cvc5.Term :=
 match s with
 | .column index => mkTupleSelect e t.getSort t index
 | .stringLiteral v => e.tm.mkString v |>.toOption
 | .nullString => e.tm.mkNullableNull! (e.tm.mkNullableSort! e.tm.getStringSort)
 | .case condition thenExpr elseExpr  =>
    let list := [thenExpr, elseExpr].map (trStringExpr e t)
    let condition' := trBoolExpr e t condition
    let terms := ([condition'] ++ list).filterMap id
    let thenTerm := terms[1]!
    let elseTerm := terms[2]!
    let thenElse := #[thenTerm, elseTerm]
    let needsLifting := thenElse.any (fun x => x.getSort.isNullable)
    let nullableTerms := if needsLifting
      then thenElse.map (fun x => if x.getSort.isNullable then x else e.tm.mkNullableSome! x)
      else thenElse
    let condition' := if terms[0]!.getSort.isNullable then
                       (e.tm.mkNullableIsSome! terms[0]!).and! (e.tm.mkNullableVal! terms[0]!)
                      else  terms[0]!
    e.tm.mkTerm! .ITE (#[condition'] ++ nullableTerms)
 | .upper a =>
   let a' := trStringExpr e t a |>.get!
   liftIfNullable e a'.getSort.isNullable .STRING_TO_UPPER [a']
 | .lower a =>
   let a' := trStringExpr e t a |>.get!
   liftIfNullable e a'.getSort.isNullable .STRING_TO_LOWER [a']
 | .concat a b =>
    let (a', b') := (trStringExpr e t a |>.get!, trStringExpr e t b |>.get!)
    let (needsLifting, nullableTerms) := getNullableTerms e [a', b']
    liftIfNullable e needsLifting .STRING_CONCAT nullableTerms
 | .substring a b c => none

partial def trIntExpr (e: Env) (t: cvc5.Term) (s: IntExpr): Option cvc5.Term :=
sorry


partial def trExpr (e: Env) (t: cvc5.Term) (s: Expr): Option cvc5.Term :=
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
  | .exists query =>
    let query' := (trQuery e query) |>.get!
    isNotEmpty e query'
  | .case condition thenExpr elseExpr  =>
    let terms := ((#[condition, thenExpr, elseExpr].map (trExpr e t)).filterMap id)
    --dbg_trace s!"terms: {terms}";
    let thenTerm := terms[1]!
    let elseTerm := terms[2]!
    let thenElse := #[thenTerm, elseTerm]
    let needsLifting := thenElse.any (fun x => x.getSort.isNullable)
    let nullableTerms := if needsLifting
      then thenElse.map (fun x => if x.getSort.isNullable then x else e.tm.mkNullableSome! x)
      else thenElse
    --dbg_trace s!"nullableTerms: {nullableTerms}";
    let condition' := if terms[0]!.getSort.isNullable then
                       (e.tm.mkNullableIsSome! terms[0]!).and! (e.tm.mkNullableVal! terms[0]!)
                      else  terms[0]!
    e.tm.mkTerm! .ITE (#[condition'] ++ nullableTerms)
  | .application op args =>
    let terms := ((args.map (trExpr e t)).filterMap id)
    let needsLifting := terms.any (fun t => t.getSort.isNullable)
    let nullableTerms := if needsLifting
      then terms.map (fun t => if t.getSort.isNullable then t else e.tm.mkNullableSome! t)
      else terms
    let arg0 := nullableTerms[0]!
    match op with
    | "=" => liftIfNullable e needsLifting .EQUAL nullableTerms
    | "<>" => liftIfNullable e needsLifting .DISTINCT nullableTerms
    | "+" => liftIfNullable e needsLifting .ADD nullableTerms
    | "-" => liftIfNullable e needsLifting .SUB nullableTerms
    | "*" => liftIfNullable e needsLifting .MULT nullableTerms
    | ">" => if isIntegerOrNullableInteger arg0
             then liftIfNullable e needsLifting .GT nullableTerms
             else liftIfNullable e needsLifting .STRING_LT #[nullableTerms[1]!, arg0]
    | "<" => if isIntegerOrNullableInteger arg0
             then liftIfNullable e needsLifting .LT nullableTerms
             else liftIfNullable e needsLifting .STRING_LT nullableTerms
    | ">=" => if isIntegerOrNullableInteger arg0
              then liftIfNullable e needsLifting .GEQ nullableTerms
              else liftIfNullable e needsLifting .STRING_LEQ #[nullableTerms[1]!, arg0]
    | "<=" => if isIntegerOrNullableInteger arg0
              then liftIfNullable e needsLifting .LEQ nullableTerms
              else liftIfNullable e needsLifting .STRING_LEQ nullableTerms
    | "UPPER" => liftIfNullable e needsLifting .STRING_TO_UPPER nullableTerms
    | "||" => liftIfNullable e needsLifting .STRING_CONCAT nullableTerms
    | "IS NULL" => if needsLifting
                   then e.tm.mkNullableIsNull! arg0
                   else e.tm.mkBoolean false
    | "IS NOT NULL" => if needsLifting
                   then e.tm.mkNullableIsSome! arg0
                   else e.tm.mkBoolean true
    | "IS TRUE" => if needsLifting
                   then (e.tm.mkNullableIsSome! arg0).and! (e.tm.mkNullableVal! arg0)
                   else arg0
    | "IS NOT TRUE" => if needsLifting
                   then (e.tm.mkNullableIsNull! arg0).or! (e.tm.mkNullableVal! arg0).not!
                   else e.tm.mkTerm! .NOT #[arg0]
    | "NOT" => liftIfNullable e needsLifting .NOT nullableTerms
    | "AND" => trAnd e needsLifting nullableTerms
    | "OR" => trOr e needsLifting nullableTerms
    | _ => none

end

def trCheck (e : Env) (name baseTable : String) (expr : Expr): cvc5.Term :=
  dbg_trace s!";; {name}";
  let table := e.map[baseTable]!
  let t := e.tm.mkVar (getTupleSort e table.getSort) "t" |>.toOption.get!
  let expr' := trExpr e t expr |>.get!
  let expr'' := if expr'.getSort.isNullable
    then
      let isSome := e.tm.mkNullableIsSome! expr'
      e.tm.mkTerm! .IMPLIES #[isSome, e.tm.mkNullableVal! expr']
    else expr'
  let boundList := e.tm.mkTerm! .VARIABLE_LIST #[t]
  let lambda := e.tm.mkTerm! .LAMBDA #[boundList, expr'']
  let all := e.tm.mkTerm! (getAllKind e) #[lambda, table]
  dbg_trace s!"(assert {all})"
  all

def trConstraint (e: Env) (c: Constraint) : cvc5.Term :=
  match c with
  | .unique name baseTable columns => trUnique e name baseTable columns
  | .primaryKey name baseTable columns => trPrimary e name baseTable columns
  | .foreignKey name child parent childColumns parentColumns =>
     trForeign e name child parent childColumns parentColumns
  | .check name baseTable expr => trCheck e name baseTable expr

def trSchema (e: Env) (d: DatabaseSchema) : Env :=
  let e' := d.baseTables.foldl declareTable e
  let constraints := d.constraints.map (fun c => trConstraint e' c)
  let e'' := {e' with constraints := constraints}
  e''



def equivalenceFormula (e: Env) (d: DatabaseSchema) (q1 q2: Query) : cvc5.Term :=
  let e' := trSchema e d
  let q1' := trQuery e' q1 |>.get!
  let q2' := trQuery e' q2 |>.get!
  let formula := mkQueryOp e .DISTINCT q1' q2'
  dbg_trace s!"(assert {formula})";
  formula


def test1 := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e: Env := {tm:= tm, s := s, semantics := .bag}
  let x := trSqlType e (.datatype .boolean true)
  let y := tm.mkTupleSort! #[x.get!]
  let tTuple := tm.mkNullableSome! (tm.mkBoolean true)
  let fTuple := tm.mkNullableSome! (tm.mkBoolean false)
  let k := cvc5.Kind.AND
  let lift := tm.mkNullableLift k #[tTuple,fTuple]
  return lift


def schema : DatabaseSchema :=
  { baseTables := #[
      { name := "users", columns := #[
          { index := 0, datatype := Datatype.datatype Basetype.integer true },
          { index := 1, datatype := Datatype.datatype Basetype.integer true },
          { index := 2, datatype := Datatype.datatype Basetype.text true },
          { index := 3, datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) true }
        ]
      },
      { name := "posts", columns := #[
          { index := 0, datatype := Datatype.datatype Basetype.integer false },
          { index := 1, datatype := Datatype.datatype Basetype.integer false },
          { index := 2, datatype := Datatype.datatype (Basetype.varchar 10) true },
          { index := 3, datatype := Datatype.datatype (Basetype.varchar 20) true },
          { index := 4, datatype := Datatype.datatype (Basetype.timestampWithoutTimeZone 0) true }
        ]
      }
    ]
  }

instance : Inhabited BaseTable where
  default := { name := "", columns := #[] }

def test2 (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e: Env := {tm:= tm, s := s, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  return z.map

--#eval test2 true
--#eval test2 false


def test3 (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let e: Env := {tm:= tm, s := s, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .queryOperation .unionAll  (.baseTable "users") (.baseTable "users")
  let w := trQuery z t
  return w

--#eval test3 true
--#eval test3 false


def test4 (simplify: Bool) (value: Bool) (op: String) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s, semantics := .bag}
  let nullLiteral := Expr.nullLiteral .boolean
  let x := Expr.boolLiteral value
  let andExpr := Expr.application op #[nullLiteral, x]
  let query := (e.tm.mkBoolean true)
  let z : Option cvc5.Term := trExpr e query andExpr
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
  let e: Env := {tm:= tm, s := s, semantics := .bag}
  let x := Expr.boolLiteral value
  let expr := Expr.application op #[x]
  let query := (e.tm.mkBoolean true)
  let z : Option cvc5.Term := trExpr e query expr
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
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .values #[#[.intLiteral 1, .stringLiteral "hello", .stringLiteral "world", .intLiteral 1],
                                #[.intLiteral 2, .stringLiteral "hello", .stringLiteral "world", .intLiteral 1]]
                                #[.datatype .integer false,
                                .datatype (.varchar 20) false,
                                .datatype (.varchar 20) false,
                                .datatype .integer false]
  let w := trQuery z t
  return w

#eval testValues true
#eval testValues false

def testProjection (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .project #[.column 0, .column 1,
  .stringLiteral "hello", .application "+" #[.intLiteral 1, .application "+" #[.column 0, .column 1]]] (.baseTable "posts")
  let w := trQuery z t
  return w

--#eval testProjection true
--#eval testProjection false


def testFilter (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .filter (.application ">" #[.column 0, .column 0]) (.baseTable "posts")
  let w := trQuery z t
  return w

--#eval testFilter true
--#eval testFilter false


def testProduct (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .join (.baseTable "posts") (.baseTable "posts") .inner (.boolLiteral true)
  let w := trQuery z t
  return w

--#eval testProduct true
--#eval testProduct false


def testLeftJoin (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .join (.baseTable "users") (.baseTable "posts") .left (.boolLiteral true)
  let w := trQuery z t
  return w

--#eval testLeftJoin true
--#eval testLeftJoin false


def testRightJoin (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .join (.baseTable "users") (.baseTable "posts") .right (.boolLiteral true)
  let w := trQuery z t
  return w

#eval testRightJoin true
#eval testRightJoin false


def testFullJoin (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .join (.baseTable "users") (.baseTable "posts") .full (.boolLiteral true)
  let w := trQuery z t
  return w

#eval testFullJoin true
#eval testFullJoin false



def testProjectUnion (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := if isBag then .bag else .set}
  let z := trSchema e schema
  let t : Query := .queryOperation
    .unionAll
    (.project #[.column 0, .column 1] (.baseTable "users"))
    (.project #[.column 0, .column 1] (.baseTable "posts"))

  let w := trQuery z t
  return w


--#eval testProjectUnion true
--#eval testProjectUnion false

def testVerify (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setLogic "HO_ALL"
  let s3 ← s2.snd.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s3.snd, semantics := if isBag then .bag else .set}
  let q1 : Query := .queryOperation
    .unionAll
    (.project #[.column 0, .column 1] (.baseTable "users"))
    (.project #[.column 0, .column 1] (.baseTable "posts"))
  let q2 : Query := .queryOperation
    .unionAll
    (.project #[.column 0, .column 1] (.baseTable "posts"))
    (.project #[.column 0, .column 1] (.baseTable "users"))
  let formula := equivalenceFormula e schema q1 q2
  return formula


#eval testVerify true
#eval testVerify false


def testExists (isBag : Bool) := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setLogic "HO_ALL"
  let s3 ← s2.snd.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s3.snd, semantics := if isBag then .bag else .set}
  let users : Query := (.baseTable "users")
  let q1 : Query := .filter ( .boolLiteral true) users
  let q2 : Query := .filter ( .exists users) users
  let formula := equivalenceFormula e schema q1 q2
  return formula


#eval testExists true
#eval testExists false


def schema2 : DatabaseSchema :=
  { baseTables := #[
      { name := "users", columns := #[
          { index := 0, datatype := Datatype.datatype Basetype.boolean true },
          { index := 1, datatype := Datatype.datatype Basetype.integer true },
          { index := 2, datatype := Datatype.datatype Basetype.integer false }
        ]
      }
    ]
  }

def testCaseStatement  := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := .bag}
  let x := Expr.column 0
  let y := Expr.column 1
  let z := Expr.column 2
  let case1 := Expr.case x y z
  let case2 := Expr.case (.application "AND" #[x,.boolLiteral true]) y z
  let q1 : Query := .project #[case1] (.baseTable "users")
  let q2 : Query := .project #[case2] (.baseTable "users")
  let formula := equivalenceFormula e schema2 q1 q2
  return formula

#eval testCaseStatement


def schema3 : DatabaseSchema :=
  { baseTables := #[
      { name := "users", columns := #[
          { index := 0, datatype := Datatype.datatype Basetype.integer true },
          { index := 1, datatype := Datatype.datatype Basetype.integer false },
          { index := 2, datatype := Datatype.datatype Basetype.integer false }
        ]
      },
      { name := "child", columns := #[
          { index := 0, datatype := Datatype.datatype Basetype.integer true },
          { index := 1, datatype := Datatype.datatype Basetype.integer false },
          { index := 2, datatype := Datatype.datatype Basetype.integer false }
        ]
      }
    ],
    constraints := #[
      .unique "uq" "users" #[0,1],
      .primaryKey "pq" "users" #[0,1],
      .foreignKey "fk" "child" "users" #[0,1] #[1,0],
      .check "ck" "users" (.application ">" #[.column 0, .intLiteral 0])
    ]
  }

def testConstraints  := do
  let tm ← TermManager.new
  let s := (Solver.new tm)
  let s2 ← s.setOption "dag-thresh" "0"
  let e: Env := {tm:= tm, s := s2.snd, semantics := .set, n:= some 3}
  let e' := trSchema e schema3
  return e'

#eval testConstraints

#check Int
#check String
#check Array Type

def tupleType (q: Query) : Type := sorry
