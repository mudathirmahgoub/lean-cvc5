import cvc5
import cvc5.Sql

open cvc5 (TermManager)

def translateBasetype? (tm: TermManager) (b: Basetype) : Option cvc5.Sort :=
  match b with
  | .bigint => tm.getIntegerSort
  | .integer => tm.getIntegerSort
  | .boolean => tm.getBooleanSort
  | .characterVarying (_: Nat) => tm.getStringSort
  | _ => none

def translateDatatype (tm: TermManager) (d: Datatype) : Option cvc5.Sort :=
  let .datatype base isNullable := d
  let s := translateBasetype? tm base
  match isNullable with
  | false => s
  | true => match s with
    | none => none
    | some s => tm.mkNullableSort? s

def test := do
  let tm ← TermManager.new
  let x := translateDatatype tm (.datatype .boolean true)
  let y := tm.mkTupleSort! #[x.get!]
  let tTuple := tm.mkBoolean true
  let fTuple := tm.mkBoolean false
  let k := cvc5.Kind.AND
  let lift := tm.mkNullableLift k #[tTuple,fTuple]
  return lift

#eval test
