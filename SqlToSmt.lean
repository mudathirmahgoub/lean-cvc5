import cvc5
import cvc5.Sql
open cvc5(TermManager)

def translateBasetype (tm: TermManager) (b: Basetype) : Option cvc5.Sort :=
  match b with
  | Basetype.bigint => tm.getIntegerSort
  | Basetype.integer => tm.getIntegerSort
  | Basetype.boolean => tm.getBooleanSort
  | Basetype.characterVarying (_: Nat) => tm.getStringSort
  | _ => none


def translateDatatype (tm: TermManager) (d: Datatype) : Option cvc5.Sort :=
  match d with
  | Datatype.datatype b false => translateBasetype tm b
  | Datatype.datatype b true =>
    let o := translateBasetype tm b
    match o with
    | none => none
    | some s =>
      let t := tm.mkNullableSort s
      match t with
      | Except.ok sort => some sort
      | _ => none


def test := do
  let tm ← TermManager.new
  let x := translateDatatype tm (Datatype.datatype Basetype.boolean true)
  return x

#eval test
