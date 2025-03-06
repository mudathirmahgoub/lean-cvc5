import cvc5
open cvc5



def k := Kind.SET_ALL

def tm : BaseIO TermManager := TermManager.new



/-- solve the system of equation `y < x ∧ x < c * y` for the provided `c` -/
def solve (c : Int) : IO (Int × Int) := do
  let tm ← TermManager.new
  Solver.run! tm do
    Solver.setOption "produce-models" "true"
    let int := tm.getIntegerSort
    let x ← Solver.declareFun "x" #[] int
    let y ← Solver.declareFun "y" #[] int
    let f := tm.mkTerm! .AND
      #[tm.mkTerm! .LT #[y, x],
        tm.mkTerm! .LT #[x, tm.mkTerm! .MULT #[tm.mkInteger c, y]]]
    Solver.assertFormula f
    let r ← Solver.checkSat
    if !r.isSat then
      throw (.error s!"expected sat, got {r}")
    let x ← Solver.getValue x
    let y ← Solver.getValue y
    return (x.getIntegerValue!, y.getIntegerValue!)

def main (args : List String) : IO UInt32 := do
  let [c] := args | IO.println "Usage: <int>"; return 1
  let .some c := c.toInt? | IO.println "Usage: <int>"; return 1
  let (x, y) ← solve c
  IO.println s!"x = {x}, y = {y}"
  return 0

#eval main ["2"]
#eval main ["6"]
