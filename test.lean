import Std -- Import the standard library

-- Example: Sorting a list of natural numbers
def compareNat (a b : Nat) : Bool :=
  if a < b then true
  else if a > b then false
  else true

def example1 : List Nat :=
  List.mergeSort [5, 1, 4, 2, 3] compareNat

#eval example1 -- Outputs: [1, 2, 3, 4, 5]

-- Example: Sorting a list of strings
def compareString (a b : String) : Ordering :=
  if a < b then Ordering.lt
  else if a > b then Ordering.gt
  else Ordering.eq

def example2 : List String :=
  List.mergeSort ["apple", "banana", "cherry", "date"] compareString

#eval example2 -- Outputs: ["apple", "banana", "cherry", "date"]
