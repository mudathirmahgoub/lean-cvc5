import Std -- Import the standard library

-- Example: Sorting a list of natural numbers
def compareNat (a b : Nat) : Bool :=
  if a < b then true
  else if a > b then false
  else true

def example1 : List Nat :=
  List.mergeSort [5, 1, 4, 2, 3] compareNat

#eval example1 -- Outputs: [1, 2, 3, 4, 5]

universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext

namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b
end Hidden



def Set (α : Type u) := α → Prop
namespace Set
def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) "∈" => mem
theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
end Set
