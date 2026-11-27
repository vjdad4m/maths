import GraphSpliceCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange

namespace Graffiti199Depleted

abbrev O := Fin 6

/-- The two low vertices are 0 and 1. The optional single removal
is 3, which belongs to the first triangle. -/
def terminalKept (loss : Bool) (i : O) : Bool := !loss || i != 3

def terminalHigh (i : O) : Bool := i != 0 && i != 1

def terminalEdges : List (O × O) :=
  [(0,1),(0,2),(0,3),(2,3),(1,4),(1,5),(4,5)]

def terminalHas (a b : O) : Bool :=
  terminalEdges.contains (a,b) || terminalEdges.contains (b,a)

def terminalPath (loss : Bool) (i : O) : List O :=
  (match i with
  | 2 => [2,3,0,1,4,5]
  | 3 => [3,2,0,1,4,5]
  | 4 => [4,5,1,0,2,3]
  | 5 => [5,4,1,0,2,3]
  | _ => []).filter (terminalKept loss)

private def validTerminal (loss : Bool) (i : O) (xs : List O) : Bool :=
  decide xs.Nodup &&
  (List.finRange 6).all (fun a => (xs.contains a) == terminalKept loss a) &&
  decide (xs.Chain' fun a b => terminalHas a b = true) &&
  xs.head? == some i

private theorem terminal_check :
    ∀ (loss : Bool) (i : O), terminalKept loss i = true → terminalHigh i = true →
      validTerminal loss i (terminalPath loss i) = true := by decide

variable {V : Type*} {G : SimpleGraph V}

abbrev terminalRegion (g : O ↪ V) (loss : Bool) : Set V :=
  {v | ∃ i, terminalKept loss i = true ∧ g i = v}

/-- Every retained high vertex can start a spanning path of the terminal pair,
including when one high of the first half has been removed. -/
theorem terminal_path_from_high (g : O ↪ V) (loss : Bool)
    (edges : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (g a) (g b))
    {i : O} (kept : terminalKept loss i = true) (high : terminalHigh i = true) :
    ∃ q : PathOn G (terminalRegion g loss), q.first = g i := by
  let xs := terminalPath loss i
  have check : validTerminal loss i xs = true := terminal_check loss i kept high
  simp only [validTerminal,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at check
  obtain ⟨⟨⟨nd,all⟩,chain⟩,head⟩ := check
  have ne : xs ≠ [] := fun h => by simp [h] at head
  have cover (a : O) : a ∈ xs ↔ terminalKept loss a = true := by
    have eq := List.all_eq_true.mp all a (List.mem_finRange _)
    rw [beq_iff_eq] at eq
    rw [← eq,List.contains_iff_mem]
  have ch := chain.imp (fun a b e => by
    simp only [terminalHas,Bool.or_eq_true,List.contains_iff_mem] at e
    exact e.elim (edges a b) (fun f => (edges b a f).symm))
  let q := liftLabelPath g xs ne nd ch cover
  refine ⟨q,?_⟩
  apply Option.some.inj
  change some (q.vertices.head q.nonempty) = some (g i)
  rw [← List.head?_eq_head q.nonempty]
  change (xs.map g).head? = _
  simp [head]

#print axioms terminal_path_from_high

end Graffiti199Depleted
