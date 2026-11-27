import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

namespace TriangleChain
open SimpleGraph Finset
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j

/-- The two neighbors of an index on an induced cycle of length at least four
are distinct and are not consecutive to one another. -/
private theorem cycle_neighbors {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p ≠ s ∧ ¬consecutive p s := by
  let near (a b : ℕ) := a+1=b ∨ b+1=a ∨ (a=0 ∧ b+1=k) ∨ (b=0 ∧ a+1=k)
  have build (a b : ℕ) (ha : a<k) (hb : b<k)
      (check : near i.val a ∧ near i.val b ∧ a≠b ∧ ¬near a b) :
      ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p≠s ∧ ¬consecutive p s :=
    ⟨⟨a,ha⟩,⟨b,hb⟩,check.1,check.2.1,fun e => check.2.2.1 (congrArg Fin.val e),check.2.2.2⟩
  by_cases first : i.val=0
  · exact build (k-1) 1 (by omega) (by omega) (by dsimp [near]; omega)
  by_cases last : i.val+1=k
  · exact build (i.val-1) 0 (by omega) (by omega) (by dsimp [near]; omega)
  · exact build (i.val-1) (i.val+1) (by omega) (by omega) (by dsimp [near]; omega)

/-- An elimination order certifies the forbidden-induced-cycle definition. -/
theorem chordal_of_elimination {U : Type*} (G : SimpleGraph U) (r : U → ℕ)
    (clique : ∀ x y z, G.Adj x y → G.Adj x z → y≠z →
      r y ≤ r x → r z ≤ r x → G.Adj y z) : Chordal G := by
  rintro k hk ⟨f,cyc⟩
  have nonempty : (univ : Finset (Fin k)).Nonempty := ⟨⟨0,by omega⟩,mem_univ _⟩
  obtain ⟨i,_,top⟩ := exists_max_image univ (fun j => r (f j)) nonempty
  obtain ⟨p,s,ip,is,ne,gap⟩ := cycle_neighbors hk i
  exact gap ((cyc p s).mp (clique (f i) (f p) (f s) ((cyc i p).mpr ip) ((cyc i s).mpr is)
    (f.injective.ne ne) (top p (mem_univ _)) (top s (mem_univ _))))

end TriangleChain
