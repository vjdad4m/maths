import PairTests180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
abbrev V := Fin 8
noncomputable def E : List (V×V) := [(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,7),(2,5),(2,6),(3,7),(4,6),(5,7)]
noncomputable def G : SimpleGraph V where
  Adj x y := x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance : DecidableRel G.Adj := fun x y =>
  inferInstanceAs (Decidable (x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)))
noncomputable abbrev A : Finset V := {0,1,2}
noncomputable abbrev P : Finset V := {0,1,2,4,7}
noncomputable abbrev X : Finset V := {0,5}
noncomputable def d (x : V) := ([2,2,0,3,2,1,1,2]:List ℕ)[x.val]!
noncomputable def pairs : Finset (Finset V) := {{0,5},{0,1},{4,7},{6,7}}

theorem data : G.Connected ∧ parity G 2 false=P ∧ Indep G A ∧ eligible A P 2=P ∧ A∩insert 2 P=A := by
  have ⟨gc,dist⟩ : G.Connected ∧ ∀ x,G.dist x 2=d x := by
    apply layers
    · exact (by decide : d 2=0)
    · intro x y
      exact (show ∀ i j : V,G.Adj i j → d i≤d j+1 by decide) x y
    · exact (show ∀ x : V,x≠2 → ∃ y,G.Adj x y ∧ d x=d y+1 by decide)
  exact ⟨gc,by ext x;simp only [mem_parity,dist];exact (show ∀ v : V,d v%2=false.toNat ↔ v∈P by decide) x,
    by unfold Indep;decide,by decide,by decide⟩


#print axioms Eight.data
end Minimal180.PairRepair.Eight
