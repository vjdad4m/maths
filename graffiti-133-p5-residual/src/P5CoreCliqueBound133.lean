import P5CoreCliqueFibers133

namespace Graffiti133P5CoreShape
open SimpleGraph Finset Graffiti133
open scoped Classical
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem clique_at_most_three_of_ordinary_C4_free
    (h4 : FourCycleFree G) (C : Finset V) (cl : G.IsClique (C : Set V)) : C.card≤3 := by
  by_contra! large
  obtain ⟨T,tC,t4⟩ := Finset.exists_subset_card_eq (show 4≤C.card by omega)
  have non : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,am⟩ := non
  have t3 : (T.erase a).card=3 := by
    have := Finset.card_erase_add_one am
    omega
  obtain ⟨b,c,d,bc,bd,cd,row⟩ := Finset.card_eq_three.mp t3
  have bm : b∈T.erase a := by simp [row]
  have cm : c∈T.erase a := by simp [row]
  have dm : d∈T.erase a := by simp [row]
  have ne_ba := (Finset.mem_erase.mp bm).1
  have ne_ca := (Finset.mem_erase.mp cm).1
  have ne_da := (Finset.mem_erase.mp dm).1
  have aa : a∈C := tC am
  have bb : b∈C := tC (Finset.mem_erase.mp bm).2
  have cc : c∈C := tC (Finset.mem_erase.mp cm).2
  have dd : d∈C := tC (Finset.mem_erase.mp dm).2
  exact cd (h4 a b c d ne_ba.symm (cl aa cc ne_ca.symm) (cl bb cc bc)
    (cl aa dd ne_da.symm) (cl bb dd bd))

#print axioms clique_at_most_three_of_ordinary_C4_free
end Graffiti133P5CoreShape
