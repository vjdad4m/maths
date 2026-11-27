import Partial133
import Mathlib.Data.Finset.Card

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

/-- In a four-port ordinary-C4-free core with no common neighbor of all
four ports, one port sees no vertex which also sees two other ports. -/
theorem four_ports_exists_anchor_without_triple_neighbor (h4 : FourCycleFree G)
    (D : Finset V) (p : Fin 4 → V) (pi : Function.Injective p)
    (noFour : ∀ v∈D, ¬ ∀ j : Fin 4, G.Adj (p j) v) :
    ∃ i : Fin 4, ∀ v∈D, G.Adj (p i) v → ∀ j k : Fin 4, j≠i → k≠i → j≠k →
      ¬(G.Adj (p j) v ∧ G.Adj (p k) v) := by
  classical
  let M (v : V) : Finset (Fin 4) := Finset.univ.filter fun j => G.Adj (p j) v
  have m (v : V) (j : Fin 4) : j∈M v ↔ G.Adj (p j) v := by simp [M]
  by_cases triple : ∃ r∈D, 3≤(M r).card
  · obtain ⟨r,rd,cr⟩ := triple
    have gap : ∃ i : Fin 4, ¬G.Adj (p i) r := by
      by_contra h
      exact noFour r rd (fun i => Classical.byContradiction (fun hi => h ⟨i,hi⟩))
    obtain ⟨i,ni⟩ := gap
    have relays (j : Fin 4) (ji : j≠i) : G.Adj (p j) r := by
      apply Classical.byContradiction
      intro nj
      have sub : M r ⊆ ((Finset.univ : Finset (Fin 4)).erase i).erase j := by
        intro a am
        have aa := (m r a).mp am
        refine Finset.mem_erase.mpr ⟨fun e=>nj (e ▸ aa),Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩⟩
        exact fun e => ni (e ▸ aa)
      have both : (((Finset.univ : Finset (Fin 4)).erase i).erase j).card=2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ji,Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ]
        decide
      have bound := Finset.card_le_card sub
      omega
    refine ⟨i,?_⟩
    intro v _ iv j k ji ki jk vjk
    have rv : r=v := h4 (p j) (p k) r v (pi.ne jk) (relays j ji) (relays k ki) vjk.1 vjk.2
    exact ni (rv.symm ▸ iv)
  · refine ⟨0,?_⟩
    intro v vd iv j k jz kz jk vjk
    have sub : ({0,j,k} : Finset (Fin 4))⊆M v := by
      intro a am
      simp only [Finset.mem_insert,Finset.mem_singleton] at am
      rcases am with rfl | rfl | rfl
      · exact (m _ _).mpr iv
      · exact (m _ _).mpr vjk.1
      · exact (m _ _).mpr vjk.2
    have three : ({0,j,k} : Finset (Fin 4)).card=3 := by simp [jz.symm,kz.symm,jk]
    have b := Finset.card_le_card sub
    exact triple ⟨v,vd,by omega⟩

#print axioms four_ports_exists_anchor_without_triple_neighbor
end Graffiti133P5CliqueArms
