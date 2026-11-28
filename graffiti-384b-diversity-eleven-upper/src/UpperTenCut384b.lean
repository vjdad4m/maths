import DiversityElevenUpper384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph OddStars OddStars.LeafCritical
open private OddStars.LeafCritical.max_compl OddStars.LeafCritical.max_covers from LeafCritical
open private OddStars.ShoreRanks.active_hit from ShoreRanks
open private Graffiti384b.cut from Proof384b
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem crossed_card (J : SimpleGraph V) [DecidableRel J.Adj] (A : Finset V) (x : V) :
    (crossed J A x).card = nbr J x (if x∈A then Aᶜ else A) := by
  unfold crossed nbr
  congr 1
  ext w
  by_cases xA : x∈A <;> simp [xA,and_comm]

theorem choose_max_with (J : SimpleGraph V) [DecidableRel J.Adj] (v : V) :
    ∃ A : Finset V, Maximum J A ∧ v∈A := by
  obtain ⟨A,_,top⟩ := exists_max_image (univ : Finset (Finset V))
    (fun A=>Graffiti384b.cut J A Aᶜ) univ_nonempty
  have mx : Maximum J A := fun S=>top S (mem_univ _)
  by_cases vA : v∈A
  · exact ⟨A,mx,vA⟩
  · exact ⟨Aᶜ,OddStars.LeafCritical.max_compl J mx,mem_compl.mpr vA⟩

/-- The exact cut-side restrictions used by the small residual checker. -/
theorem upper_cut_conditions (G : SimpleGraph V) [DecidableRel G.Adj]
    (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {u v : V} {A : Finset V} (max : Maximum (patch G ∅) A)
    (criticalPair : critical (patch G ∅) A={u,v}) :
    let J := patch G ∅
    (∀ x∈high J,x≠u→x≠v→3≤(crossed J A x).card) ∧
    (∀ x∈high J,2≤nbr J x (if x∈A then A else Aᶜ) →
      x∈crossed J A u ∨ x∈crossed J A v) := by
  let J := patch G ∅
  constructor
  · intro x xh xu xv
    change 3≤(crossed J A x).card
    have ge : 2≤(crossed J A x).card := by
      rw [crossed_card]
      by_cases xA : x∈A
      · exact (if_pos xA) ▸ OddStars.LeafCritical.max_covers J max x xh xA
      · have og := OddStars.LeafCritical.max_covers J (OddStars.LeafCritical.max_compl J max)
          x xh (mem_compl.mpr xA)
        rw [compl_compl] at og
        exact (if_neg xA) ▸ og
    have off : (crossed J A x).card≠2 := by
      intro two
      have mem : x∈critical J A := mem_filter.mpr ⟨xh,two⟩
      rw [criticalPair] at mem
      simp only [mem_insert,mem_singleton] at mem
      exact mem.elim xu xv
    omega
  · intro x xh two
    have am : x∈active J A := mem_filter.mpr ⟨xh,two⟩
    obtain ⟨c,cm,xc⟩ := OddStars.ShoreRanks.active_hit G bad size max am
    rw [criticalPair] at cm
    simp only [mem_insert,mem_singleton] at cm
    rcases cm with rfl|rfl
    · exact Or.inl xc
    · exact Or.inr xc

#print axioms upper_cut_conditions
end Graffiti384b.DiversityEleven
