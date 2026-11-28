import DiversityElevenProfile384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Repair.nbr_add Repair.nbr_mono Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An 8-high-board weighted dominating triple closes the pendant branch.
The anchor is a fixed kept vertex; it contributes one unit precisely to
its neighbors. The other retained low vertex only serves the omitted low. -/
theorem exact_of_pendant_triple (t : (types G).card=11) (nine : (high G).card=9)
    {e f a : V} (ea : G.Adj e a) (ef : G.Adj e f) (al : a∈high G)
    (el : e∉high G) (fl : f∉high G)
    {K : Finset V} (incl : K ⊆ (high G).erase a) (three : K.card=3)
    (good : ∀ v∈(high G).erase a \ K, 2≤nbr G v K+(if G.Adj v a then 1 else 0)) :
    gamma G≤bound G := by
  classical
  let U := (high G).erase a
  let O := insert e (U \ K)
  have small : O.card=6 := by
    have en : e∉U \ K := fun h => el (mem_erase.mp (mem_sdiff.mp h).1).2
    change O.card=6
    rw [show O=insert e (U \ K) from rfl,card_insert_of_not_mem en,card_sdiff incl,three]
    have sz : U.card=8 := by dsimp [U]; rw [card_erase_of_mem al,nine]
    rw [show ((high G).erase a).card=8 from sz]
  have ao : a∉O := by
    simp only [O,mem_insert,not_or]
    exact ⟨ea.ne.symm, fun hm => (mem_erase.mp (mem_sdiff.mp hm).1).1 rfl⟩
  have fo : f∉O := by
    simp only [O,mem_insert,not_or]
    exact ⟨ef.ne.symm,fun hm=>fl (mem_erase.mp (mem_sdiff.mp hm).1).2⟩
  have enough : ∀ v∈O, 2≤nbr G v Oᶜ := by
    intro v vm
    rcases (mem_insert.mp vm) with ve|hv
    · subst v
      have sub : ({a,f}:Finset V) ⊆ (Oᶜ).filter (G.Adj e) := by
        intro w wm
        simp only [mem_insert,mem_singleton] at wm
        rcases wm with rfl|rfl
        · exact mem_filter.mpr ⟨mem_compl.mpr ao,ea⟩
        · exact mem_filter.mpr ⟨mem_compl.mpr fo,ef⟩
      have cnt := card_le_card sub
      have af : a≠f := fun eq => fl (eq ▸ al)
      rwa [card_pair af] at cnt
    · have dis : Disjoint K ({a}:Finset V) := disjoint_left.mpr (by
        intro x xk xa
        exact (mem_erase.mp (incl xk)).1 (mem_singleton.mp xa))
      have sub : K∪{a} ⊆ Oᶜ := by
        intro x xm
        apply mem_compl.mpr
        rcases mem_union.mp xm with h|h
        · intro xo
          rcases (mem_insert.mp xo) with rfl|z
          · exact el (mem_erase.mp (incl h)).2
          · exact (mem_sdiff.mp z).2 h
        · exact (mem_singleton.mp h).symm ▸ ao
      have mono := Repair.nbr_mono G v sub
      have one : nbr G v {a} = (if G.Adj v a then 1 else 0) := by
        unfold nbr
        rw [filter_singleton]
        split <;> simp
      rw [Repair.nbr_add G v dis,one] at mono
      exact (good v hv).trans mono
  have c := Repair.omit_set G O enough
  simpa [bound,t,small] using c

#print axioms exact_of_pendant_triple
end Graffiti384b.DiversityEleven
