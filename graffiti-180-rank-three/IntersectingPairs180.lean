import Proof177

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset
variable {I V : Type*} [DecidableEq V]

/-- A nonempty intersecting family of pairs has a common point or consists
of all three pairs on a triple (duplicates in the indexing are allowed). -/
theorem intersecting_pairs (F : I→Finset V) (Q : I→Prop) (nz : ∃ i,Q i)
    (two : ∀ i,Q i → (F i).card=2) (meet : ∀ i,Q i → ∀ j,Q j → (F i∩F j).Nonempty) :
    (∃ z,∀ i,Q i → z∈F i) ∨ ∃ a b c : V,a≠b ∧ a≠c ∧ b≠c ∧
      (∃ i,Q i ∧ F i={a,b}) ∧ (∃ i,Q i ∧ F i={b,c}) ∧ (∃ i,Q i ∧ F i={a,c}) ∧
      ∀ i,Q i → F i={a,b} ∨ F i={b,c} ∨ F i={a,c} := by
  classical
  by_cases common : ∃ z,∀ i,Q i → z∈F i
  · exact Or.inl common
  obtain ⟨i,qi⟩ := nz
  obtain ⟨a,b,ab,pi⟩ := card_eq_two.mp (two i qi)
  have missing (z : V) : ∃ j,Q j ∧ z∉F j := by
    by_contra! no
    exact common ⟨z,no⟩
  obtain ⟨j,qj,na⟩ := missing a
  obtain ⟨k,qk,nb⟩ := missing b
  have one (l : I) (ql : Q l) : a∈F l ∨ b∈F l := by
    obtain ⟨w,hw⟩ := meet i qi l ql
    obtain ⟨wi,wl⟩ := mem_inter.mp hw
    rw [pi] at wi
    rcases mem_insert.mp wi with rfl|wb
    · exact Or.inl wl
    · exact Or.inr ((mem_singleton.mp wb) ▸ wl)
  have bj := (one j qj).resolve_left na
  have ak := (one k qk).resolve_right nb
  obtain ⟨c,hc⟩ := meet j qj k qk
  obtain ⟨cj,ck⟩ := mem_inter.mp hc
  have ac : a≠c := fun eq => na (eq ▸ cj)
  have bc : b≠c := fun eq => nb (eq ▸ ck)
  have pair {l : I} (ql : Q l) {s t : V} (st : s≠t) (sl : s∈F l) (tl : t∈F l) :
      F l={s,t} := (eq_of_subset_of_card_le (insert_subset sl (singleton_subset_iff.mpr tl))
        (by rw [two l ql,card_pair st])).symm
  have pj := pair qj bc bj cj
  have pk := pair qk ac ak ck
  refine Or.inr ⟨a,b,c,ab,ac,bc,⟨i,qi,pi⟩,⟨j,qj,pj⟩,⟨k,qk,pk⟩,?_⟩
  intro l ql
  by_cases al : a∈F l
  · by_cases bl : b∈F l
    · exact Or.inl (pair ql ab al bl)
    obtain ⟨w,hw⟩ := meet j qj l ql
    obtain ⟨wj,wl⟩ := mem_inter.mp hw
    rw [pj] at wj
    have cw : w=c := mem_singleton.mp ((mem_insert.mp wj).resolve_left (fun wb => bl (wb ▸ wl)))
    exact Or.inr (Or.inr (pair ql ac al (cw ▸ wl)))
  · have bl := (one l ql).resolve_left al
    obtain ⟨w,hw⟩ := meet k qk l ql
    obtain ⟨wk,wl⟩ := mem_inter.mp hw
    rw [pk] at wk
    have cw : w=c := mem_singleton.mp ((mem_insert.mp wk).resolve_left (fun wa => al (wa ▸ wl)))
    exact Or.inr (Or.inl (pair ql bc bl (cw ▸ wl)))

#print axioms intersecting_pairs
end Minimal180.HigherRank
