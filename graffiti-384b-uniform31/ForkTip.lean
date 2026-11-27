import TenGap
import FlexibleTip
namespace Graffiti384b.TenPins
open Finset SimpleGraph ForkGuard34 LowSample EightPins SparsePairs
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Cover the other anchors simultaneously. Private three-vertex paths in
their rows and vertices touching multiple anchors supply disjoint pins. -/
theorem fork_tip {W : Finset V} (data : AnchorData G W) {r : V} (rr : r∈W)
    (privateR : ∀z∈row G W r,nbr G z W=1) (gap : ∀a∈W,a≠r → 10≤trianglesAt G a) :
    ∃ P Q,W⊆P ∧ twos G⊆Q ∧ Tip G P Q r ∧ Disjoint (row G W r) (P∪Q) := by
  classical
  have wh := data.highPins; have ears := data.ears; have anchor := data.owns
  let C := candidates G W
  let Q := twos G∪C
  let B := W.filter (fun w => w≠r ∧ nbr G w Q<2)
  have base (v : V) (vq : v∈Q) : 2≤nbr G v W := by
    rcases mem_union.mp vq with ve|vc
    · have inc : G.neighborFinset v⊆W.filter (G.Adj v) := fun i im => mem_filter.mpr ⟨ears v ve im,(G.mem_neighborFinset _ _).mp im⟩
      have le := card_le_card inc
      rw [card_neighborFinset_eq_degree] at le
      exact (mem_filter.mp (mem_sdiff.mp ve).1).2.trans le
    · exact (mem_filter.mp vc).2
  have blind (w : V) (wb : w∈B) {j : V} (jc : j∈C) : ¬G.Adj w j := by
    intro edge
    obtain ⟨e,el,we⟩ := anchor w (mem_filter.mp wb).1
    have ne : e≠j := fun eq => (mem_sdiff.mp el).2 (eq ▸ (mem_sdiff.mp (mem_filter.mp jc).1).1)
    have two := PinnedColor34.two G ne we edge (mem_union_left C el) (mem_union_right (twos G) jc)
    exact (not_lt_of_ge two) (mem_filter.mp wb).2.2
  have rowOut {w v : V} (wb : w∈B) (vm : v∈row G W w) : v∉W ∧ v∉Q := by
    obtain ⟨outside,wv⟩ := mem_filter.mp vm
    exact ⟨(mem_sdiff.mp outside).2,fun vq => (mem_union.mp vq).elim (fun ve => (mem_sdiff.mp ve).2 (mem_sdiff.mp outside).1)
      (fun vc => blind w wb vc wv)⟩
  have own {u v j : V} (ub : u∈B) (vb : v∈B) (ju : j∈row G W u) (jv : j∈row G W v) : u=v := by
    by_contra ne
    obtain ⟨out,uj⟩ := mem_filter.mp ju
    have vj := (mem_filter.mp jv).2
    have hit := PinnedColor34.two G ne uj.symm vj.symm (mem_filter.mp ub).1 (mem_filter.mp vb).1
    exact blind u ub (mem_filter.mpr ⟨out,hit⟩) uj
  have existsM (w : V) (wb : w∈B) : ∃ m∈row G W w,2≤nbr G m (row G W w) := by
    by_contra! missing
    have ww := (mem_filter.mp wb).1
    obtain ⟨p,pw,pd⟩ := data.sparsePin
    have mixed : ∀ i∈high G\W,∀j∈W,G.Adj w i → G.Adj w j → ¬G.Adj i j := by
      intro i ix j jw wi wj ij
      have two := PinnedColor34.two G wj.ne wi.symm ij ww jw
      exact blind w wb (mem_filter.mpr ⟨ix,two⟩) wi
    have cap := link_budget G W data.four ww pw pd (data.singleEar w ww) false true
      (fun _ i im => by change nbr G i (row G W w)≤1; have h := missing i im; omega) (fun _ => mixed)
    have sz := data.rowSize w ww
    have lower := gap w ww (mem_filter.mp wb).2.1
    simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero] at cap
    split at cap <;> omega
  let mid (w : V) := if wb : w∈B then (existsM w wb).choose else w
  have prop (w : V) (wb : w∈B) : mid w∈row G W w ∧ 2≤nbr G (mid w) (row G W w) := by
    simpa only [mid,dif_pos wb] using (existsM w wb).choose_spec
  let ends (w : V) := (row G W w).filter (G.Adj (mid w))
  let M := B.image mid
  let X := B.biUnion ends
  let P := W∪M
  let S := Q∪X
  have pq : Disjoint P S := disjoint_left.mpr (by
    intro v vp vs
    rcases mem_union.mp vp with vw|vm <;> rcases mem_union.mp vs with vq|vx
    · rcases mem_union.mp vq with vl|vc
      · exact (mem_sdiff.mp vl).2 (wh vw)
      · exact (mem_sdiff.mp (mem_filter.mp vc).1).2 vw
    · obtain ⟨w,wb,ve⟩ := mem_biUnion.mp vx
      exact (rowOut wb (mem_filter.mp ve).1).1 vw
    · obtain ⟨w,wb,rfl⟩ := mem_image.mp vm
      exact (rowOut wb (prop w wb).1).2 vq
    · obtain ⟨w,wb,rfl⟩ := mem_image.mp vm
      obtain ⟨u,ub,ve⟩ := mem_biUnion.mp vx
      have eq := own wb ub (prop w wb).1 (mem_filter.mp ve).1
      subst u
      exact (mem_filter.mp ve).2.ne rfl)
  obtain ⟨u,ue,ru⟩ := anchor r rr
  refine ⟨P,S,subset_union_left,subset_union_left.trans subset_union_left,⟨pq,mem_union_left _ rr,
    ⟨u,mem_union_left _ (mem_union_left _ ue),ru⟩,?_,?_⟩,?_⟩
  · have endS (w : V) (wb : w∈B) : ends w⊆S := fun v ve => mem_union_right _ (mem_biUnion.mpr ⟨w,wb,ve⟩)
    intro v vp vr
    rcases mem_union.mp vp with vw|vm
    · by_cases wb : v∈B
      · have inc : ends v⊆S.filter (G.Adj v) := fun i im => mem_filter.mpr ⟨endS v wb im,(mem_filter.mp (mem_filter.mp im).1).2⟩
        exact (prop v wb).2.trans (card_le_card inc)
      · exact (show 2≤nbr G v Q from Nat.le_of_not_gt (fun small => wb (mem_filter.mpr ⟨vw,vr,small⟩))).trans (Repair.nbr_mono G v subset_union_left)
    · obtain ⟨w,wb,rfl⟩ := mem_image.mp vm
      have inc : ends w⊆S.filter (G.Adj (mid w)) := fun i im => mem_filter.mpr ⟨endS w wb im,(mem_filter.mp im).2⟩
      exact (prop w wb).2.trans (card_le_card inc)
  · intro v vs
    rcases mem_union.mp vs with vq|vx
    · exact (base v vq).trans (Repair.nbr_mono G v subset_union_left)
    · obtain ⟨w,wb,ve⟩ := mem_biUnion.mp vx
      have vw := (mem_filter.mp (mem_filter.mp ve).1).2.symm
      have vm := (mem_filter.mp ve).2.symm
      have ne := (mem_filter.mp (prop w wb).1).2.ne
      exact PinnedColor34.two G ne vw vm (mem_union_left M (mem_filter.mp wb).1) (mem_union_right W (mem_image.mpr ⟨w,wb,rfl⟩))
  · apply disjoint_left.mpr
    intro z zm pins
    have zx := (mem_filter.mp zm).1; have rz := (mem_filter.mp zm).2
    have lone := privateR z zm
    have clash {a : V} (ab : a∈B) (az : z∈row G W a) : False := by
      have aw := (mem_filter.mp ab).1; have ar := (mem_filter.mp ab).2.1
      have two := PinnedColor34.two G ar (mem_filter.mp az).2.symm rz.symm aw rr; omega
    rcases mem_union.mp pins with pin|pin
    · rcases mem_union.mp pin with zw|midPin
      · exact (mem_sdiff.mp zx).2 zw
      · obtain ⟨a,ab,eq⟩ := mem_image.mp midPin; exact clash ab (eq ▸ (prop a ab).1)
    · rcases mem_union.mp pin with basePin|endPin
      · rcases mem_union.mp basePin with ze|zh
        · exact (mem_sdiff.mp ze).2 (mem_sdiff.mp zx).1
        · have high := (mem_filter.mp zh).2; change 2≤nbr G z W at high; omega
      · obtain ⟨a,ab,az⟩ := mem_biUnion.mp endPin; exact clash ab (mem_filter.mp az).1

end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.fork_tip
