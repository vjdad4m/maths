import SharedSaving33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph HighEar RootCut CliquePivot33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
open private CubicShore.half_tight from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- At most two vertices of any five-clique miss both cubic neighborhoods.
This also covers a core whose unique score-one vertex is cubic. -/
theorem clique_remainder {u v : V} (du : H.degree u=3) (us : trianglesAt H u=2)
    (dv : H.degree v=3) (vs : trianglesAt H v=3) (pos : ∀ w,0<trianglesAt H w)
    (inj : Function.Injective (trianglesAt H)) {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) :
    (C\(H.neighborFinset u∪H.neighborFinset v)).card≤2 := by
  classical
  let M := C\(H.neighborFinset u∪H.neighborFinset v)
  by_cases low : ∃ e,H.degree e=2
  · obtain ⟨e,de⟩ := low
    obtain ⟨a,c,ea,ec,ac⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
    apply safe_cap H de ea ec ac pos inj tight cl (show M⊆C from sdiff_subset)
    intro x xm w dw _ ed
    rcases cubic_scores H de dw pos inj with two|three
    · obtain rfl := inj (two.trans us.symm)
      exact (mem_sdiff.mp xm).2 (mem_union_left _ ((H.mem_neighborFinset ..).mpr ed))
    · obtain rfl := inj (three.trans vs.symm)
      exact (mem_sdiff.mp xm).2 (mem_union_right _ ((H.mem_neighborFinset ..).mpr ed))
  · have min (w : V) : 2≤H.degree w ∧ (w∉R → 3≤H.degree w) := by
      obtain ⟨a,c,wa,wc,ac⟩ := (TrianglePrune.triangle_iff H w).mp (pos w)
      have d := OneEar.deg2 H ac.ne wa wc
      exact ⟨d,fun _ => by have notTwo : H.degree w≠2 := fun h => low ⟨w,h⟩; omega⟩
    obtain ⟨_,im,light,cov⟩ := three_cubics H R min pos inj tight cl
    let B := univ.filter (fun w => H.degree w=3)
    have image : B.image (trianglesAt H)=Icc 1 3 := im
    obtain ⟨e,em,es⟩ := mem_image.mp (show 1∈B.image (trianglesAt H) from image.symm ▸ (by decide : 1∈Icc 1 3))
    have sub : M⊆C.filter (H.Adj e) := by
      intro x xm
      obtain ⟨xc,off⟩ := mem_sdiff.mp xm
      obtain ⟨w,wm,inside⟩ := mem_biUnion.mp (cov xc)
      have ed := (mem_filter.mp inside).2
      have val : trianglesAt H w∈Icc 1 3 := image ▸ mem_image_of_mem (trianglesAt H) wm
      have ⟨lo,hi⟩ := mem_Icc.mp val
      rcases (show trianglesAt H w=1 ∨ trianglesAt H w=2 ∨ trianglesAt H w=3 by omega) with one|two|three
      · obtain rfl := inj (one.trans es.symm)
        exact mem_filter.mpr ⟨xc,ed⟩
      · obtain rfl := inj (two.trans us.symm)
        exact (off (mem_union_left _ ((H.mem_neighborFinset ..).mpr ed))).elim
      · obtain rfl := inj (three.trans vs.symm)
        exact (off (mem_union_right _ ((H.mem_neighborFinset ..).mpr ed))).elim
    exact (card_le_card sub).trans (light e em).2.2

/-- At order 32 two common neighbors of the two specified cubics force
an ordinary (uncredited) 2-dominating set of size at most fifteen. -/
theorem core_saving {u v p q : V} (n : Fintype.card V=32) (du : H.degree u=3) (us : trianglesAt H u=2)
    (dv : H.degree v=3) (vs : trianglesAt H v=3) (pq : p≠q)
    (up : H.Adj u p) (uq : H.Adj u q) (vp : H.Adj v p) (vq : H.Adj v q)
    (pos : ∀ w,0<trianglesAt H w) (inj : Function.Injective (trianglesAt H)) : gamma H≤15 := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have tight := CubicShore.half_tight H (by omega)
  have hit (C : Finset V) (cl : H.IsNClique 5 C) : p∈C ∨ q∈C := by
    apply Classical.byContradiction; intro outside
    have off := not_or.mp outside
    let P : Finset V := {p,q}
    let A := H.neighborFinset u
    let B := H.neighborFinset v
    have pa : P⊆A := insert_subset ((H.mem_neighborFinset ..).mpr up) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr uq))
    have pb : P⊆B := insert_subset ((H.mem_neighborFinset ..).mpr vp) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr vq))
    have ca : (A\P).card=1 := by rw [card_sdiff pa]; simp [A,P,du,pq]
    have cb : (B\P).card=1 := by rw [card_sdiff pb]; simp [B,P,dv,pq]
    have sub : C∩(A∪B)⊆(A\P)∪(B\P) := by
      intro w wm
      obtain ⟨wc,wn⟩ := mem_inter.mp wm
      have wp : w∉P := by
        intro h; rcases (show w=p ∨ w=q by simpa [P] using h) with rfl|rfl
        · exact off.1 wc
        · exact off.2 wc
      exact (mem_union.mp wn).elim (fun t => mem_union_left _ (mem_sdiff.mpr ⟨t,wp⟩))
        (fun t => mem_union_right _ (mem_sdiff.mpr ⟨t,wp⟩))
    have cap := (card_le_card sub).trans (card_union_le (A\P) (B\P))
    have rem : (C\(A∪B)).card≤2 := clique_remainder H du us dv vs pos inj tight cl
    have all := (card_sdiff_add_card_inter C (A∪B)).trans cl.2
    omega
  exact (not_lt_of_ge (shared_saving H n du us dv vs pq up uq vp vq pos inj hit)) bad

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.clique_remainder
#print axioms Graffiti384b.ForcedCubics.core_saving
