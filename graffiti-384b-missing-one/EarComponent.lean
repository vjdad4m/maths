import MissingOne
namespace Graffiti384b.OddStars.EarComponent
open Finset SimpleGraph ComponentQuota ComponentPort ComponentCenters SingleLeaf

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every positive vertex reaches a vertex of score one along edges in
triangles. Hence all vertices of positive score lie in a single component. -/
theorem every_component_has_one (conn : G.Connected) (bad : bound G<gamma G) {x : V}
    (px : 0<trianglesAt G x) : ∃y,(patch G ∅).Reachable x y ∧ trianglesAt G y=1 := by
  classical
  let S := component G x
  let K := block G S
  obtain ⟨_,_,_,r,ec,lo,_,_,_,failed⟩ := canonical_at G conn bad px
  let E := withLeaf K r
  have order : 2<Fintype.card ((S:Set V)⊕Unit) := by
    have c : Fintype.card (S:Set V)=S.card := Fintype.card_coe S
    rw [Fintype.card_sum,Fintype.card_unit,c]
    exact lo
  have present : 1∈types E := by
    apply Classical.byContradiction; intro no
    exact (not_lt_of_ge (MissingOne.exact E ec order no)) failed
  obtain ⟨v,_,e⟩ := mem_image.mp present
  have scores := leaf_scores K r
  have one : 1∈types K := by
    cases v with
    | inl w => exact mem_image.mpr ⟨w,mem_univ _,(scores.1 w).symm.trans e⟩
    | inr w => cases w; have err := scores.2.1.symm.trans e; omega
  rw [show types K=S.image (trianglesAt G) from local_scores G S (closed_component G x)] at one
  obtain ⟨y,ym,ey⟩ := mem_image.mp one
  exact ⟨y,(mem_component ..).mp ym,ey⟩

theorem positive_connected (conn : G.Connected) (bad : bound G<gamma G) {x y : V}
    (px : 0<trianglesAt G x) (py : 0<trianglesAt G y) : (patch G ∅).Reachable x y := by
  obtain ⟨a,xa,sa⟩ := every_component_has_one G conn bad px
  obtain ⟨b,yb,sb⟩ := every_component_has_one G conn bad py
  exact xa.trans ((equal_score_connected G bad (by omega) (sa.trans sb.symm)).trans yb.symm)

/-- Without any hypothesis on the palette, a disconnected positive
triangle support suffices for the original catalogue bound. -/
theorem exact_disconnected (conn : G.Connected) {x y : V} (px : 0<trianglesAt G x)
    (py : 0<trianglesAt G y) (no : ¬(patch G ∅).Reachable x y) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  exact no (positive_connected G conn bad px py)
end Graffiti384b.OddStars.EarComponent
#print axioms Graffiti384b.OddStars.EarComponent.every_component_has_one
#print axioms Graffiti384b.OddStars.EarComponent.positive_connected
#print axioms Graffiti384b.OddStars.EarComponent.exact_disconnected
