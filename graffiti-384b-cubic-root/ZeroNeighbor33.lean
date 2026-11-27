import CubicRootFinish33

namespace Graffiti384b.RootCut
open Finset SimpleGraph CliquePivot33 PositiveCore33
open private Repair.full_nbr from Repair384b
open private PositiveCore33.positive_clique from CliquePivot33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private HighEar.nonEar from HighEarBypass33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Intrinsic full-graph form. The zero-score vertex may have any degree.
A single neighbor of degree at most four suffices. -/
theorem zero_neighbor_bound (n : Fintype.card V=33) (t : (types G).card=33)
    (conn : G.Connected) {z b : V} (zz : trianglesAt G z=0) (zb : G.Adj z b)
    (db : G.degree b≤4) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have sz : (univ.image (trianglesAt G)).card=(univ : Finset V).card := t.trans (n.symm.trans card_univ.symm)
  have inj : Function.Injective (trianglesAt G) := fun i j eq => (card_image_iff.mp sz) (mem_univ i) (mem_univ j) eq
  let P := ({z}:Finset V)ᶜ
  let H := G.induce (P : Set V)
  let r : P := ⟨b,by simp [P,zb.ne.symm]⟩
  let R := univ.filter (fun v : P => G.Adj v.val z)
  have rr : r∈R := mem_filter.mpr ⟨mem_univ _,zb.symm⟩
  have single : nbr G b {z}=1 := by
    have f : ({z}:Finset V).filter (G.Adj b)={z} := filter_true_of_mem (by intro y m; obtain rfl := mem_singleton.mp m; exact zb.symm)
    exact (congrArg card f).trans (card_singleton _)
  have total := Repair.full_nbr G b {z}
  have reduced : H.degree r≤3 := by rw [EarAnchor.induced_degree]; change nbr G b P≤3; dsimp [P]; omega
  obtain ⟨sp,_,_,pos,distinct,g⟩ := PositiveCore33.extremal_core G n t conn bad inj zz zb
  have tightR : Tight H R := rooted_tight G n t bad z
  have tight : Tight H {r} := by
    intro D cover
    apply tightR D
    intro v out
    have h := cover v out
    by_cases vr : v=r
    · subst v; simpa [rr] using h
    · simp [vr] at h; exact Nat.le_add_right_of_le h
  rcases dichotomy G n t conn bad inj zz zb with low|high
  · obtain ⟨e,_,de,er⟩ := low
    have re : r≠e := fun eq => er (eq ▸ rr)
    have minR := HighEar.nonEar H de re pos distinct
    have dr : H.degree r=3 := by omega
    obtain ⟨a,c,ea,ec,ac⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
    have five : ¬G.CliqueFree 5 := fun free => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free G conn (by omega) t.ge free)) bad
    simp only [CliqueFree,not_forall,Classical.not_not] at five
    obtain ⟨C,cl⟩ := five
    obtain ⟨K,kc⟩ := PositiveCore33.positive_clique G zz cl
    have half : Fintype.card P≤2*gamma H := by rw [Fintype.card_coe]; change P.card=32 at sp; change gamma H=16 at g; omega
    exact cubic_root H dr de ea ec ac pos distinct half kc tight
  · obtain ⟨minH,_,_,miss,_⟩ := high
    have lo : 3≤H.degree r := minH r
    have dr : H.degree r=3 := by omega
    exact miss r (mem_filter.mpr ⟨mem_univ _,dr⟩) rr

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.zero_neighbor_bound
