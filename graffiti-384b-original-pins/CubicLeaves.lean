import PrivateLink
namespace Graffiti384b.OddStars.CubicLeaves
open Finset SimpleGraph LeafCritical
open private Graffiti384b.cut Graffiti384b.nbr_partition from Proof384b
open private OddStars.LeafCritical.exposed_side from LeafExposure
open private OddStars.LeafCritical.max_compl OddStars.LeafCritical.crit_cubic_side from LeafCritical
open private OddStars.crossing OddStars.translated from CutAtVertex
open private OddStars.ShoreCounts.in_high from ShoreCounts
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At a cubic, the unique same-shore skeletal neighbor is the only
original neighbor outside the opposite high shore. -/
theorem sole_neighbor (conn : G.Connected) (order : 2<Fintype.card V) (bad : bound G<gamma G)
    (one : 1∉types G) {A : Finset V} (m : Maximum (patch G ∅) A) {w : V}
    (dw : (patch G ∅).degree w=3) (wa : w∈A) :
    ((high (patch G ∅)\A)ᶜ.filter (G.Adj w))=A.filter ((patch G ∅).Adj w) := by
  let J := patch G ∅
  let H := high J
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  obtain ⟨_,u,v,_,_,_,uv,cub,crit⟩ := PaletteCorollaries.missing_one_failure G conn order bad one
  have wc : w∈critical J A := by
    rw [crit _ m]
    simpa only [mem_insert,mem_singleton] using (cub _).mp dw
  have cross := (mem_filter.mp wc).2
  change (OddStars.crossing J A w).card=2 at cross
  rw [OddStars.translated,if_pos wa] at cross
  have decomp := Graffiti384b.nbr_partition J w A
  have unit : (A.filter (J.Adj w)).card=1 := by
    change nbr J w A=1
    change J.degree w=3 at dw
    omega
  have thin : nbr G w (H\A)ᶜ≤1 := by
    by_contra! many
    obtain ⟨y,yh,yo,yw,two⟩ := OddStars.LeafCritical.exposed_side G bad sz m wa many
    have dy := OddStars.LeafCritical.crit_cubic_side G bad sz (OddStars.LeafCritical.max_compl J m)
      yh yo (by simpa only [compl_compl] using two)
    rcases (cub _).mp dw with rfl|rfl <;> rcases (cub _).mp dy with rfl|rfl
    · exact yw.ne rfl
    · exact uv yw.symm
    · exact uv yw
    · exact yw.ne rfl
  symm
  apply eq_of_subset_of_card_le
  · intro y ym
    obtain ⟨ya,wy⟩ := mem_filter.mp ym
    exact mem_filter.mpr ⟨mem_compl.mpr (fun k => (mem_sdiff.mp k).2 ya),wy.1⟩
  · rw [unit]; exact thin

/-- All original neighbors of a skeletal cubic are high in the skeleton.
Every unsupported edge at either cubic crosses every maximum skeletal cut. -/
theorem forced_crossing (conn : G.Connected) (order : 2<Fintype.card V) (bad : bound G<gamma G)
    (one : 1∉types G) {A : Finset V} (m : Maximum (patch G ∅) A) {w y : V}
    (dw : (patch G ∅).degree w=3) (edge : G.Adj w y) :
    y∈high (patch G ∅) ∧ (¬(patch G ∅).Adj w y → ¬(w∈A ↔ y∈A)) := by
  classical
  let J := patch G ∅
  let H := high J
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have side {B : Finset V} (wb : w∈B) (mx : Maximum J B) : y∈H ∧ (y∈B → J.Adj w y) := by
    have eq := sole_neighbor G conn order bad one mx dw wb
    have visible (ym : y∉H ∨ y∈B) : J.Adj w y := by
      have mem : y∈(H\B)ᶜ.filter (G.Adj w) := mem_filter.mpr ⟨mem_compl.mpr
        (fun k => ym.elim (fun no => no (mem_sdiff.mp k).1) (mem_sdiff.mp k).2),edge⟩
      rw [eq] at mem
      exact (mem_filter.mp mem).2
    exact ⟨by
      by_contra no
      exact no (OddStars.ShoreCounts.in_high G bad sz (visible (Or.inl no))),fun yb => visible (Or.inr yb)⟩
  by_cases wa : w∈A
  · obtain ⟨yh,adj⟩ := side wa m
    exact ⟨yh,fun no eq => no (adj (eq.mp wa))⟩
  · obtain ⟨yh,adj⟩ := side (mem_compl.mpr wa) (OddStars.LeafCritical.max_compl J m)
    exact ⟨yh,fun no eq => no (adj (mem_compl.mpr (fun ya => wa (eq.mpr ya))))⟩

/-- A zero-count neighbor at either skeletal cubic suffices for the
catalogue inequality, at every order. -/
theorem exact_zero_at_cubic (conn : G.Connected) (order : 2<Fintype.card V) (one : 1∉types G)
    {w z : V} (dw : (patch G ∅).degree w=3) (edge : G.Adj w z) (zero : trianglesAt G z=0) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  let J := patch G ∅
  obtain ⟨A,_,opt⟩ := exists_max_image (univ : Finset (Finset V)) (fun A => Graffiti384b.cut J A Aᶜ) univ_nonempty
  have mx : Maximum J A := fun S => opt _ (mem_univ S)
  have zH := (forced_crossing G conn order bad one mx dw edge).1
  have low := skeleton_degree_bound G z
  have hi : 3≤J.degree z := (mem_filter.mp zH).2
  rw [zero] at low
  change J.degree z≤2*0 at low
  omega

end Graffiti384b.OddStars.CubicLeaves
#print axioms Graffiti384b.OddStars.CubicLeaves.sole_neighbor
#print axioms Graffiti384b.OddStars.CubicLeaves.forced_crossing
#print axioms Graffiti384b.OddStars.CubicLeaves.exact_zero_at_cubic
