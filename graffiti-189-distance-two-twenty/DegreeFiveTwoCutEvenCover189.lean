import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary right_boundary from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

private theorem mem_even_at {x z : V} : z∈EvenFrom G x ↔ Even (G.dist x z) := by
  classical
  simp [EvenFrom]

private theorem even_next_of_not_even {n : ℕ} (h : ¬Even n) : Even (1+n) := by
  simp only [Nat.even_iff] at h ⊢
  omega

private theorem cover_by_five_even_sets
    (hc : G.Connected) {x u v : V}
    (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (uR : u∈S.R) (au : G.Adj a u) (vR : v∈S.R) (bv : G.Adj b v) :
    (univ : Finset V)⊆(EvenFrom G a∪EvenFrom G b)∪
      (EvenFrom G x∪EvenFrom G u∪EvenFrom G v) := by
  classical
  intro z _
  rcases S.cover z with rfl|rfl|zl|zr
  · exact mem_union_left _ (mem_union_left _ (mem_even_at.mpr (by simp [SimpleGraph.dist_self])))
  · exact mem_union_left _ (mem_union_right _ (mem_even_at.mpr (by simp [SimpleGraph.dist_self])))
  · by_cases az : G.dist a z≤G.dist b z
    · by_cases e : Even (G.dist a z)
      · exact mem_union_left _ (mem_union_left _ (mem_even_at.mpr e))
      have eq := cross_metric S.R hc uR (fun h=>disjoint_left.mp S.dis zl h) (right_boundary S)
      have step := dist_eq_one_iff_adj.mpr au.symm
      have pos : 0<G.dist u b := by
        have n : G.dist u b≠0 := fun h=>S.rightOff.2 ((hc.dist_eq_zero_iff.mp h) ▸ uR)
        omega
      have hz : G.dist u z=1+G.dist a z := by omega
      exact mem_union_right _ (mem_union_left _ (mem_union_right _ (mem_even_at.mpr
        (hz.symm ▸ even_next_of_not_even e))))
    by_cases e : Even (G.dist b z)
    · exact mem_union_left _ (mem_union_right _ (mem_even_at.mpr e))
    have eq := cross_metric S.R hc vR (fun h=>disjoint_left.mp S.dis zl h) (right_boundary S)
    have step := dist_eq_one_iff_adj.mpr bv.symm
    have pos : 0<G.dist v a := by
      have n : G.dist v a≠0 := fun h=>S.rightOff.1 ((hc.dist_eq_zero_iff.mp h) ▸ vR)
      omega
    have hz : G.dist v z=1+G.dist b z := by omega
    exact mem_union_right _ (mem_union_right _ (mem_even_at.mpr (hz.symm ▸ even_next_of_not_even e)))
  have eq := cross_metric S.L hc xL (fun h=>disjoint_left.mp S.dis h zr) (left_boundary S)
  have xa := dist_eq_one_iff_adj.mpr ax.symm
  have xb := dist_eq_one_iff_adj.mpr bx.symm
  have hit (e : Even (G.dist x z)) :
      z∈(EvenFrom G a∪EvenFrom G b)∪(EvenFrom G x∪EvenFrom G u∪EvenFrom G v) :=
    mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_even_at.mpr e)))
  by_cases az : G.dist a z≤G.dist b z
  · by_cases e : Even (G.dist a z)
    · exact mem_union_left _ (mem_union_left _ (mem_even_at.mpr e))
    have hz : G.dist x z=1+G.dist a z := by omega
    exact hit (hz.symm ▸ even_next_of_not_even e)
  by_cases e : Even (G.dist b z)
  · exact mem_union_left _ (mem_union_right _ (mem_even_at.mpr e))
  have hz : G.dist x z=1+G.dist b z := by omega
  exact hit (hz.symm ▸ even_next_of_not_even e)

private theorem even_pair_overlap_of_dist_two {x y : V} (two : G.dist x y=2) :
    2≤(EvenFrom G x∩EvenFrom G y).card := by
  classical
  have ne : x≠y := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have rev : G.dist y x=2 := by rwa [SimpleGraph.dist_comm]
  have sub : ({x,y} : Finset V)⊆EvenFrom G x∩EvenFrom G y := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact mem_inter.mpr ⟨mem_even_at.mpr (by simp [SimpleGraph.dist_self]),
        mem_even_at.mpr (by simp [rev])⟩
    exact mem_inter.mpr ⟨mem_even_at.mpr (by simp [two]),
      mem_even_at.mpr (by simp [SimpleGraph.dist_self])⟩
  have k := card_le_card sub
  simpa [ne] using k

/-- Two radius-parity sets centered two steps apart share both centers,
so under a cap of six their union has at most ten vertices. -/
theorem even_union_le_ten_of_dist_two {x y : V}
    (two : G.dist x y=2) (even : ∀ z,(EvenFrom G z).card≤6) :
    (EvenFrom G x∪EvenFrom G y).card≤10 := by
  have c := card_union_add_card_inter (EvenFrom G x) (EvenFrom G y)
  have low := even_pair_overlap_of_dist_two two
  have x6 := even x
  have y6 := even y
  omega

private theorem cross_common_distance_two
    (hc : G.Connected) {x u : V} (xL : x∈S.L) (uR : u∈S.R)
    (hit : (G.Adj a x ∧ G.Adj a u) ∨ (G.Adj b x ∧ G.Adj b u)) :
    G.dist x u=2 := by
  have ne : x≠u := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ uR)
  have no := S.cross x xL u uR
  have hd : u∈DistanceTwo G x :=
    hit.elim (fun e=>d2 hc ne no e.1.symm e.2) (fun e=>d2 hc ne no e.1.symm e.2)
  simpa [DistanceTwo] using hd

theorem order_le_twenty_four_at_distance_two_two_shores
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ z,(EvenFrom G z).card≤6)
    {x u v : V}
    (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (uR : u∈S.R) (au : G.Adj a u) (vR : v∈S.R) (bv : G.Adj b v) :
    Fintype.card V≤24 := by
  classical
  let A := EvenFrom G a∪EvenFrom G b
  let X := EvenFrom G x
  let U := EvenFrom G u
  let W := EvenFrom G v
  have ab := even_union_le_ten_of_dist_two two even
  have xu := cross_common_distance_two S hc xL uR (.inl ⟨ax,au⟩)
  have xv := cross_common_distance_two S hc xL vR (.inr ⟨bx,bv⟩)
  have w := even_pair_overlap_of_dist_two xv
  have h := card_union_add_card_inter (X∪U) W
  have mono : X∩W⊆(X∪U)∩W :=
    fun _ q=>mem_inter.mpr ⟨mem_union_left _ (mem_inter.mp q).1,(mem_inter.mp q).2⟩
  have wt : (X∩W).card≤((X∪U)∩W).card := card_le_card mono
  have mid := even_union_le_ten_of_dist_two xu even
  have v6 := even v
  change 2≤(X∩W).card at w
  change (X∪U).card≤10 at mid
  change W.card≤6 at v6
  have tail : (X∪U∪W).card≤14 := by omega
  have cover := cover_by_five_even_sets S hc xL ax bx uR au vR bv
  have all := (card_le_card cover).trans (card_union_le A (X∪U∪W))
  rw [card_univ] at all
  change A.card≤10 at ab
  omega

theorem order_le_twenty_at_distance_two_with_common_on_both
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ z,(EvenFrom G z).card≤6)
    {x y : V}
    (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (yR : y∈S.R) (ay : G.Adj a y) (by' : G.Adj b y) :
    Fintype.card V≤20 := by
  classical
  have ab := even_union_le_ten_of_dist_two two even
  have xy := cross_common_distance_two S hc xL yR (.inl ⟨ax,ay⟩)
  have extra := even_union_le_ten_of_dist_two xy even
  have cov := cover_by_five_even_sets S hc xL ax bx yR ay yR by'
  have shortened : (univ : Finset V)⊆
      (EvenFrom G a∪EvenFrom G b)∪(EvenFrom G x∪EvenFrom G y) := by
    simpa [Finset.union_assoc] using cov
  have tot := (card_le_card shortened).trans (card_union_le _ _)
  rw [card_univ] at tot
  omega

#print axioms even_union_le_ten_of_dist_two
#print axioms order_le_twenty_four_at_distance_two_two_shores
#print axioms order_le_twenty_at_distance_two_with_common_on_both
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem order_bounds_at_actual_five_distance_two_cut {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    :
    Fintype.card V≤24 ∧
      ((∀ C : (CutGraph (G:=G) a b).ConnectedComponent,
        ∃ x∈Shore C,G.Adj a x ∧ G.Adj b x) → Fintype.card V≤20) := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  refine ⟨?_,?_⟩
  · obtain ⟨u,ur,au⟩ := shore_hit_a ab conn D
    obtain ⟨v,vr,bv⟩ := shore_hit_b ab conn D
    exact Split.Five.order_le_twenty_four_at_distance_two_two_shores S hc two even
      xC ax xb.symm ur au vr bv
  intro both
  obtain ⟨y,yR,ay,by'⟩ := both D
  exact Split.Five.order_le_twenty_at_distance_two_with_common_on_both S hc two even
    xC ax xb.symm yR ay by'

#print axioms order_bounds_at_actual_five_distance_two_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
