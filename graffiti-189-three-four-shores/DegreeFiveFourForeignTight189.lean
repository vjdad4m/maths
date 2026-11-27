import DegreeFiveTwoFourShapes189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget all_adj_of_no_second from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem tight_four_foreign_charges_exclude_port_neighbors
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    let E := Shore C \ cutPorts C
    let F := Shore D \ cutPorts D
    let A := E.filter (G.Adj x)
    let B := F.filter (fun z=>G.dist x z≠4)
    2*A.card+B.card=8 →
      ∀ z∈E,z∉A → ∀ w∈cutPorts C,¬G.Adj z w := by
  classical
  dsimp only
  let E := Shore C \ cutPorts C
  let F := Shore D \ cutPorts D
  let A := E.filter (G.Adj x)
  let B := F.filter (fun z=>G.dist x z≠4)
  let LA := secondShore C a
  let LB := secondShore C b
  let RA := secondShore D a
  let RB := secondShore D b
  obtain ⟨_,_,_,dom⟩ := four_foreign_near_with_exception hc two even conn cd cover D4 xc ax bx
  have ad : A⊆LA := by
    intro z az
    obtain ⟨ze,xz⟩ := mem_filter.mp az
    obtain ⟨zc,nP⟩ := mem_sdiff.mp ze
    have n : ¬G.Adj a z := fun h=>nP (mem_filter.mpr ⟨zc,.inl h⟩)
    have ne : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc ne n ax xz⟩
  have bd : A⊆LB := by
    intro z az
    obtain ⟨ze,xz⟩ := mem_filter.mp az
    obtain ⟨zc,nP⟩ := mem_sdiff.mp ze
    have n : ¬G.Adj b z := fun h=>nP (mem_filter.mpr ⟨zc,.inr h⟩)
    have ne : b≠z := fun e=>(shore_off C).2 (e.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc ne n bx xz⟩
  have choices : B⊆RA∪RB := by
    intro z bz
    obtain ⟨zf,no4⟩ := mem_filter.mp bz
    obtain ⟨zd,nP⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := (dom z zd nP).resolve_left no4
    obtain ⟨_,aw|bw⟩ := mem_filter.mp wp
    · have ne : a≠z := fun e=>(shore_off D).1 (e.symm ▸ zd)
      have n : ¬G.Adj a z := fun h=>nP (mem_filter.mpr ⟨zd,.inl h⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨zd,d2 hc ne n aw zw.symm⟩)
    have ne : b≠z := fun e=>(shore_off D).2 (e.symm ▸ zd)
    have n : ¬G.Adj b z := fun h=>nP (mem_filter.mpr ⟨zd,.inr h⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zd,d2 hc ne n bw zw.symm⟩)
  have la := card_le_card ad
  have lb := card_le_card bd
  have tally := (card_le_card choices).trans (card_union_le RA RB)
  have sumA : LA.card+RA.card≤4 :=
    two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have sumB : LB.card+RB.card≤4 :=
    two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ (by rwa [dist_comm]) even
  change 2*A.card+B.card=8 → ∀ z∈E,z∉A → ∀ w∈cutPorts C,¬G.Adj z w
  intro tight z ze za w wp zw
  obtain ⟨zc,zp⟩ := mem_sdiff.mp ze
  obtain ⟨wc,aw|bw⟩ := mem_filter.mp wp
  · have no : ¬G.Adj a z := fun e=>zp (mem_filter.mpr ⟨zc,.inl e⟩)
    have ne : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zc)
    have zL : z∈LA := mem_inter.mpr ⟨zc,d2 hc ne no aw zw.symm⟩
    have charge := card_le_card (insert_subset_iff.mpr ⟨zL,ad⟩)
    rw [card_insert_of_not_mem za] at charge
    omega
  have no : ¬G.Adj b z := fun e=>zp (mem_filter.mpr ⟨zc,.inr e⟩)
  have ne : b≠z := fun e=>(shore_off C).2 (e.symm ▸ zc)
  have zL : z∈LB := mem_inter.mpr ⟨zc,d2 hc ne no bw zw.symm⟩
  have charge := card_le_card (insert_subset_iff.mpr ⟨zL,bd⟩)
  rw [card_insert_of_not_mem za] at charge
  omega

#print axioms tight_four_foreign_charges_exclude_port_neighbors
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
