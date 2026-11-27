import DegreeFiveThreeFiveDom189
import DegreeFiveBothNonsaturated189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp two_shore_budget from DegreeFiveThreeForeignImpossible189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private d2 from CrossSaturation189
open private graph_order_le_shores_add_two from DegreeFiveBothNonsaturated189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Rooted five-port saturation forces one charge to a cut endpoint per
nonporter, and two charges for every own-shore nonporter. -/
theorem opposite_five_order_bound_by_double_charges
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (D5 : (cutPorts D).card=5)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    Fintype.card V+(Shore C).card≤15+2*(cutPorts C).card := by
  classical
  let E := Shore C \ cutPorts C
  let F := Shore D \ cutPorts D
  let A := secondShore C a∪secondShore D a
  let B := secondShore C b∪secondShore D b
  have eS : E⊆Shore C := sdiff_subset
  have fS : F⊆Shore D := sdiff_subset
  have es : E.card+(cutPorts C).card=(Shore C).card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have fs : F.card+5=(Shore D).card := by
    have h : F.card+(cutPorts D).card=(Shore D).card := card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [D5] at h
  have AC : A.card≤4 := (card_union_le _ _).trans
    (two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even)
  have BC : B.card≤4 := (card_union_le _ _).trans
    (two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ (by rwa [dist_comm]) even)
  have eAB : E⊆A∩B := by
    intro z zz
    obtain ⟨zc,np⟩ := mem_sdiff.mp zz
    have no : ¬(G.Adj a z ∨ G.Adj b z) := fun e=>np (mem_filter.mpr ⟨zc,e⟩)
    have xz := common_universal_in_shore_at_five hc even cd xc ax bx D5 z zc
      (fun e=>no (.inl (e ▸ ax)))
    have az := d2 hc (show a≠z from fun e=>(shore_off C).1 (e.symm ▸ zc)) (fun h=>no (.inl h)) ax xz
    have bz := d2 hc (show b≠z from fun e=>(shore_off C).2 (e.symm ▸ zc)) (fun h=>no (.inr h)) bx xz
    exact mem_inter.mpr ⟨mem_union_left _ (mem_inter.mpr ⟨zc,az⟩),
      mem_union_left _ (mem_inter.mpr ⟨zc,bz⟩)⟩
  have fAB : F⊆A∪B := by
    intro z zz
    obtain ⟨zd,np⟩ := mem_sdiff.mp zz
    have no : ¬(G.Adj a z ∨ G.Adj b z) := fun e=>np (mem_filter.mpr ⟨zd,e⟩)
    obtain ⟨w,wp,zw⟩ := (saturated_common_foreign_port_domination hc even cd D5 xc ax bx).2 z zd np
    obtain ⟨_,aw|bw⟩ := mem_filter.mp wp
    · have az := d2 hc (show a≠z from fun e=>(shore_off D).1 (e.symm ▸ zd)) (fun h=>no (.inl h)) aw zw.symm
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨zd,az⟩))
    have bz := d2 hc (show b≠z from fun e=>(shore_off D).2 (e.symm ▸ zd)) (fun h=>no (.inr h)) bw zw.symm
    exact mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨zd,bz⟩))
  have included : E∪F⊆A∪B := union_subset
    (fun _ h=>mem_union_left _ (mem_inter.mp (eAB h)).1) fAB
  have bound := card_le_card included
  rw [card_union_of_disjoint ((shore_disjoint cd).mono eS fS)] at bound
  have double := card_le_card eAB
  have budget := card_union_add_card_inter A B
  have order := graph_order_le_shores_add_two cover
  omega

#print axioms opposite_five_order_bound_by_double_charges
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
