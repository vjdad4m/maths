import DegreeFiveCommonUniversalFive189
import DegreeFiveBalancedCommonRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Reverse alignment: the common shore has four or five vertices and the
local cut shells are exactly its vertices missing the respective color. -/
theorem reverse_common_shore_geometry
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    4 ≤ (Shore C).card ∧ (Shore C).card ≤ 5 ∧
    (secondShore C a).card+4 = (Shore C).card ∧
    (secondShore C b).card+3 = (Shore C).card := by
  classical
  let K := sharedPortSet C
  let E := secondShore C a
  have dis : Disjoint (portColor D a) (portColor D b) := by
    apply disjoint_left.mpr
    intro w wa wb
    exact none w (mem_filter.mp wa).1 ⟨(mem_filter.mp wa).2,(mem_filter.mp wb).2⟩
  have union : portColor D a ∪ portColor D b = cutPorts D := by
    ext w
    simp [portColor,cutPorts,and_or_left]
  have five : (cutPorts D).card=5 := by
    rw [←union,card_union_of_disjoint dis,pA,pB]
  obtain ⟨x,xk⟩ := card_pos.mp (show 0<K.card by exact lt_of_lt_of_le (by decide) shared)
  obtain ⟨xc,ax,bx⟩ := mem_filter.mp xk
  have uni := common_universal_in_shore_at_five hc even cd xc ax bx five
  obtain ⟨u,up,uh⟩ := anywhere_high_of_two degree (show 2 ≤ (portColor D a).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  have bu : ¬G.Adj b u := fun h=>none u ud ⟨au,h⟩
  have hu := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc ud au uh
  rw [if_neg bu] at hu
  change 5 ≤ (portColor D a).card+(secondShore D a).card at hu
  have he := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have e1 : E.card ≤ 1 := by change (secondShore C a).card ≤ 1; omega
  have part (c : V) (hit : G.Adj c x) (co : c∉Shore C) :
      (portColor C c).card + (secondShore C c).card = (Shore C).card := by
    let P := portColor C c
    let Q := secondShore C c
    have dis : Disjoint P Q := by
      apply disjoint_left.mpr
      intro w wp wq
      have one := dist_eq_one_iff_adj.mpr (mem_filter.mp wp).2
      have two := (mem_filter.mp (mem_inter.mp wq).2).2
      omega
    have eq : P∪Q=Shore C := by
      apply le_antisymm
      · exact union_subset (filter_subset _ _) inter_subset_left
      intro w wc
      by_cases cw : G.Adj c w
      · exact mem_union_left _ (mem_filter.mpr ⟨wc,cw⟩)
      have xw : x≠w := fun h=>cw (h ▸ hit)
      have cw' : c≠w := fun h=>co (h.symm ▸ wc)
      exact mem_union_right _ (mem_inter.mpr ⟨wc,d2 hc cw' cw hit (uni w wc xw)⟩)
    have h := congrArg Finset.card eq
    rwa [card_union_of_disjoint dis] at h
  have pa := part a ax (shore_off C).1
  have pb := part b bx (shore_off C).2
  rw [cA] at pa
  rw [cB] at pb
  change (secondShore C a).card ≤ 1 at e1
  exact ⟨by omega,by omega,by omega,by omega⟩

#print axioms reverse_common_shore_geometry
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
