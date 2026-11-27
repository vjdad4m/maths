import DegreeFiveCommonUniversalFive189
import DegreeFiveBalancedCommonRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem common_part_at_universal
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)} {x : V}
    (uni : ∀ w∈Shore C,x≠w → G.Adj x w) (c : V) (hit : G.Adj c x) (co : c∉Shore C) :
    (portColor C c).card + (secondShore C c).card = (Shore C).card := by
  classical
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

/-- When both shores are marked by five ports, the two local shell budgets
give a stronger order bound depending on both shared counts. -/
theorem both_five_shore_order_weighted
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5) :
    (Shore C).card+(Shore D).card≤14 ∧
    2*((Shore C).card+(Shore D).card) ≤
      18+(sharedPortSet C).card+(sharedPortSet D).card := by
  classical
  have ux := common_universal_in_shore_at_five hc even cd xc ax bx D5
  have uy := common_universal_in_shore_at_five hc even cd.symm yd ay by' C5
  have xa := common_part_at_universal hc ux a ax (shore_off C).1
  have xb := common_part_at_universal hc ux b bx (shore_off C).2
  have ya := common_part_at_universal hc uy a ay (shore_off D).1
  have yb := common_part_at_universal hc uy b by' (shore_off D).2
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have pa := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have pb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  have tally (T : Cmp (G:=G) (a:=a) (b:=b)) :
      (portColor T a).card+(portColor T b).card=(cutPorts T).card+(sharedPortSet T).card := by
    have h := card_union_add_card_inter (portColor T a) (portColor T b)
    have u : portColor T a∪portColor T b=cutPorts T := by
      ext z
      simp [portColor,cutPorts,and_or_left]
    have i : portColor T a∩portColor T b=sharedPortSet T := by
      ext z
      simp [portColor,sharedPortSet,and_assoc,and_left_comm]
    rw [u,i] at h
    exact h.symm
  have qC := tally C
  have qD := tally D
  have aTop (T : Cmp (G:=G) (a:=a) (b:=b)) : (portColor T a).card≤(cutPorts T).card :=
    card_le_card (fun w wm=>mem_filter.mpr ⟨(mem_filter.mp wm).1,.inl (mem_filter.mp wm).2⟩)
  have ac := aTop C
  have ad := aTop D
  constructor <;> omega

#print axioms both_five_shore_order_weighted
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
