import DegreeFiveEitherColorVisible189
import DegreeFiveBothNonsaturated189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
open private common_side_color_cover from DegreeFiveBothAtLeastFour189
open private graph_order_le_shores_add_two from DegreeFiveBothNonsaturated189
open private visible_from_either_named_cut from DegreeFiveEitherColorVisible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The top-order nonsaturated 4+5 profile has all four-port-side
contacts shared, and at most one exclusive porter of each color in the
five-port shore. -/
theorem order_fifteen_four_five_contact_constraints
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D5 : (cutPorts D).card=5)
    (large : 15≤Fintype.card V)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    sharedPortSet C=cutPorts C ∧ 4≤(portColor D a).card ∧
      4≤(portColor D b).card := by
  classical
  have n := graph_order_le_shores_add_two cover
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vC
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vC vd
  let S : Split G a b := ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,
    shore_connected C,(fun _ uc _ vd=>cross uc vd),shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  let T : Split G a b := ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,
    shore_connected D,(fun _ vd _ uc e=>cross uc vd e.symm),shore_hit_a ab conn D,shore_hit_b ab conn D,
    (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have xNear := (Split.Five.near_universal_at_four_foreign S hc even conn xc ax bx (show 4≤(cutPorts D).card by omega)).2
  have yNear := (Split.Five.near_universal_at_four_foreign T hc even conn yd ay by' (show 4≤(cutPorts C).card by omega)).2
  have xCover (z : V) (zc : z∈Shore C) : G.dist x z≤2 := xNear z zc
  have yCover (z : V) (zd : z∈Shore D) : G.dist y z≤2 := yNear z zd
  have q (c : V) (ac : G.Adj a c) (bc : G.Adj b c)
      {U W : Cmp (G:=G) (a:=a) (b:=b)} (uw : U≠W)
      (uc : c∈Shore U) (cross' : ∀ w∈Shore W,¬G.Adj c w) :
      (secondShore U c).card+(cutPorts W).card≤5 := by
    have far : cutPorts W⊆DistanceTwo G c := by
      intro z zz
      obtain ⟨zw,hit⟩ := mem_filter.mp zz
      have ne : c≠z := fun e=>disjoint_left.mp (shore_disjoint uw) uc (e.symm ▸ zw)
      exact hit.elim (fun h=>d2 hc ne (cross' z zw) ac.symm h)
        (fun h=>d2 hc ne (cross' z zw) bc.symm h)
    have d : Disjoint (secondShore U c) (cutPorts W) :=
      (shore_disjoint uw).mono inter_subset_left (filter_subset _ _)
    have h := (card_le_card (union_subset
      (show secondShore U c⊆DistanceTwo G c from inter_subset_right) far)).trans
      (distanceTwo_le_of_even 5 c (even c))
    rwa [card_union_of_disjoint d] at h
  have xx := q x ax bx cd xc (fun _ z=>cross xc z)
  have yy := q y ay by' cd.symm yd (fun _ z e=>cross z yd e.symm)
  have xa := common_side_color_cover hc xCover ax (shore_off C).1
  have xb := common_side_color_cover hc xCover bx (shore_off C).2
  have ya := common_side_color_cover hc yCover ay (shore_off D).1
  have yb := common_side_color_cover hc yCover by' (shore_off D).2
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have aa := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have bb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  have tally (U : Cmp (G:=G) (a:=a) (b:=b)) :
      (portColor U a).card+(portColor U b).card=(cutPorts U).card+(sharedPortSet U).card := by
    have h := card_union_add_card_inter (portColor U a) (portColor U b)
    have u : portColor U a∪portColor U b=cutPorts U := by
      ext z
      simp [portColor,cutPorts,and_or_left]
    have i : portColor U a∩portColor U b=sharedPortSet U := by
      ext z
      simp [portColor,sharedPortSet,and_assoc,and_left_comm]
    rw [u,i] at h
    exact h.symm
  have hC := tally C
  have hD := tally D
  have colorSub (E : Cmp (G:=G) (a:=a) (b:=b)) (c : V) (cc : c=a ∨ c=b) :
      portColor E c⊆cutPorts E := by
    intro z zp
    obtain ⟨ze,cz⟩ := mem_filter.mp zp
    exact cut_mem_iff.mpr ⟨ze,cc.elim (fun e=>.inl (e ▸ cz)) (fun e=>.inr (e ▸ cz))⟩
  have ca := card_le_card (colorSub C a (.inl rfl))
  have cb := card_le_card (colorSub C b (.inr rfl))
  have da := card_le_card (colorSub D a (.inl rfl))
  have db := card_le_card (colorSub D b (.inr rfl))
  have dA : 4≤(portColor D a).card := by omega
  have dB : 4≤(portColor D b).card := by omega
  have dShare : 2≤(sharedPortSet D).card := by omega
  have near (w : V) (wk : w∈sharedPortSet D) :
      (secondShore D w).card≤1 ∧ ∀ t∈Shore D,G.dist w t≤2 := by
    obtain ⟨wd,aw,bw⟩ := mem_filter.mp wk
    exact Split.Five.near_universal_at_four_foreign T hc even conn wd aw bw (le_of_eq C4.symm)
  have cv (c : V) (cc : c=a ∨ c=b)
      (hC : (Shore C).card≤(portColor C c).card+(secondShore C c).card+(secondShore C x).card)
      (hD : (Shore D).card≤(portColor D c).card+(secondShore D c).card+(secondShore D y).card)
      (cap : (secondShore C c).card+(secondShore D c).card≤4) :
      (portColor C c).card=4 := by
    apply Classical.byContradiction
    intro neq
    have hi := card_le_card (colorSub C c cc)
    have hj := card_le_card (colorSub D c cc)
    have hD5 : (portColor D c).card=5 := by omega
    have eq : portColor D c=cutPorts D := eq_of_subset_of_card_le (colorSub D c cc) (by omega)
    have all (w : V) (wp : w∈cutPorts D) : G.Adj c w := by
      have q : w∈portColor D c := eq.symm ▸ wp
      exact (mem_filter.mp q).2
    have vis := visible_from_either_named_cut hc two even cd (le_of_eq C4.symm) dShare cc all near
    have dHi := (card_le_card vis).trans (card_union_le _ _)
    omega
  have aC := cv a (.inl rfl) xa ya aa
  have bC := cv b (.inr rfl) xb yb bb
  have eq := eq_of_subset_of_card_le (common_sub_ports C) (by omega)
  exact ⟨eq,dA,dB⟩

#print axioms order_fifteen_four_five_contact_constraints
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
