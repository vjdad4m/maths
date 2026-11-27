import DegreeFiveActualCut189
import DegreeFiveRouteBasic189
import DegreeFiveFourPort189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveDistanceTwoSingletonClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveFourForeign189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveTwoTwoThreeShared189
import DegreeFiveBalancedCommonRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two charge_at_high_port from DegreeFiveDistanceTwoThreeClose189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private boundary_permuted from DegreeFiveExclusiveGateway189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private sharedPortSet common_shore_count_by_charges_general from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem two_two_common_shore_geometry
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2) :
    3≤(sharedPortSet C).card ∧
    3≤(portColor C a).card ∧ (portColor C a).card≤4 ∧
    3≤(portColor C b).card ∧ (portColor C b).card≤4 ∧
    (Shore C).card≤(sharedPortSet C).card+3 ∧
    (secondShore C a).card≤1 ∧ (secondShore C b).card≤1 := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have two' : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uC v e with rfl|rfl|vh
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp (shore_disjoint cd) vh vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  have da := shore_hit_a ab conn D
  have db := shore_hit_b ab conn D
  let T := Split.Five.switch S (shore_connected D) da db
  let P := portColor D a
  let Q := portColor D b
  let K := sharedPortSet C
  have union : P∪Q=cutPorts D := by
    ext z
    change z∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      z∈(Shore D).filter (fun z=>G.Adj a z ∨ G.Adj b z)
    simp [and_or_left]
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z zp zq
    exact none _ (mem_filter.mp zp).1 ⟨(mem_filter.mp zp).2,(mem_filter.mp zq).2⟩
  have tally := congrArg Finset.card union
  rw [card_union_of_disjoint dis] at tally
  have pAc : P.card=2 := pA
  have pBc : Q.card=2 := pB
  have four : 4≤S.foreignPorts.card := by
    change 4≤(cutPorts D).card
    omega
  have nz : K.Nonempty := card_pos.mp (show 0<K.card by exact lt_of_lt_of_le (by decide) shared)
  obtain ⟨x,xK⟩ := nz
  obtain ⟨xC,ax,bx⟩ := mem_filter.mp xK
  obtain ⟨u,uP,u5⟩ := anywhere_high_of_two degree (show 2≤P.card by omega)
  obtain ⟨v,vP,v5⟩ := anywhere_high_of_two degree (show 2≤Q.card by omega)
  obtain ⟨uD,au⟩ := mem_filter.mp uP
  obtain ⟨vD,bv⟩ := mem_filter.mp vP
  have bu : ¬G.Adj b u := fun e=>none u uD ⟨au,e⟩
  have av : ¬G.Adj a v := fun e=>none v vD ⟨e,bv⟩
  have cf := opposite_ports_at_exclusive_le_four T hc even uD au bu
  have df := opposite_ports_at_exclusive_le_four T.flip hc even vD bv av
  have chargeA := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc uD au u5
  rw [if_neg bu] at chargeA
  have chargeB := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vD bv v5
  rw [if_neg av] at chargeB
  change 5≤P.card+(secondShore D a).card at chargeA
  change 5≤Q.card+(secondShore D b).card at chargeB
  have shellA := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have shellB := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ two' even
  have near := Split.Five.near_universal_at_four_foreign S hc even conn xC ax bx four
  have leftbound := common_shore_count_by_charges_general hc xC ax bx near.2
  let X := secondShore C x
  have px : X.card+(cutPorts D).card≤5 := by
    have far : cutPorts D⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zD,az|bz⟩ := mem_filter.mp zp
      all_goals
        have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xC (e.symm ▸ zD)
        have no := cross x xC z zD
      · exact d2 hc ne no ax.symm az
      exact d2 hc ne no bx.symm bz
    have dd : Disjoint X (cutPorts D) :=
      (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
    have h := card_le_card (union_subset (show X⊆DistanceTwo G x from inter_subset_right) far)
    rw [card_union_of_disjoint dd] at h
    exact h.trans (distanceTwo_le_of_even 5 x (even x))
  change (Shore C).card≤K.card+(secondShore C a).card+(secondShore C b).card+X.card at leftbound
  have e1 : (secondShore C a).card≤1 := by omega
  have f1 : (secondShore C b).card≤1 := by omega
  have s3 : (Shore C).card≤(sharedPortSet C).card+3 := by
    change (Shore C).card≤K.card+3
    omega
  have sh := three_shared_of_small_common_shore_with_one_place_each hc degree shared s3 e1 f1
  have ka : sharedPortSet C⊆portColor C a := fun z zh=>by
    obtain ⟨zc,az,_⟩ := mem_filter.mp zh
    exact mem_filter.mpr ⟨zc,az⟩
  have kb : sharedPortSet C⊆portColor C b := fun z zh=>by
    obtain ⟨zc,_,bz⟩ := mem_filter.mp zh
    exact mem_filter.mpr ⟨zc,bz⟩
  exact ⟨sh,sh.trans (card_le_card ka),cf,sh.trans (card_le_card kb),df,s3,e1,f1⟩

#print axioms two_two_common_shore_geometry
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
