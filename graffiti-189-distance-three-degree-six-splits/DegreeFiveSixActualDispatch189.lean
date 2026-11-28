import DegreeFiveSevenActual189
import DegreeFiveEightActual189
import DegreeFiveSixTwoFourFinal189
import DistThreeSingletonHigh189
import DistanceThreeBothHigh189
import DegreeFiveBridgeSize189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b ab_ne order_ge_three_from_dist from DegreeFiveActualCut189
open private count_cut_a from DegreeFiveBridgeSize189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false


theorem traceable_actual_six_of_both_three {a b : V} (hc : G.Connected)
    (three : G.dist a b=3) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected)
    (a6 : G.degree a=6)
    (threeThree : ∀ S : Split G a b, 5 ≤ G.degree b → S.localA.card=3 → S.foreignA.card=3 →
      (S.L.filter (G.Adj b)).card≤3 → (S.R.filter (G.Adj b)).card≤3 →
      (G.induce (↑S.R : Set V)).Connected →
      (∃ x∈S.R,G.Adj a x) → (∃ x∈S.R,G.Adj b x) →
      ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support) :
    ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have far : 3≤G.dist a b := by omega
  have ab := ab_ne far
  let J := G.induce {x : V | x≠a ∧ x≠b}
  have hi := component_card_le_two_at_cut_distance_ge_three hc far even conn degree
  have lo := component_card_gt_one_of_disconnected a b (order_ge_three_from_dist hc far) cut
  change 1<Nat.card J.ConnectedComponent at lo
  change Nat.card J.ConnectedComponent≤2 at hi
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card Bool=Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_bool,←Nat.card_eq_fintype_card]
    omega
  let C := Fintype.equivOfCardEq n
  let L := Shore (C false)
  let R := Shore (C true)
  have dis : Disjoint L R := shore_disjoint (fun h=>Bool.false_ne_true (C.injective h))
  have cover (x : V) : x=a ∨ x=b ∨ x∈L ∨ x∈R := by
    by_cases xa : x=a
    · exact .inl xa
    by_cases xb : x=b
    · exact .inr (.inl xb)
    obtain ⟨i,e⟩ := C.surjective (J.connectedComponentMk ⟨x,xa,xb⟩)
    cases i
    · exact .inr (.inr (.inl (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
    · exact .inr (.inr (.inr (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
  have cross (x : V) (xl : x∈L) (y : V) (yr : y∈R) : ¬G.Adj x y := by
    intro xy
    have yr' : y∈Shore (C true) := yr
    rcases shore_closed (C false) x xl y xy with e|e|e
    · exact (shore_off (C true)).1 (e ▸ yr')
    · exact (shore_off (C true)).2 (e ▸ yr')
    exact disjoint_left.mp dis e yr
  let S : Split G a b :=
    ⟨L,R,dis,shore_off (C false),shore_off (C true),shore_connected (C false),cross,
      shore_hit_a ab conn (C false),shore_hit_b ab conn (C false),cover⟩
  have rc := shore_connected (C true)
  have ra := shore_hit_a ab conn (C true)
  have rb := shore_hit_b ab conn (C true)
  let T := Split.Five.switch S rc ra rb
  have right := Split.Five.foreign_a_ports_le_four S hc far even
  have left := Split.Five.foreign_a_ports_le_four T hc far even
  change S.localA.card≤4 at left
  let LB := S.L.filter (G.Adj b)
  let RB := S.R.filter (G.Adj b)
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have three' : G.dist b a=3 := by rwa [dist_comm]
  have cb := Split.Five.foreign_a_ports_le_four S.flip hc far' even
  have db := Split.Five.foreign_a_ports_le_four T.flip hc far' even
  change RB.card≤4 at cb
  change LB.card≤4 at db
  have bSum := count_cut_a S.flip far'
  change G.degree b=LB.card+RB.card at bSum
  have cut' : ¬(G.induce {z : V | z≠b ∧ z≠a}).Connected := by
    have eq : ({z : V | z ≠ b ∧ z ≠ a} : Set V) = {z : V | z ≠ a ∧ z ≠ b} := by
      ext z
      exact and_comm
    rwa [eq]
  by_cases seven : G.degree b=7
  · exact traceable_at_actual_five_distance_three_cut_degree_seven hc three' even conn degree cut' seven
  by_cases eight : G.degree b=8
  · exact traceable_at_actual_five_distance_three_cut_degree_eight hc three' even conn degree cut' eight
  have bCap : G.degree b≤6 := by omega
  have tally := count_cut_a S far
  by_cases l2 : S.localA.card=2
  · have r4 : S.foreignA.card=4 := by omega
    exact Split.Five.traceable_six_two_four S hc far even conn degree l2 r4 rc ra rb
  by_cases r2 : S.foreignA.card=2
  · have l4 : S.localA.card=4 := by omega
    exact Split.Five.traceable_six_two_four T hc far even conn degree r2 l4 S.leftConnected S.leftA S.leftB
  have l3 : S.localA.card=3 := by omega
  have r3 : S.foreignA.card=3 := by omega
  have distinct : C false≠C true := fun e=>Bool.false_ne_true (C.injective e)
  by_cases l4 : LB.card=4
  · by_cases r2 : RB.card=2
    · exact Split.Five.traceable_six_two_four T.flip hc far' even conn degree r2 l4 S.leftConnected S.leftB S.leftA
    obtain ⟨y,yr,by'⟩ := rb
    have yrB : y∈RB := mem_filter.mpr ⟨yr,by'⟩
    have pos := card_pos.mpr ⟨y,yrB⟩
    have r1 : RB.card=1 := by omega
    have eq : RB={y} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr yrB)
      (by rw [r1,card_singleton])).symm
    have only (z : V) (zr : z∈R) (bz : G.Adj b z) : z=y :=
      mem_singleton.mp (eq ▸ (show z∈RB from mem_filter.mpr ⟨zr,bz⟩))
    have high := singleton_port_high_opposite_four hc far even conn degree distinct.symm yr by' only l4
    exact Split.Five.traceable_singleton_four_at_three_three T hc far even conn degree r3 l3 l4
      S.leftConnected S.leftA S.leftB yr by' high only
  by_cases r4 : RB.card=4
  · by_cases l2 : LB.card=2
    · exact Split.Five.traceable_six_two_four S.flip hc far' even conn degree l2 r4 rc rb ra
    obtain ⟨y,yl,by'⟩ := S.leftB
    have yL : y∈LB := mem_filter.mpr ⟨yl,by'⟩
    have pos := card_pos.mpr ⟨y,yL⟩
    have l1 : LB.card=1 := by omega
    have eq : LB={y} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr yL)
      (by rw [l1,card_singleton])).symm
    have only (z : V) (zl : z∈L) (bz : G.Adj b z) : z=y :=
      mem_singleton.mp (eq ▸ (show z∈LB from mem_filter.mpr ⟨zl,bz⟩))
    have high := singleton_port_high_opposite_four hc far even conn degree distinct yl by' only r4
    exact Split.Five.traceable_singleton_four_at_three_three S hc far even conn degree l3 r3 r4
      rc ra rb yl by' high only
  have bHigh := (both_cut_degrees_at_least_five_of_far_cut hc far even conn degree distinct cover).2
  exact threeThree S bHigh l3 r3 (by change LB.card ≤ 3; omega) (by change RB.card ≤ 3; omega) rc ra rb

#print axioms traceable_actual_six_of_both_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
