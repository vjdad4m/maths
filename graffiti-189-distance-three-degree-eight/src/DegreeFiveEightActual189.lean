import DegreeFiveEightSplit189
import DegreeFiveBridgeSize189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b ab_ne order_ge_three_from_dist from DegreeFiveActualCut189
open private count_cut_a from DegreeFiveBridgeSize189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false


theorem traceable_at_actual_five_distance_three_cut_degree_eight {a b : V} (hc : G.Connected)
    (three : G.dist a b=3) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected)
    (a8 : G.degree a=8) :
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
  have right := Split.Five.foreign_a_ports_le_four S hc far even
  have left := Split.Five.foreign_a_ports_le_four (Split.Five.switch S rc ra rb) hc far even
  change S.localA.card≤4 at left
  have sum := count_cut_a S far
  have l4 : S.localA.card=4 := by omega
  have r4 : S.foreignA.card=4 := by omega
  exact Split.Five.traceable_four_a_ports_each_shore_distance_three S hc three even degree l4 r4 rc ra rb

#print axioms traceable_at_actual_five_distance_three_cut_degree_eight
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
