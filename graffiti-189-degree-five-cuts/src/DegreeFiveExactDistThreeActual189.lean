import DegreeFiveActualCut189
import DegreeFiveExactDistThree189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b ab_ne order_ge_three_from_dist from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Degree-five #189 whenever an actual two-vertex separator is at distance
three and both deleted vertices have degree exactly five. -/
theorem traceable_at_actual_exact_five_distance_three_cut {a b : V} (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected)
    (a5 : G.degree a=5) (b5 : G.degree b=5) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
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
  have cap := cut_distance_le_three_at_actual_five_cut hc even conn degree cut
  have exactDist : G.dist a b=3 := by omega
  exact Split.Five.traceable_of_exact_five_distance_three_cut S hc exactDist even degree conn
    (shore_connected (C true)) (shore_hit_a ab conn (C true)) (shore_hit_b ab conn (C true)) a5 b5

#print axioms traceable_at_actual_exact_five_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
