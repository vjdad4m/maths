import DegreeFiveTwoThreeClose189



namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A distance-two cut covering all off-cut vertices by two shores
must have at least five total contacts under the pair-degree premise. -/
theorem five_le_total_ports_at_distance_two
    (two : G.dist a b=2)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D) :
    5≤(cutPorts C).card+(cutPorts D).card := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have bound (c : V) (cut : c=a ∨ c=b) : G.degree c≤(cutPorts C).card+(cutPorts D).card := by
    have sub (K : Cmp (G:=G) (a:=a) (b:=b)) : portColor K c⊆cutPorts K := by
      intro z zc
      obtain ⟨zk,cz⟩ := mem_filter.mp zc
      exact mem_filter.mpr ⟨zk,cut.elim (fun e=>.inl (e ▸ cz)) (fun e=>.inr (e ▸ cz))⟩
    rw [count_cut_degree_on_two_shores cd cover two cut]
    exact Nat.add_le_add (card_le_card (sub C)) (card_le_card (sub D))
  exact (degree a b ab).elim (fun h=>h.trans (bound a (.inl rfl)))
    (fun h=>h.trans (bound b (.inr rfl)))

#print axioms five_le_total_ports_at_distance_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
