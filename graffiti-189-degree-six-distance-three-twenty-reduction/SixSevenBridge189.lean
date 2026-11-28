import SixSevenRoleBounds189
import SixSevenArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open scoped BigOperators
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two port_have_wasted_even from TwoCutDistanceCaps189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open FiveAdjacent (shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem role_ports_seen (far : 3≤G.dist a b) (S : Finset V) :
    cutPorts G S a=(sixBucket G a b S 0∪sixBucket G a b S 1) ∧
    cutPorts G S b=(sixBucket G a b S 2∪sixBucket G a b S 3) ∧
    cutSeen G S a=(sixBucket G a b S 3∪(sixBucket G a b S 4∪sixBucket G a b S 6)) ∧
    cutSeen G S b=(sixBucket G a b S 1∪(sixBucket G a b S 5∪sixBucket G a b S 6)) := by
  have no (z : V) : ¬(G.Adj a z∧G.Adj b z) := no_common_far far
  refine ⟨?_,?_,?_,?_⟩ <;> ext z
  all_goals
    have ha : G.Adj a z → G.dist a z≠2 := fun h e=>by have t := dist_eq_one_iff_adj.mpr h; omega
    have hb : G.Adj b z → G.dist b z≠2 := fun h e=>by have t := dist_eq_one_iff_adj.mpr h; omega
    simp [cutPorts,mem_cutSeen,mem_sixBucket (no z),sixClassSpec]
    tauto

theorem role_family_card (S : Finset V) (I : Finset (Fin 8)) :
    (I.biUnion (sixBucket G a b S)).card = ∑ i ∈ I,(sixBucket G a b S i).card :=
  card_biUnion (fun _ _ _ _ ij=>sixBuckets_disjoint a b S S ij)

theorem cut_port_range (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7) (cd : C≠D) :
    1≤(cutPorts G (Shore D) a).card ∧ (cutPorts G (Shore D) a).card≤5 := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yd,ay⟩ := shore_hit_a ab conn D
  obtain ⟨z,zd,ze⟩ := port_have_wasted_even hc far C xc ax (shore_hit_b ab conn C) cd
  let P := cutPorts G (Shore D) a
  have h : P⊆PositiveEven G x := by
    intro v vv
    have t := each_foreign_port_is_distance_two hc cd (mem_filter.mpr ⟨xc,ax⟩)
      (show v∈cutPorts G (Shore D) a from vv)
    exact in_positive_even_of_dist_two (mem_filter.mp t).2
  have t := (card_le_card (insert_subset ze h)).trans (positive_even_cap (d:=6) (even x))
  have zp : z∉P := fun e=>zd (mem_filter.mp e).1
  rw [card_insert_of_not_mem zp] at t
  have p := card_pos.mpr (show P.Nonempty from ⟨y,mem_filter.mpr ⟨yd,ay⟩⟩)
  change 1≤P.card∧P.card≤5
  omega

theorem cut_ports_sum (far : 3≤G.dist a b) (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) :
    G.degree a=(cutPorts G (Shore C) a).card+(cutPorts G (Shore D) a).card := by
  let P := cutPorts G (Shore C) a
  let Q := cutPorts G (Shore D) a
  have noab : ¬G.Adj a b := fun h=>by have z := dist_eq_one_iff_adj.mpr h; omega
  have eq : G.neighborFinset a=P∪Q := by
    ext x
    rw [G.mem_neighborFinset,mem_union]
    constructor
    · intro ax
      have xa : x≠a := ax.ne.symm
      have xb : x≠b := fun e=>noab (e ▸ ax)
      exact (cover xa xb).imp (fun xc=>mem_filter.mpr ⟨xc,ax⟩) (fun xd=>mem_filter.mpr ⟨xd,ax⟩)
    · exact fun e=>e.elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2)
  have dPQ : Disjoint P Q := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
  rw [←G.card_neighborFinset_eq_degree,eq,card_union_of_disjoint dPQ]

theorem little_disallowed_local_even (hc : G.Connected) (far : 3≤G.dist a b)
    (eleven : (Shore D).card=11) {i j : Fin 8} {u x : V}
    (ud : u∈Shore D) (xd : x∈Shore D) (uh : 6≤G.degree u) (xh : 6≤G.degree x)
    (us : sixClassSpec G a b u i) (xs : sixClassSpec G a b x j)
    (bad : j∉allowedRoles i) : x∈DistanceTwo G u := by
  have un : ¬(G.Adj a u∧G.Adj b u) := no_common_far far
  have xn : ¬(G.Adj a x∧G.Adj b x) := no_common_far far
  have ij : i≠j := by
    intro eq
    subst j
    exact bad (by fin_cases i <;> decide)
  have ne : u≠x := by
    intro eq
    subst x
    exact ij (((class_spec un i).mpr us).symm.trans ((class_spec un j).mpr xs))
  have ua : u≠a := fun e=>(shore_off D).1 (e ▸ ud)
  have ub : u≠b := fun e=>(shore_off D).2 (e ▸ ud)
  have xa : x≠a := fun e=>(shore_off D).1 (e ▸ xd)
  have xb : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  exact eleven_nonedge_charges hc far eleven ud xd ne
    (fun h=>bad (six_role_of_edge hc far ua ub xa xb h us xs)) uh xh

#print axioms little_disallowed_local_even
#print axioms cut_port_range
#print axioms role_ports_seen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
