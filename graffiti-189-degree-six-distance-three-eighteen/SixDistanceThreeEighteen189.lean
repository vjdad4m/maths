import SixTenOre189
import SixTenRegular189
import AdjacentCutFiveFourteenDarkLift189
import AdjacentCutFiveMixedRouteSmall189
import AdjacentCutFiveMixedFourteenSixteen189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_connected shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private degree_le_shore from AdjacentCutFiveComponents189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private rooted_side inside_lower_of_boundary from AdjacentCutFiveMixedRouteSmall189
open private no_common_far shore_inside_five six_min_shore route_at_ordered_shores from SixDistanceThreeShort189
open private ten_shore_has_above_five neighbor_subset_of_dark from SixTenRegular189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem join_shore_to_middle (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c10 : (Shore C).card≤10) {ya yb : V}
    (aya : G.Adj a ya) (byb : G.Adj b yb) (M : RouteOn G (Shore D) ya yb) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨xa,xaC,axa⟩ := shore_hit_a ab conn C
  obtain ⟨xb,xbC,bxb⟩ := shore_hit_b ab conn C
  have xab : xa≠xb := fun eq=>no_common_far far ⟨axa,eq.symm ▸ bxb⟩
  obtain ⟨s,t,port,R⟩ := rooted_side (Shore C) (fun z=>G.Adj a z ∨ G.Adj b z)
    (fun z=>6≤G.degree z) (shore_connected C)
    ⟨xa,xaC,xb,xbC,xab,.inl axa,.inr bxb⟩
    (fun u _ v _ uv=>degree u v uv) (by
      intro u uc v vc _ _ hu hv
      have h := shore_inside_five far C uc hu
      have j := shore_inside_five far C vc hv
      omega)
  have finish {g h i j : V} (gh : g≠h)
      (gC : g∉Shore C) (hC : h∉Shore C) (gD : g∉Shore D) (hD : h∉Shore D)
      (ends : ∀ {z : V},z≠g → z≠h → z∈Shore C ∨ z∈Shore D)
      (route : RouteOn G (Shore D) i j) (gs : G.Adj g s) (gi : G.Adj g i) (hj : G.Adj h j) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    have dis : Disjoint (insert g (Shore C)) (insert h (Shore D)) := by
      apply disjoint_left.mpr
      intro z zc zd
      rcases mem_insert.mp zc with rfl|zc
      · exact (mem_insert.mp zd).elim gh gD
      rcases mem_insert.mp zd with rfl|zd
      · exact hC zc
      exact disjoint_left.mp (shore_disjoint cd) zc zd
    obtain ⟨q,qq,qs⟩ := (R.reverse.suffix gs.symm gC).join (route.suffix hj.symm hD) dis gi
    refine ⟨t,h,q,qq,fun z=>(qs z).mpr ?_⟩
    by_cases e : z=g
    · simp [e]
    by_cases f : z=h
    · simp [f]
    rcases ends e f with k|k <;> simp [k]
  rcases port with pa|pb
  · exact finish ab (shore_off C).1 (shore_off C).2 (shore_off D).1 (shore_off D).2 cover M pa aya byb
  exact finish ab.symm (shore_off C).2 (shore_off C).1 (shore_off D).2 (shore_off D).1
    (fun zb za=>cover za zb) M.reverse pb byb aya

private theorem route_middle_ten (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (ten : (Shore D).card=10)
    (high : ∀ z∈Shore D,6≤G.degree z) :
    ∃ s t, G.Adj a s ∧ G.Adj b t ∧ RouteOn G (Shore D) s t := by
  classical
  let U := ↑(↑(Shore D) : Set V)
  let J := G.induce (↑(Shore D) : Set V)
  let A : Finset U := univ.filter (fun x=>G.Adj a x.val)
  let B : Finset U := univ.filter (fun x=>G.Adj b x.val)
  have n : Fintype.card U=10 := (Fintype.card_coe (Shore D)).trans ten
  have ds : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    exact no_common_far far ⟨(mem_filter.mp za).2,(mem_filter.mp zb).2⟩
  have Apos : A.Nonempty := by
    obtain ⟨z,zd,az⟩ := shore_hit_a ab conn D
    exact ⟨⟨z,zd⟩,mem_filter.mpr ⟨mem_univ _,az⟩⟩
  have Bpos : B.Nonempty := by
    obtain ⟨z,zd,bz⟩ := shore_hit_b ab conn D
    exact ⟨⟨z,zd⟩,mem_filter.mpr ⟨mem_univ _,bz⟩⟩
  have eq (z : U) : (inside G (Shore D) z.val).card=J.degree z :=
    inside_card_eq_degree_induce (G:=G) (Shore D) z
  have min (z : U) : 5≤J.degree z := by
    rw [←eq]
    exact shore_inside_five far D z.property (high z z.property)
  have dark (z : U) (za : z∉A) (zb : z∉B) : 6≤J.degree z := by
    have za' : ¬G.Adj a z.val := fun e=>za (mem_filter.mpr ⟨mem_univ _,e⟩)
    have zb' : ¬G.Adj b z.val := fun e=>zb (mem_filter.mpr ⟨mem_univ _,e⟩)
    have h := card_le_card (neighbor_subset_of_dark D z.property za' zb')
    rw [card_neighborFinset_eq_degree,eq] at h
    exact (high z z.property).trans h
  obtain ⟨r,rd,rr⟩ := ten_shore_has_above_five hc far ab conn even degree cd ten high
  have r6 : 6≤J.degree (⟨r,rd⟩ : U) := by
    rw [←eq]
    exact rr
  obtain ⟨x,xa,y,yb,p,pp,ps⟩ := cross_marked_ten_ore (G:=J) n A B ds Apos Bpos min r6 dark
  exact ⟨x.val,y.val,(mem_filter.mp xa).2,(mem_filter.mp yb).2,lift_side_path (Shore D) p pp ps⟩

/-- At degree six a distance-three actual two-cut is traceable through order 18. -/
theorem traceable_at_six_distance_three_order_eighteen
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤18) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have cs := six_min_shore far ab conn C degree
  have ds := six_min_shore far ab conn D degree
  have t := shore_sum_with_cover ab cd cover
  have branch (C D : Cmp G a b) (cd : C≠D)
      (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
      (d10 : (Shore D).card=10) (c6 : (Shore C).card=6) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    by_cases h : ∀ z∈Shore D,6≤G.degree z
    · obtain ⟨s,t,as',bt,p⟩ := route_middle_ten hc far ab conn even degree cd d10 h
      exact join_shore_to_middle far ab conn degree cd cover (by omega) as' bt p
    push_neg at h
    obtain ⟨w,wd,wl⟩ := h
    have ch (z : V) (zc : z∈Shore C) : 6≤G.degree z := by
      have ne : z≠w := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd)
      exact (degree z w ne).resolve_right (by omega)
    exact route_at_ordered_shores far ab conn degree cd.symm (fun za zb=>(cover za zb).symm)
      (by omega) (by omega) ch
  by_cases c9 : (Shore C).card≤9
  · by_cases d9 : (Shore D).card≤9
    · exact traceable_at_two_small_shores_distance_three far ab conn degree cd cover c9 d9
    exact branch C D cd cover (by omega) (by omega)
  exact branch D C cd.symm (fun za zb=>(cover za zb).symm) (by omega) (by omega)

#print axioms traceable_at_six_distance_three_order_eighteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
