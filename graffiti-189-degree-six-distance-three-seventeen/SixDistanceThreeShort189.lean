import SixCutComponents189
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
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem no_common_far (far : 3≤G.dist a b) {z : V} :
    ¬(G.Adj a z ∧ G.Adj b z) := by
  intro ⟨az,bz⟩
  have q := G.dist_le (Walk.cons az (Walk.cons bz.symm .nil))
  simp at q
  omega

private theorem shore_inside_five (far : 3≤G.dist a b)
    (C : Cmp G a b) {z : V} (zc : z∈Shore C) (hi : 6≤G.degree z) :
    5≤(inside G (Shore C) z).card := by
  classical
  have cost {t : V} (h : ∀ w,G.Adj z w → w∈Shore C ∨ w=t) :
      G.degree z≤(inside G (Shore C) z).card+1 := by
    simpa using inside_lower_of_boundary (G:=G) (Shore C) {t} (u:=z)
      (fun w zw=>(h w zw).imp id mem_singleton.mpr)
  by_cases az : G.Adj a z
  · have q := cost (t:=a) (fun w zw=>by
      rcases shore_closed C z zc w zw with rfl|rfl|h
      · exact .inr rfl
      · exact (no_common_far far ⟨az,zw.symm⟩).elim
      exact .inl h)
    omega
  have q := cost (t:=b) (fun w zw=>by
    rcases shore_closed C z zc w zw with rfl|rfl|h
    · exact (az zw.symm).elim
    · exact .inr rfl
    exact .inl h)
  omega

private theorem six_min_shore (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (C : Cmp G a b)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) :
    6≤(Shore C).card := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yc,by'⟩ := shore_hit_b ab conn C
  have xy : x≠y := fun eq=>no_common_far far ⟨ax,eq.symm ▸ by'⟩
  have l := degree_le_shore C xc (.inr (fun bx=>no_common_far far ⟨ax,bx⟩))
  have r := degree_le_shore C yc (.inl (fun ay=>no_common_far far ⟨ay,by'⟩))
  rcases degree x y xy with h|h <;> omega

private theorem route_at_ordered_shores (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c10 : (Shore C).card≤10) (d9 : (Shore D).card≤9)
    (dhigh : ∀ z∈Shore D,6≤G.degree z) :
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
  obtain ⟨ya,yaD,aya⟩ := shore_hit_a ab conn D
  obtain ⟨yb,ybD,byb⟩ := shore_hit_b ab conn D
  have yab : ya≠yb := fun eq=>no_common_far far ⟨aya,eq.symm ▸ byb⟩
  have M : RouteOn G (Shore D) ya yb :=
    terminal_route_on_of_local_ore (Shore D) yaD ybD yab
      (fun u um v vm _ _=>by
        have h := shore_inside_five far D um (dhigh u um)
        have j := shore_inside_five far D vm (dhigh v vm)
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

/-- At a nonadjacent separating pair of distance at least three, two shores of
order at most nine always provide a spanning path. No even bound is required
once the two-shore premise is known. -/
theorem traceable_at_two_small_shores_distance_three (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c9 : (Shore C).card≤9) (d9 : (Shore D).card≤9) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases all : ∀ z∈Shore D,6≤G.degree z
  · exact route_at_ordered_shores far ab conn degree cd cover (by omega) d9 all
  push_neg at all
  obtain ⟨w,wd,wl⟩ := all
  have chigh (z : V) (zc : z∈Shore C) : 6≤G.degree z := by
    have ne : z≠w := fun eq=>disjoint_left.mp (shore_disjoint cd) zc (eq.symm ▸ wd)
    exact (degree z w ne).resolve_right (by omega)
  exact route_at_ordered_shores far ab conn degree cd.symm (fun za zb=>(cover za zb).symm)
    (by omega) c9 chigh

/-- The degree-six distance-three two-cut branch is traceable through order 17. -/
theorem traceable_at_six_distance_three_order_seventeen
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤17) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have cs := six_min_shore far ab conn C degree
  have ds := six_min_shore far ab conn D degree
  have b := shore_sum_with_cover ab cd cover
  exact traceable_at_two_small_shores_distance_three far ab conn degree cd cover (by omega) (by omega)

#print axioms traceable_at_two_small_shores_distance_three
#print axioms traceable_at_six_distance_three_order_seventeen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
