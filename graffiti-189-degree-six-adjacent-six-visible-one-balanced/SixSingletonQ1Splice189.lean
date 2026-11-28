import SixSingletonQ1Slots189
import SixRootedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore ArticulationPair
open private Cmp from SixCutFar189
open private Dark from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

theorem splice_route_to_complement {A : Finset V} {x y u v : V}
    (left : RouteOn G A x y) (right : RouteOn G (univ\A) u v) (edge : G.Adj y u) :
    Traceable G := by
  have disj : Disjoint A (univ\A) := by
    rw [Finset.disjoint_left]
    exact fun _ h k=>(mem_sdiff.mp k).2 h
  obtain ⟨p,hp,ps⟩ := left.join right disj edge
  refine ⟨x,v,p,hp,fun w=>(ps w).mpr ?_⟩
  by_cases hw : w∈A
  · exact mem_union_left _ hw
  · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hw⟩)

theorem six_q1_splice_core (F : SixVisibleData G D s) (bal : nearBal D={z})
    (ea : (EA D).card≤2) (eb : (EB D).card≤2)
    {u v y : V} (core : y∈(Dark D).erase z) (edge : G.Adj y u)
    (tail : RouteOn G (univ\(Dark D).erase z) u v) : Traceable G := by
  obtain ⟨sz,deg⟩ := six_q1_core_bounds F bal ea eb
  obtain ⟨x,_,r⟩ := rooted_side_route (G:=G) ((Dark D).erase z) core (fun i hi j hj _ _=>by
    have h := deg i hi
    have k := deg j hj
    omega)
  exact splice_route_to_complement r tail edge

theorem six_q1_splice_dense (F : SixVisibleData G D s) (bal : nearBal D={z})
    (ea : (EA D).card≤2) (eb : (EB D).card≤2)
    (dense : 4≤(inside G (Dark D) z).card)
    {u v y : V} (core : y∈Dark D) (edge : G.Adj y u)
    (tail : RouteOn G (univ\Dark D) u v) : Traceable G := by
  have mindeg (w : V) (hw : w∈Dark D) : 4≤(inside G (Dark D) w).card := by
    rw [←F.darkPart,bal,mem_union,mem_union,mem_singleton] at hw
    rcases hw with (h|h)|rfl
    · have q := F.strictA_local w h
      omega
    · have q := F.strictB_local w h
      omega
    exact dense
  obtain ⟨x,_,r⟩ := rooted_side_route (G:=G) (Dark D) core (fun i hi j hj _ _=>by
    have h := mindeg i hi
    have k := mindeg j hj
    have sz := F.dark7
    omega)
  exact splice_route_to_complement r tail edge

#print axioms splice_route_to_complement
#print axioms six_q1_splice_core
#print axioms six_q1_splice_dense
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
