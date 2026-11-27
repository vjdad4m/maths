import DegreeFiveActualCut189
import DegreeFiveRouteBasic189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveBalancedCommonRoot189
import DegreeFiveBalancedTerminal189
import DegreeFiveMixedFourForeign189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem traceable_of_balanced_exclusive_shore_at_most_seven
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : 2≤(portColor D a).card) (pB : 2≤(portColor D b).card)
    (small : (Shore D).card≤7) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  let T : Split G a b :=
    ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,shore_connected D,
      (fun u ud v vc e=>by
        rcases shore_closed D u ud v e with rfl|rfl|vD
        · exact (shore_off C).1 vc
        · exact (shore_off C).2 vc
        exact disjoint_left.mp (shore_disjoint cd) vc vD),
      shore_hit_a ab conn D,shore_hit_b ab conn D,(fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  obtain ⟨_,x,xC,ax,bx,y,wing⟩ := rooted_common_side_when_exclusive_contacts_balanced
    hc two even conn degree cd cover shared none pA pB
  obtain ⟨u,uD,v,vD,au,bv,path⟩ :=
    Split.Five.terminal_route_of_small_balanced_exclusive_shore T conn small pA pB degree none
  have middle : RouteOn G (insert b (insert a (Shore D))) a b := by
    have q : RouteOn G (Shore D) u v := path
    have p := q.prefix au (shore_off D).1
    exact p.suffix bv.symm (fun h=>(mem_insert.mp h).elim ab.symm (shore_off D).2)
  have off : Disjoint (insert b (insert a (Shore D))) (Shore C) := by
    apply disjoint_left.mpr
    intro z h zC
    rcases mem_insert.mp h with rfl|h
    · exact (shore_off C).2 zC
    rcases mem_insert.mp h with rfl|h
    · exact (shore_off C).1 zC
    exact disjoint_left.mp (shore_disjoint cd) zC h
  obtain ⟨w,wp,ws⟩ := middle.join wing off bx
  refine ⟨a,y,w,wp,fun z=>(ws z).mpr ?_⟩
  rcases cover z with rfl|rfl|zC|zD
  · simp
  · simp
  · exact mem_union_right _ zC
  exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zD))

theorem traceable_of_balanced_mixed_shore_at_four_foreign
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : 2≤(portColor D a).card) (pB : 2≤(portColor D b).card)
    {c d u v : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (vD : v∈Shore D) (dv : G.Adj d v)
    (uv : G.Adj u v) (three : (portColor D c).card≤3)
    (four : (portColor C c).card=4) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  have du : ¬G.Adj d u := by
    intro h
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact none _ uD ⟨cu,h⟩
    exact none _ uD ⟨h,cu⟩
  have small := exclusive_shore_le_seven_of_mixed_with_four_foreign hc two even cd
    perm uD cu du vD dv uv three four
  exact traceable_of_balanced_exclusive_shore_at_most_seven hc two even conn degree cd cover
    shared none pA pB small

#print axioms traceable_of_balanced_exclusive_shore_at_most_seven
#print axioms traceable_of_balanced_mixed_shore_at_four_foreign
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
