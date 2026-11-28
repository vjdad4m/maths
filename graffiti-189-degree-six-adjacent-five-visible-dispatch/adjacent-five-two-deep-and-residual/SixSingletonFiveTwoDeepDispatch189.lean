import SixSingletonFiveTwoDeepPlans189
import SixSingletonFiveTwoDeepSparseCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private deep_shape_two deep_every_balance_dark_hit from SixSingletonFiveTwoDeepSparseCore189
open private dark_core_six from SixSingletonFiveTwoDeepBase189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

private theorem deep_full_dark_support {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w : V} (zm : z∈D\S) (wm : w∈D\S) (zw : z≠w) :
    insert w (insert z S)=D := by
  have eq := (deep_shape_two F zm wm zw).2
  have zw' : w∈D.erase z := mem_erase.mpr ⟨zw.symm,(mem_sdiff.mp wm).1⟩
  rw [eq,insert_comm,insert_erase zw',insert_erase (mem_sdiff.mp zm).1]

private theorem deep_finish_either {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {h z c t : V} (hm : h∈L∪R) (p : RouteOn G D h z)
    (bdr : RouteOn G K c t) (zc : G.Adj z c) (tK : t∈K) :
    ∃ u v,∃ q : G.Walk u v,q.IsPath ∧ ∀ u,u∈q.support := by
  rcases mem_union.mp hm with l|r
  · exact finish_by_balance p bdr F.sa F.ax (F.xL h l) zc (F.commonB t tK).symm F.by'
  have p1 := p.prefix (F.yR h r) (by decide)
  have p2 := p1.prefix F.by' (by decide)
  have p3 := p2.prefix F.sb (by decide)
  have q1 := bdr.suffix (F.commonA t tK).symm (by decide)
  have q2 := q1.suffix F.ax (by decide)
  obtain ⟨q,qp,qs⟩ := p3.join q2 (by decide) zc
  exact ⟨s,x,q,qp,fun u=>(qs u).mpr ((by decide : ∀ v : V,
    v∈insert s (insert b (insert y D)) ∪ insert x (insert a K)) u)⟩

private theorem deep_sparse_chain {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w n : V} (zm : z∈D\S) (wm : w∈D\S) (zw : G.Adj z w)
    (nl : n∈S) (nz : G.Adj n z) (low : (inside G D w).card≤3)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  obtain ⟨h,hm,p⟩ := deep_root_through_strict_core F zm wm zw.ne nl
  have p1 := p.suffix nz (mem_sdiff.mp zm).2
  have p2 := p1.suffix zw (fun m=>(mem_insert.mp m).elim zw.ne.symm (mem_sdiff.mp wm).2)
  rw [deep_full_dark_support F zm wm zw.ne] at p2
  obtain ⟨c,_,t,tm,rt,wc⟩ := deep_early_common_plan F wm zm zw.ne.symm low hc even
  exact deep_finish_either F hm p2 rt wc tm

private theorem deep_port_full_of_no_strict {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w : V} (zm : z∈D\S) (wm : w∈D\S) (zw : G.Adj z w)
    (no : ¬∃ t∈S,G.Adj t z) : ∀ u∈P,G.Adj z u := by
  have sh := (deep_shape_two F zm wm zw.ne).1
  have sub : G.neighborFinset z⊆insert w P := by
    intro t tm
    have e := (mem_neighborFinset _ _ _).mp tm
    rcases mem_union.mp (F.darkBounds z (mem_sdiff.mp zm).1 t e) with td|tp
    · have tc : t∉S := fun m=>no ⟨t,m,e.symm⟩
      have m := mem_sdiff.mpr ⟨td,tc⟩
      rw [sh,mem_insert,mem_singleton] at m
      exact mem_insert.mpr (.inl (m.resolve_left e.ne.symm))
    exact mem_insert_of_mem tp
  have eq := eq_of_subset_of_card_le sub (by
    rw [card_neighborFinset_eq_degree]
    have i := card_insert_le w P
    have j := F.darkHigh z (mem_sdiff.mp zm).1
    have k := p5
    omega)
  intro u um
  exact (mem_neighborFinset _ _ _).mp (eq.symm ▸ mem_insert_of_mem um)

private theorem deep_route_core_no_strict_hits {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w : V} (zm : z∈D\S) (wm : w∈D\S) (zw : G.Adj z w)
    (noZ : ¬∃ t∈S,G.Adj t z) (noW : ¬∃ t∈S,G.Adj t w)
    (lowW : (inside G D w).card≤3)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  have sh := (deep_shape_two F zm wm zw.ne).1
  have pure (u : V) (um : u∈S) : inside G D u=inside G S u := by
    ext t
    simp only [inside,mem_filter]
    refine ⟨fun h=>⟨?_,h.2⟩,fun h=>⟨F.core_sub h.1,h.2⟩⟩
    by_contra p
    have m := mem_sdiff.mpr ⟨h.1,p⟩
    rw [sh,mem_insert,mem_singleton] at m
    exact m.elim (fun e=>noZ ⟨u,um,e ▸ h.2⟩) (fun e=>noW ⟨u,um,e ▸ h.2⟩)
  obtain ⟨l,ll⟩ : L.Nonempty := card_pos.mp (by have h := F.l2; omega)
  obtain ⟨r,rr⟩ : R.Nonempty := card_pos.mp (by have h := F.r2; omega)
  have lr : l≠r := fun e=>disjoint_left.mp F.apart ll (e.symm ▸ rr)
  have route : RouteOn G S l r := by
    apply terminal_route_on_of_local_ore S (F.left_sub ll) (F.right_sub rr) lr
    intro u um v vm _ _
    have p := F.dark5 u um
    have q := F.dark5 v vm
    have t := dark_core_six F
    rw [pure u um] at p
    rw [pure v vm] at q
    omega
  have pp1 := route.prefix (F.xL l ll) (fun xS=> (by decide : x∉D) (F.core_sub xS))
  have pp2 := pp1.prefix F.ax (fun aS=>(mem_insert.mp aS).elim (by decide : a≠x)
    (fun h=>(by decide : a∉D) (F.core_sub h)))
  have pp3 := pp2.prefix F.sa (fun m=>(mem_insert.mp m).elim (by decide : s≠a)
    (fun m=>(mem_insert.mp m).elim (by decide : s≠x) (fun h=>(by decide : s∉D) (F.core_sub h))))
  obtain ⟨c,_,t,tm,kp,wc⟩ := deep_early_common_plan F wm zm zw.ne.symm lowW hc even
  have b1 := kp.prefix wc (fun wK=>disjoint_left.mp (by decide : Disjoint K D) wK (mem_sdiff.mp wm).1)
  have wz : z∉insert w K := fun m=>(mem_insert.mp m).elim zw.ne
    (fun zK=>disjoint_left.mp (by decide : Disjoint K D) zK (mem_sdiff.mp zm).1)
  have b2 := b1.prefix zw wz
  have b3 := b2.prefix ((deep_port_full_of_no_strict F zm wm zw noZ) y (by decide)).symm (by
    intro e; rcases mem_insert.mp e with q|q
    · exact (by decide : y∉D) (q ▸ (mem_sdiff.mp zm).1)
    rcases mem_insert.mp q with q|q
    · exact (by decide : y∉D) (q ▸ (mem_sdiff.mp wm).1)
    exact (by decide : y∉K) q)
  have b4 := b3.suffix (F.commonB t tm).symm (by
    intro e; rcases mem_insert.mp e with q|q
    · exact (by decide : b≠y) q
    rcases mem_insert.mp q with q|q
    · exact (by decide : b∉D) (q ▸ (mem_sdiff.mp zm).1)
    rcases mem_insert.mp q with q|q
    · exact (by decide : b∉D) (q ▸ (mem_sdiff.mp wm).1)
    exact (by decide : b∉K) q)
  have eqD := deep_full_dark_support F zm wm zw.ne
  have sep : Disjoint (insert s (insert a (insert x S))) (insert b (insert y (insert z (insert w K)))) := by
    apply disjoint_left.mpr
    intro u ju ku
    simp only [mem_insert] at ju ku
    rcases ju with rfl|rfl|rfl|um
    · exact ku.elim (by decide) (fun v=>v.elim (by decide) (fun v=>v.elim
        (fun e=>(by decide : s∉D) (e ▸ (mem_sdiff.mp zm).1)) (fun v=>v.elim
        (fun e=>(by decide : s∉D) (e ▸ (mem_sdiff.mp wm).1)) (by decide))))
    · exact ku.elim (by decide) (fun v=>v.elim (by decide) (fun v=>v.elim
        (fun e=>(by decide : a∉D) (e ▸ (mem_sdiff.mp zm).1)) (fun v=>v.elim
        (fun e=>(by decide : a∉D) (e ▸ (mem_sdiff.mp wm).1)) (by decide))))
    · exact ku.elim (by decide) (fun v=>v.elim (by decide) (fun v=>v.elim
        (fun e=>(by decide : x∉D) (e ▸ (mem_sdiff.mp zm).1)) (fun v=>v.elim
        (fun e=>(by decide : x∉D) (e ▸ (mem_sdiff.mp wm).1)) (by decide))))
    have d := F.core_sub um
    rcases ku with rfl|rfl|rfl|rfl|uK
    · exact (by decide : b∉D) d
    · exact (by decide : y∉D) d
    · exact (mem_sdiff.mp zm).2 um
    · exact (mem_sdiff.mp wm).2 um
    exact disjoint_left.mp (by decide : Disjoint K D) uK d
  obtain ⟨q,qp,qs⟩ := pp3.join b4 sep (F.yR r rr).symm
  refine ⟨s,b,q,qp,fun u=>(qs u).mpr ?_⟩
  simp only [mem_union,mem_insert]
  have cover : ∀ i : V,i=s ∨ i=a ∨ i=x ∨ i=b ∨ i=y ∨ i∈K ∨ i∈D := by decide
  rcases cover u with h|h|h|h|h|h|h <;> try tauto
  rw [←eqD,mem_insert,mem_insert] at h
  tauto

#print axioms deep_sparse_chain
#print axioms deep_route_core_no_strict_hits
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
