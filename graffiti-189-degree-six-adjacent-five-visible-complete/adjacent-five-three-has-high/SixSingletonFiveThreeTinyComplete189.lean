import SixSingletonFiveThreeAdjacentTwoTiny189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private paired_tiny_core_ore tiny_pair_splice from SixSingletonFiveThreeAdjacentTwoTiny189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- If the two degree-one/two balances are adjacent, their combined
deletion costs at most two degree units on any pair of other vertices.
The other six are therefore Hamilton-connected. -/
theorem three_balances_adjacent_two_tiny {L R S : Finset V} {T z w h : V}
    (F : ProfileThree G L R S T) (hc : G.Connected)
    (even : ∀ i,(EvenFrom G i).card≤7)
    (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zh : z≠h) (wh : w≠h) (zw : G.Adj z w)
    (lowZ : (inside G D z).card≤2) (lowW : (inside G D w).card≤2)
    (h4 : 4≤(inside G D h).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let E := (D.erase z).erase w
  have wE : w∈D.erase z := mem_erase.mpr ⟨zw.ne.symm,(mem_sdiff.mp wm).1⟩
  have e6 : E.card=6 := by
    change ((D.erase z).erase w).card=6
    rw [card_erase_of_mem wE,card_erase_of_mem (mem_sdiff.mp zm).1,d8]
  have eqFull : insert w (insert z E)=D := by
    change insert w (insert z ((D.erase z).erase w))=D
    rw [insert_comm,insert_erase wE,insert_erase (mem_sdiff.mp zm).1]
  have eSub : E⊆D := fun q m=>(mem_erase.mp (mem_erase.mp m).2).2
  have sE : S⊆E := fun q m=>mem_erase.mpr ⟨fun e=>(mem_sdiff.mp wm).2 (e ▸ m),
    mem_erase.mpr ⟨fun e=>(mem_sdiff.mp zm).2 (e ▸ m),F.core_sub m⟩⟩
  have ore := paired_tiny_core_ore F zm wm hm zh wh zw lowZ lowW h4
  by_cases zH : ∃ q∈E,G.Adj q z
  · obtain ⟨q,qm,qz⟩ := zH
    exact tiny_pair_splice F hc even zm wm zw lowW qm qz ore
  by_cases wH : ∃ q∈E,G.Adj q w
  · obtain ⟨q,qm,qw⟩ := wH
    have es : (D.erase w).erase z=E := by ext i; simp only [E,mem_erase]; tauto
    exact tiny_pair_splice F hc even wm zm zw.symm lowZ (es.symm ▸ qm) qw
      (paired_tiny_core_ore F wm zm hm wh zh zw.symm lowW lowZ h4)
  have zport : G.neighborFinset z⊆insert w P := by
    intro u um
    have zu := (mem_neighborFinset _ _ _).mp um
    rcases mem_union.mp (F.darkBounds z (mem_sdiff.mp zm).1 u zu) with d|p
    · by_cases q : u=w
      · exact mem_insert.mpr (.inl q)
      have m : u∈E := mem_erase.mpr ⟨q,mem_erase.mpr ⟨zu.ne.symm,d⟩⟩
      exact (zH ⟨u,m,zu.symm⟩).elim
    exact mem_insert_of_mem p
  have eq := eq_of_subset_of_card_le zport (by
    rw [card_neighborFinset_eq_degree]
    have a := card_insert_le w P
    have b := F.darkHigh z (mem_sdiff.mp zm).1
    have c := p5
    omega)
  have yZ : G.Adj z y := (mem_neighborFinset _ _ _).mp
    (eq.symm ▸ mem_insert_of_mem (by decide : y∈P))
  obtain ⟨l,ll⟩ : L.Nonempty := card_pos.mp (by rw [F.l2]; decide)
  obtain ⟨r,rr⟩ : R.Nonempty := card_pos.mp (by rw [F.r2]; decide)
  have lr : l≠r := fun e=>disjoint_left.mp F.apart ll (e.symm ▸ rr)
  have route : RouteOn G E l r := terminal_route_on_of_local_ore E
    (sE (F.left_sub ll)) (sE (F.right_sub rr)) lr
    (fun u um v vm uv _=>by rw [e6]; exact ore u um v vm uv)
  have pp1 := route.prefix (F.xL l ll) (fun xS=> (by decide : x∉D) (eSub xS))
  have pp2 := pp1.prefix F.ax (fun aS=>(mem_insert.mp aS).elim (by decide : a≠x)
    (fun h=>(by decide : a∉D) (eSub h)))
  have pp3 := pp2.prefix F.sa (fun m=>(mem_insert.mp m).elim (by decide : s≠a)
    (fun m=>(mem_insert.mp m).elim (by decide : s≠x) (fun h=>(by decide : s∉D) (eSub h))))
  obtain ⟨c,_,t,tm,kp,wc⟩ := three_balance_low_can_exit F hc even wm (by omega)
  have b1 := kp.prefix wc (fun wK=>disjoint_left.mp (by decide : Disjoint K D) wK (mem_sdiff.mp wm).1)
  have wz : z∉insert w K := fun m=>(mem_insert.mp m).elim zw.ne
    (fun zK=>disjoint_left.mp (by decide : Disjoint K D) zK (mem_sdiff.mp zm).1)
  have b2 := b1.prefix zw wz
  have b3 := b2.prefix yZ.symm (by
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
  have eqD := eqFull
  have sep : Disjoint (insert s (insert a (insert x E))) (insert b (insert y (insert z (insert w K)))) := by
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
    have d := eSub um
    rcases ku with rfl|rfl|rfl|rfl|uK
    · exact (by decide : b∉D) d
    · exact (by decide : y∉D) d
    · exact (mem_erase.mp (mem_erase.mp um).2).1 rfl
    · exact (mem_erase.mp um).1 rfl
    exact disjoint_left.mp (by decide : Disjoint K D) uK d
  obtain ⟨q,qp,qs⟩ := pp3.join b4 sep (F.yR r rr).symm
  refine ⟨s,b,q,qp,fun u=>(qs u).mpr ?_⟩
  simp only [mem_union,mem_insert]
  have cover : ∀ i : V,i=s ∨ i=a ∨ i=x ∨ i=b ∨ i=y ∨ i∈K ∨ i∈D := by decide
  rcases cover u with h|h|h|h|h|h|h <;> try tauto
  rw [←eqD,mem_insert,mem_insert] at h
  tauto

#print axioms three_balances_adjacent_two_tiny
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
