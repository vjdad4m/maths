import SixSingletonFiveTwoDeepParity189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 k3 p5 finish_by_balance finish_plain from SixSingletonFiveShallowRoute189
open private dark_core_six from SixSingletonFiveTwoDeepBase189
open private small_common_path from SixSingletonFiveDensePorts189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem deep_common_complete_without_balance {L R S : Finset V} {T c : V}
    (F : ProfileTwoDeep G L R S T) (ck : c∈K) (no : ¬∃ z∈D\S,G.Adj z c) :
    ∀ u∈P,u≠c → G.Adj c u := by
  have sub : G.neighborFinset c⊆insert a (insert b (P.erase c)) := by
    intro u um
    have cu := (mem_neighborFinset _ _ _).mp um
    rcases mem_insert.mp (F.commonBounds c ck u cu) with e|e
    · exact mem_insert.mpr (.inl e)
    rcases mem_insert.mp e with e|e
    · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
    rcases mem_union.mp e with e|e
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨cu.ne.symm,e⟩))
    exact (no ⟨u,e,cu.symm⟩).elim
  have pc : c∈P := mem_insert_of_mem (mem_insert_of_mem ck)
  have eq := eq_of_subset_of_card_le sub (by
    rw [card_neighborFinset_eq_degree]
    have i := card_insert_le a (insert b (P.erase c))
    have j := card_insert_le b (P.erase c)
    have k := card_erase_of_mem pc
    rw [p5] at k
    have h := F.commonHigh c ck
    omega)
  intro u um ne
  exact (mem_neighborFinset _ _ _).mp (eq.symm ▸
    mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨ne,um⟩)))

/-- For the order-16 normalized board with two balances and one deep
vertex, the common ports still form a connected triple. A dense dark
block then gives a spanning path of the entire graph. -/
theorem traceable_of_two_deep_balances_dark_dense {L R S : Finset V} {T : V}
    (F : ProfileTwoDeep G L R S T) (hc : G.Connected)
    (even : ∀ z,(EvenFrom G z).card≤7) (dense : ∀ z∈D,4≤(inside G D z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  obtain ⟨l,ll⟩ : L.Nonempty := card_pos.mp (by have v:=F.l2; omega)
  obtain ⟨r,rr⟩ : R.Nonempty := card_pos.mp (by have v:=F.r2; omega)
  have whole {u v : V} (ud : u∈D) (vd : v∈D) (uv : u≠v) : RouteOn G D u v :=
    eight_high_core_route D S F.core_sub d8 (by rw [dark_core_six F]; decide) dense F.dark5 ud vd uv
  have route_of_hit {c t : V} (tm : t∈K) (path : RouteOn G K c t)
      (hit : ∃ z∈D\S,G.Adj z c) :
      ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
    obtain ⟨z,zm,zc⟩ := hit
    have d := (mem_sdiff.mp zm).1
    have nz := (mem_sdiff.mp zm).2
    have lp := whole (F.core_sub (F.left_sub ll)) d (fun e=>nz (e ▸ F.left_sub ll))
    exact finish_by_balance lp path F.sa F.ax (F.xL l ll) zc (F.commonB t tm).symm F.by'
  obtain ⟨c,cm,t,tm,path⟩ := small_common_path (common_two_deep_nonisolated F hc even)
  by_cases cHit : ∃ z∈D\S,G.Adj z c
  · exact route_of_hit tm path cHit
  have cp := deep_common_complete_without_balance F cm cHit
  have ly : G.Adj y c := (cp y (by decide) (fun e=>(by decide : y∉K) (e ▸ cm))).symm
  have lr : l≠r := fun e=>disjoint_left.mp F.apart ll (e.symm ▸ rr)
  have middle := whole (F.core_sub (F.left_sub ll)) (F.core_sub (F.right_sub rr)) lr
  exact finish_plain middle path F.sa F.ax (F.xL l ll) (F.yR r rr).symm ly (F.commonB t tm).symm

#print axioms traceable_of_two_deep_balances_dark_dense
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
