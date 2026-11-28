import SixSingletonFiveDensePorts189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private d8 k3 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private common_exit_balance from SixSingletonFiveDensePorts189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure ProfileTwo (G : SimpleGraph V) [DecidableRel G.Adj] (L R S : Finset V) : Prop where
  left_sub : L⊆S
  right_sub : R⊆S
  core_sub : S⊆D
  strict6 : 6≤(L∪R).card
  apart : Disjoint L R
  l2 : 2≤L.card
  r2 : 2≤R.card
  balance : (D\S).card=2
  sa : G.Adj s a
  sb : G.Adj s b
  ax : G.Adj a x
  by' : G.Adj b y
  commonA : ∀ c∈K,G.Adj a c
  commonB : ∀ c∈K,G.Adj b c
  xL : ∀ z∈L,G.Adj x z
  yR : ∀ z∈R,G.Adj y z
  dark5 : ∀ z∈S,5≤(inside G D z).card
  darkHigh : ∀ z∈D,6≤G.degree z
  commonHigh : ∀ c∈K,6≤G.degree c
  commonBounds : ∀ c∈K,∀ z,G.Adj c z → z∈insert a (insert b (P∪(D\S)))
  darkBounds : ∀ d∈D,∀ z,G.Adj d z → z∈D∪P

theorem two_balanced_no_double_port {L R S : Finset V} (F : ProfileTwo G L R S)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∀ c∈K, ¬(G.Adj c x ∧ G.Adj c y) := by
  have sub := F.core_sub
  have ext (c : V) (ck : c∈K) : ¬(G.Adj c x ∧ G.Adj c y) := by
    rintro ⟨cx,cy⟩
    have ss : L∪R⊆DistanceTwo G c := by
      intro t tm
      have tmS := (mem_union.mp tm).elim (fun m=>F.left_sub m) (fun m=>F.right_sub m)
      have td := sub tmS
      have ct : c≠t := fun h=>disjoint_left.mp (by decide : Disjoint K D) ck (h.symm ▸ td)
      have tn : ¬G.Adj c t := by
        intro h
        rcases mem_insert.mp (F.commonBounds c ck t h) with e|e
        · exact (by decide : a∉D) (e ▸ td)
        rcases mem_insert.mp e with e|e
        · exact (by decide : b∉D) (e ▸ td)
        rcases mem_union.mp e with p|p
        · exact disjoint_left.mp (by decide : Disjoint P D) p td
        exact (mem_sdiff.mp p).2 tmS
      rcases mem_union.mp tm with h|h
      · exact d2 hc ct tn cx (F.xL t h)
      exact d2 hc ct tn cy (F.yR t h)
    have sn : ¬G.Adj c s := by
      intro h
      have g := F.commonBounds c ck s h
      have j : s∈insert a (insert b (P∪D)) := by
        rcases mem_insert.mp g with p|p
        · exact mem_insert.mpr (.inl p)
        rcases mem_insert.mp p with p|p
        · exact mem_insert_of_mem (mem_insert.mpr (.inl p))
        apply mem_insert_of_mem
        apply mem_insert_of_mem
        exact (mem_union.mp p).elim (fun h=>mem_union_left _ h)
          (fun h=>mem_union_right _ (mem_sdiff.mp h).1)
      exact (by decide : s∉insert a (insert b (P∪D))) j
    have sc : c≠s := fun e=>(by decide : s∉K) (e ▸ ck)
    have st := d2 hc sc sn (F.commonA c ck).symm F.sa.symm
    have sd : s∉L∪R := fun h=>(by decide : s∉D)
      (sub ((mem_union.mp h).elim (fun m=>F.left_sub m) (fun m=>F.right_sub m)))
    have k := card_le_card (insert_subset st ss)
    rw [card_insert_of_not_mem sd] at k
    have hi := distanceTwo_le_of_even 6 c (even c)
    have h := F.strict6
    omega
  exact ext

theorem traceable_of_two_balanced_dark_dense {L R S : Finset V} (F : ProfileTwo G L R S)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7)
    (dense : ∀ z∈D,4≤(inside G D z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let W := D\S
  have noBoth := two_balanced_no_double_port F hc even
  obtain ⟨c,cm,t,tm,z,zm,cp,zc⟩ := common_exit_balance W F.balance F.commonHigh F.commonBounds noBoth
  obtain ⟨l,lm⟩ : L.Nonempty := card_pos.mp (by have h := F.l2; omega)
  have root : l∈D\W := by
    have s := F.left_sub lm
    exact mem_sdiff.mpr ⟨F.core_sub s,fun h=>(mem_sdiff.mp h).2 s⟩
  apply traceable_five_dense_two_balances W (sdiff_subset) F.balance root dense _ cp
    (⟨z,zm,zc⟩) F.sa F.ax (F.xL l lm) (F.commonB t tm).symm F.by'
  intro u um
  have d := mem_sdiff.mp um
  by_contra p
  have s : u∈S := Classical.byContradiction (fun h=>d.2 (mem_sdiff.mpr ⟨d.1,h⟩))
  exact p (F.dark5 u s)

#print axioms traceable_of_two_balanced_dark_dense
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
