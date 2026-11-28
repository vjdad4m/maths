import SixSingletonFivePairPlans189
import SixEightHighCoreRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 k3 p5 finish_by_balance finish_plain from SixSingletonFiveShallowRoute189
open private d2 from CrossSaturation189
open private small_common_path from SixSingletonFiveDensePorts189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

structure ProfileThree (G : SimpleGraph V) [DecidableRel G.Adj] (L R S : Finset V) (deep : V) : Prop where
  left_sub : L⊆S
  right_sub : R⊆S
  core_sub : S⊆D
  apart : Disjoint L R
  l2 : L.card=2
  r2 : R.card=2
  balance : (D\S).card=3
  deepS : deep∈S
  deep6 : 6≤(inside G D deep).card
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
  deepL : deep∉L
  deepR : deep∉R

private theorem dark_core_five {L R S : Finset V} {T : V} (F : ProfileThree G L R S T) :
    S.card=5 := by
  have n := card_sdiff F.core_sub
  have p := card_le_card F.core_sub
  rw [F.balance,d8] at n
  rw [d8] at p
  omega

private theorem c_not_s {L R S : Finset V} {T c : V} (F : ProfileThree G L R S T) (ck : c∈K) :
    ¬G.Adj c s := by
  intro h
  have cc := F.commonBounds c ck s h
  have q : s∈insert a (insert b (P∪D)) := by
    rcases mem_insert.mp cc with e|e
    · exact mem_insert.mpr (.inl e)
    rcases mem_insert.mp e with e|e
    · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union.mp e |>.elim
      (mem_union_left _) (fun j=>mem_union_right _ (mem_sdiff.mp j).1)))
  exact (by decide : s∉insert a (insert b (P∪D))) q

private theorem c_not_core {L R S : Finset V} {T c u : V} (F : ProfileThree G L R S T)
    (ck : c∈K) (us : u∈S) : ¬G.Adj c u := by
  intro h
  have ud := F.core_sub us
  rcases mem_insert.mp (F.commonBounds c ck u h) with e|e
  · exact (by decide : a∉D) (e ▸ ud)
  rcases mem_insert.mp e with e|e
  · exact (by decide : b∉D) (e ▸ ud)
  rcases mem_union.mp e with j|j
  · exact disjoint_left.mp (by decide : Disjoint P D) j ud
  exact (mem_sdiff.mp j).2 us

private theorem core_two_from_port {L R S : Finset V} {T c u p : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (ck : c∈K) (us : u∈S) (cp : G.Adj c p) (pu : G.Adj p u) :
    u∈DistanceTwo G c :=
  d2 hc (fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ F.core_sub us))
    (c_not_core F ck us) cp pu

private theorem clear_two {c u : V} (hc : G.Connected) (ne : c≠u) (no : ¬G.Adj c u)
    {a : V} (ca : G.Adj c a) (au : G.Adj a u) : u∈DistanceTwo G c :=
  d2 hc ne no ca au

private theorem deep_hits_balance {L R S : Finset V} {T : V} (F : ProfileThree G L R S T) :
    ∃ w∈D\S,G.Adj w T := by
  by_contra no
  have sub : inside G D T⊆S := by
    intro w m
    have ⟨wd,tw⟩ := mem_filter.mp m
    by_contra ws
    exact no ⟨w,mem_sdiff.mpr ⟨wd,ws⟩,tw.symm⟩
  have n := card_le_card sub
  rw [dark_core_five F] at n
  have a := F.deep6
  omega

#print axioms deep_hits_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
