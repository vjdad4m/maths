import SixEightTripleSupport189
import SixSingletonFiveThreeExactOneLow189
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 finish_by_balance from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem split_dark_degree {L R S : Finset V} {T : V} (F : ProfileThree G L R S T) (v : V) :
    (inside G D v).card=(inside G S v).card+(inside G (D\S) v).card := by
  have eq : inside G D v=inside G S v∪inside G (D\S) v := by
    ext u
    simp only [inside,mem_filter,mem_union,mem_sdiff]
    constructor
    · intro h
      by_cases z : u∈S
      · exact .inl ⟨z,h.2⟩
      exact .inr ⟨⟨h.1,z⟩,h.2⟩
    intro h
    rcases h with ⟨us,uv⟩|⟨⟨ud,us⟩,uv⟩
    · exact ⟨F.core_sub us,uv⟩
    exact ⟨ud,uv⟩
  have d : Disjoint (inside G S v) (inside G (D\S) v) :=
    disjoint_left.mpr (fun _ h j=>(mem_sdiff.mp (mem_filter.mp j).1).2 (mem_filter.mp h).1)
  rw [eq,card_union_of_disjoint d]

private theorem low_balance_has_missing_edge {L R S : Finset V} {T : V} (F : ProfileThree G L R S T)
    (low : ∀ z∈D\S,(inside G D z).card≤3) :
    ∃ u∈D\S,∃ v∈D\S,u≠v ∧ ¬G.Adj u v := by
  classical
  by_contra no
  push_neg at no
  let W := D\S
  have minW (u : V) (us : u∈S) : 1≤(inside G W u).card := by
    have h := F.dark5 u us
    have k : inside G S u⊆S.erase u := fun v vm=>mem_erase.mpr
      ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
    have f := card_le_card k
    rw [card_erase_of_mem us,dark_core_five F] at f
    rw [split_dark_degree F] at h
    change (inside G S u).card+(inside G W u).card≥5 at h
    omega
  have maxW (u : V) (uw : u∈W) : (inside G S u).card≤1 := by
    have h := low u uw
    have k : W.erase u⊆inside G W u := fun v vm=>mem_filter.mpr
      ⟨(mem_erase.mp vm).2,no u uw v (mem_erase.mp vm).2 (mem_erase.mp vm).1.symm⟩
    have f := card_le_card k
    have w3 : W.card=3 := F.balance
    rw [card_erase_of_mem uw,w3] at f
    rw [split_dark_degree F] at h
    change (inside G S u).card+(inside G W u).card≤3 at h
    omega
  have cast (v : V) : S.bipartiteBelow G.Adj v=inside G S v := by
    ext u
    simp only [mem_bipartiteBelow,inside,mem_filter]
    exact and_congr_right (fun _=>⟨Adj.symm,Adj.symm⟩)
  have count := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s:=S) (t:=W)
  simp_rw [cast] at count
  change (∑ u∈S,(inside G W u).card) = ∑ v∈W,(inside G S v).card at count
  have l : (∑ _u∈S, (1:ℕ))≤∑ u∈S,(inside G W u).card := sum_le_sum minW
  have r : (∑ u∈W,(inside G S u).card)≤∑ _u∈W,(1:ℕ) := sum_le_sum maxW
  rw [sum_const,nsmul_eq_mul,Nat.mul_one,dark_core_five F] at l
  have w3 : W.card=3 := F.balance
  rw [sum_const,nsmul_eq_mul,Nat.mul_one,w3] at r
  omega

/-- Three balanced vertices each of dark degree at least three can be routed.
If none is high enough to be backup, a missing edge among them supplies
the backup after a first weighted clique closure. -/
theorem three_balances_dark_min_three {L R S : Finset V} {T : V}
    (F : ProfileThree G L R S T) (hc : G.Connected)
    (even : ∀ u,(EvenFrom G u).card≤7) (minimum : ∀ z∈D,3≤(inside G D z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  by_cases no : ∀ z∈D,4≤(inside G D z).card
  · exact traceable_of_three_balances_dark_dense F hc even no
  have w : ∃ z∈D\S, (inside G D z).card≤3 := by
    push_neg at no
    obtain ⟨z,zd,zlow⟩ := no
    have n : z∉S := fun m=>by have h := F.dark5 z m; omega
    exact ⟨z,mem_sdiff.mpr ⟨zd,n⟩,by omega⟩
  have either : ∃ z∈D\S,∃ h∈D\S,z≠h ∧ (inside G D z).card≤3 ∧
      (4≤(inside G D h).card ∨ ¬G.Adj z h) := by
    by_cases high : ∃ h∈D\S,4≤(inside G D h).card
    · obtain ⟨z,zm,zl⟩ := w
      obtain ⟨h,hm,hh⟩ := high
      refine ⟨z,zm,h,hm,?_,zl,.inl hh⟩
      intro eq
      subst h
      omega
    have low : ∀ h∈D\S,(inside G D h).card≤3 := by
      intro h hm
      by_contra no
      exact high ⟨h,hm,by omega⟩
    obtain ⟨z,zm,h,hm,zh,miss⟩ := low_balance_has_missing_edge F low
    exact ⟨z,zm,h,hm,zh,low z zm,.inr miss⟩
  obtain ⟨z,zm,h,hm,zh,zl,back⟩ := either
  obtain ⟨l,lm⟩ : L.Nonempty := card_pos.mp (by rw [F.l2]; decide)
  have lz : l≠z := fun e=>(mem_sdiff.mp zm).2 (e ▸ F.left_sub lm)
  have p : RouteOn G D l z := eight_triple_support D S F.core_sub d8 (dark_core_five F) F.dark5 minimum
    (F.core_sub (F.left_sub lm)) (mem_sdiff.mp zm).1 (mem_sdiff.mp hm).1 lz zh
    (mem_sdiff.mp zm).2 (mem_sdiff.mp hm).2 back
  obtain ⟨c,cm,t,tm,q,zc⟩ := three_balance_low_can_exit F hc even zm zl
  exact finish_by_balance p q F.sa F.ax (F.xL l lm) zc (F.commonB t tm).symm F.by'

#print axioms three_balances_dark_min_three
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
