import AdjacentCutFiveTopFlatten189
import AdjacentCutFiveOrderSeventeenArithmetic189
import AdjacentCutFiveTwinFourteen189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint shore_nonempty from AdjacentCutFiveActual189
open private degree_le_shore_add_one from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private key classSet prof key_facts profile_size from AdjacentCutFiveTopProfiles189
open private local_profile_conditions key_b_port key_a_port from AdjacentCutFiveTopFlatten189
open private cut_profile_budget cross_profile_budget from AdjacentCutFiveTopFlatten189
open private all_common_of_four_equal_odd order_counts_of_two_shores order_le_sixteen_of_adjacent_singleton_shore from AdjacentCutFiveTopFlatten189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem all_common_incidence_of_symmetric_profile
    (hc : G.Connected) (ab : G.Adj a b) {C : Cmp G a b}
    (hs : (prof C).symmetricProfile) : ∀ z∈Shore C,G.Adj a z ↔ G.Adj b z := by
  intro z zc
  have za : z≠a := fun e=>(shore_off C).1 (e ▸ zc)
  have zb : z≠b := fun e=>(shore_off C).2 (e ▸ zc)
  have equal (k : key G a b z=5) : G.dist a z=G.dist b z := by
    obtain ⟨da,db,_⟩ := key_facts hc ab z
    rw [k] at da db
    exact da.trans db.symm
  constructor
  · intro av
    rcases key_a_port hc ab zb av with h|h
    · have q : (classSet C 3).Nonempty := ⟨z,mem_filter.mpr ⟨zc,h⟩⟩
      have ct := card_pos.mpr q
      have ze : (classSet C 3).card=0 := hs.2.2.1
      omega
    · exact dist_eq_one_iff_adj.mp ((equal h).symm.trans (dist_eq_one_iff_adj.mpr av))
  · intro bv
    rcases key_b_port hc ab za bv with h|h
    · have q : (classSet C 4).Nonempty := ⟨z,mem_filter.mpr ⟨zc,h⟩⟩
      have ct := card_pos.mpr q
      have ze : (classSet C 4).card=0 := hs.2.2.2
      omega
    · exact dist_eq_one_iff_adj.mp ((equal h).trans (dist_eq_one_iff_adj.mpr bv))

theorem twins_of_actual_adjacent_two_shores_order_seventeen
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2) (n : 17≤Fintype.card V) :
    ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z) := by
  classical
  have hi := order_le_seventeen_of_actual_adjacent_two_shores hc ab even conn degree two
  obtain ⟨C,D,cd,cov⟩ := actual_two_shores two
  have minside {K L : Cmp G a b} (kl : K≠L)
      (cover : ∀ {z : V},z≠a → z≠b → z∈Shore K ∨ z∈Shore L) :
      4≤(Shore K).card := by
    have pos := card_pos.mpr (shore_nonempty K)
    by_cases one : (Shore K).card=1
    · have s := order_le_sixteen_of_adjacent_singleton_shore hc ab even conn degree kl cover one
      omega
    by_contra small
    obtain ⟨u,uk,v,vk,uv⟩ := one_lt_card.mp (show 1<(Shore K).card by omega)
    have du := degree_le_shore_add_one K uk
    have dv := degree_le_shore_add_one K vk
    rcases degree u v uv with h|h <;> omega
  have run {K L : Cmp G a b} (kl : K≠L)
      (cover : ∀ {z : V},z≠a → z≠b → z∈Shore K ∨ z∈Shore L)
      (sm : (Shore K).card≤(Shore L).card) :
      ∀ z,z≠a → z≠b → (G.Adj a z ↔ G.Adj b z) := by
    have sc := order_counts_of_two_shores ab.ne kl cover
    have lc := local_profile_conditions hc ab conn degree (minside kl cover)
    have rc := local_profile_conditions hc ab conn degree (minside kl.symm
      (fun za zb=>(cover za zb).symm))
    have sh := AdjProfile.compact_at_seventeen (prof K) (prof L)
      (by simpa only [profile_size] using sm)
      (by simp only [profile_size]; omega)
      lc rc (cut_profile_budget hc ab even kl) (cross_profile_budget hc ab even kl)
      (cross_profile_budget hc ab even kl.symm)
    rcases sh with ⟨k4,ko4⟩|⟨ks,ls⟩
    · rw [profile_size] at k4
      have small := order_le_sixteen_of_adjacent_four_common_shore hc ab even kl cover k4
        (all_common_of_four_equal_odd hc ab degree k4 ko4)
      omega
    intro z za zb
    rcases cover za zb with zk|zl
    · exact all_common_incidence_of_symmetric_profile hc ab ks z zk
    · exact all_common_incidence_of_symmetric_profile hc ab ls z zl
  by_cases small : (Shore C).card≤(Shore D).card
  · exact run cd cov small
  · exact run cd.symm (fun za zb=>(cov za zb).symm) (by omega)

theorem traceable_of_actual_adjacent_two_shores_order_seventeen
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2) (n : 17≤Fintype.card V) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support :=
  traceable_of_adjacent_twins_two_shores_order_ge_fourteen hc ab even
    (twins_of_actual_adjacent_two_shores_order_seventeen hc ab even conn degree two n) conn degree two
    (by omega)

#print axioms twins_of_actual_adjacent_two_shores_order_seventeen
#print axioms traceable_of_actual_adjacent_two_shores_order_seventeen
theorem order_le_sixteen_of_actual_adjacent_two_unequal_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2)
    (notTwins : ¬∀ z,z≠a → z≠b → (G.Adj a z ↔ G.Adj b z)) :
    Fintype.card V≤16 := by
  by_contra large
  exact notTwins (twins_of_actual_adjacent_two_shores_order_seventeen hc ab even conn degree two
    (Nat.lt_of_not_ge large))

#print axioms order_le_sixteen_of_actual_adjacent_two_unequal_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
