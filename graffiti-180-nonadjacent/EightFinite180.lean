import EightPrime180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
private theorem equal_after_two {a b c : Bool} (h : a≠b) (j : b≠c) : a=c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Two disjoint triangles bound the order by six. A third triangle and a
five-cycle exclude all remaining deletion pairs except the four listed. -/
theorem ranks_upper (Z : Finset V) (col : TwoColor G Z) : Z.card≤6 ∧ (6≤Z.card → univ\Z∈pairs) := by
  obtain ⟨c,proper⟩ := (color_function ..).mp col
  have tri (i j k : V) (ij : G.Adj i j) (jk : G.Adj j k) (ki : G.Adj k i) :
      ∃ x∈({i,j,k}:Finset V),x∉Z := by
    by_contra! all
    have im := all i (by simp)
    have jm := all j (by simp)
    have km := all k (by simp)
    exact (proper k km i im ki) (equal_after_two (proper i im j jm ij) (proper j jm k km jk)).symm
  obtain ⟨u,ui,uz⟩ := tri 0 4 6 (by decide) (by decide) (by decide)
  obtain ⟨v,vi,vz⟩ := tri 1 5 7 (by decide) (by decide) (by decide)
  have ne : u≠v := fun eq => Finset.disjoint_left.mp
    (by decide : Disjoint ({0,4,6}:Finset V) ({1,5,7}:Finset V)) ui (eq ▸ vi)
  have incl : ({u,v}:Finset V)⊆univ\Z :=
    insert_subset (mem_sdiff.mpr ⟨mem_univ _,uz⟩) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _,vz⟩))
  have size := card_le_card incl
  rw [card_pair ne] at size
  have sz := card_sdiff_add_card_eq_card (subset_univ Z)
  have n : (univ:Finset V).card=8 := by decide
  refine ⟨by omega,fun large => ?_⟩
  have eq : ({u,v}:Finset V)=univ\Z := eq_of_subset_of_card_le incl (by rw [card_pair ne];omega)
  obtain ⟨w,wm,wz⟩ := tri 0 3 7 (by decide) (by decide) (by decide)
  have pent : ∃ x∈({1,4,6,2,5}:Finset V),x∉Z := by
    by_contra! all
    have h1 := all 1 (by decide)
    have h4 := all 4 (by decide)
    have h6 := all 6 (by decide)
    have h2 := all 2 (by decide)
    have h5 := all 5 (by decide)
    have e1 := equal_after_two (proper 1 h1 4 h4 (by decide)) (proper 4 h4 6 h6 (by decide))
    have e2 := equal_after_two (proper 6 h6 2 h2 (by decide)) (proper 2 h2 5 h5 (by decide))
    exact (proper 1 h1 5 h5 (by decide)) (e1.trans e2)
  obtain ⟨t,tm,tz⟩ := pent
  have member (x : V) (off : x∉Z) : x∈({u,v}:Finset V) := eq ▸ mem_sdiff.mpr ⟨mem_univ _,off⟩
  rw [←eq]
  exact (show ∀ i∈({0,4,6}:Finset V),∀ j∈({1,5,7}:Finset V),
    (∃ w∈({0,3,7}:Finset V),w∈({i,j}:Finset V)) →
    (∃ t∈({1,4,6,2,5}:Finset V),t∈({i,j}:Finset V)) → ({i,j}:Finset V)∈pairs by decide)
    u ui v vi ⟨w,wm,member w wz⟩ ⟨t,tm,member t tz⟩

theorem lower_pair (S : Finset V) (sm : S∈pairs) : TwoColor G (univ\S) := by
  simp only [pairs,mem_insert,mem_singleton] at sm
  rcases sm with rfl|rfl|rfl|rfl
  · exact ⟨{1,3,6},{2,4,7},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩
  · exact ⟨{2,4,7},{3,5,6},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩
  · exact ⟨{0,1,2},{3,5,6},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩
  · exact ⟨{0,1,2},{3,4,5},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩

theorem exact_pairs : bipartiteNum G=6 ∧
    ∀ S : Finset V,S.card=2 → (TwoColor G (univ\S) ↔ S∈pairs) := by
  have ⟨Z,col,mx⟩ := optB G
  have hi := (ranks_upper Z col).1
  have lo := size_bip G (lower_pair X (by decide))
  change (univ\X).card≤bipartiteNum G at lo
  have sz : (univ\X).card=6 := by decide
  refine ⟨by omega,fun S two => ⟨fun c => ?_,lower_pair S⟩⟩
  have eq := card_sdiff_add_card_eq_card (subset_univ S)
  have n : (univ:Finset V).card=8 := by decide
  have yes := (ranks_upper _ c).2 (by omega)
  simpa only [Finset.sdiff_sdiff_eq_self (subset_univ S)] using yes


#print axioms Eight.exact_pairs
end Minimal180.PairRepair.Eight
