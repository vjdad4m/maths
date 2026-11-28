import AdjacentCutFiveTopFlatten189
import AdjacentCutFiveFifteenSingletonArithmetic189
import AdjacentCutFiveSixteenSingletonGeometry189
import AdjacentCutFiveProfilePorts189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_hit_a shore_hit_b shore_disjoint from AdjacentCutFiveActual189
open private key classSet prof sa sb pa key_facts profile_size from AdjacentCutFiveTopProfiles189
open private local_profile_conditions cut_profile_budget cross_profile_budget key_a_port key_b_port
  from AdjacentCutFiveTopFlatten189
open private d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem compact_graph_singleton_fifteen_profile
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (one : (Shore C).card=1) (big : (Shore D).card=12) :
    ∃ s, Shore C={s} ∧ G.Adj a s ∧ G.Adj b s ∧
      (((prof D).ea=3 ∧ (prof D).eb=3 ∧ (prof D).ec=1 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=3) ∨
      ((prof D).ea=3 ∧ (prof D).eb=4 ∧ (prof D).ec=0 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=3) ∨
      ((prof D).ea=3 ∧ (prof D).eb=4 ∧ (prof D).ec=0 ∧ (prof D).oa=1 ∧ (prof D).ob=2 ∧ (prof D).oc=2) ∨
      ((prof D).ea=4 ∧ (prof D).eb=3 ∧ (prof D).ec=0 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=3) ∨
      ((prof D).ea=4 ∧ (prof D).eb=3 ∧ (prof D).ec=0 ∧ (prof D).oa=2 ∧ (prof D).ob=1 ∧ (prof D).oc=2) ∨
      ((prof D).ea=4 ∧ (prof D).eb=4 ∧ (prof D).ec=0 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=2)) := by
  classical
  obtain ⟨s,eq⟩ := card_eq_one.mp one
  obtain ⟨u,uc,au⟩ := shore_hit_a ab.ne conn C
  obtain ⟨v,vc,bv⟩ := shore_hit_b ab.ne conn C
  have ueq : u=s := by simpa [eq] using uc
  have veq : v=s := by simpa [eq] using vc
  have as' : G.Adj a s := ueq ▸ au
  have bs' : G.Adj b s := veq ▸ bv
  have k : key G a b s=5 := by simp [key,dist_eq_one_iff_adj.mpr as',dist_eq_one_iff_adj.mpr bs']
  have source : prof C=⟨0,0,0,0,0,1⟩ := by simp [prof,classSet,eq,k,Finset.filter_singleton]
  have local' := local_profile_conditions hc ab conn degree (show 4≤(Shore D).card by omega)
  have cc := cut_profile_budget hc ab even cd
  have cr := cross_profile_budget hc ab even cd
  have cl := cross_profile_budget hc ab even cd.symm
  rw [source] at cc cr cl
  exact ⟨s,eq,as',bs',AdjProfile.compact_fifteen_singleton (prof D)
    ((profile_size D).trans big) local' cc cr cl⟩

    
#print axioms compact_graph_singleton_fifteen_profile

theorem alternate_cut_or_three_profiles_of_adjacent_singleton_twelve_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (one : (Shore C).card=1) (big : (Shore D).card=12) :
    (∃ x y : V,x≠y ∧ ¬G.Adj x y ∧ ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected) ∨
    ((prof D).ea=3 ∧ (prof D).eb=3 ∧ (prof D).ec=1 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=3) ∨
    ((prof D).ea=3 ∧ (prof D).eb=4 ∧ (prof D).ec=0 ∧ (prof D).oa=1 ∧ (prof D).ob=2 ∧ (prof D).oc=2) ∨
    ((prof D).ea=4 ∧ (prof D).eb=3 ∧ (prof D).ec=0 ∧ (prof D).oa=2 ∧ (prof D).ob=1 ∧ (prof D).oc=2) := by
  classical
  obtain ⟨s,SC,as',bs',p⟩ := compact_graph_singleton_fifteen_profile hc ab even conn degree cd one big
  have sc : s∈Shore C := by simp [SC]
  have cut (ea : 0<(prof D).ea) (eb : 0<(prof D).eb) (ec : (prof D).ec=0)
      (oa : (prof D).oa=1) (ob : (prof D).ob=1)
      (four : 4≤(prof D).ea ∨ 4≤(prof D).eb) :
      ∃ x y : V,x≠y ∧ ¬G.Adj x y ∧ ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected :=
    nonadjacent_separator_of_common_other_unique_and_four_even hc ab even cd sc as' bs' ea eb ec oa ob four
  rcases p with p|p|p|p|p|p
  · exact .inr (.inl p)
  · obtain ⟨ea,eb,ec,oa,ob,_⟩ := p
    exact .inl (cut (by omega) (by omega) ec oa ob (.inr eb.ge))
  · exact .inr (.inr (.inl p))
  · obtain ⟨ea,eb,ec,oa,ob,_⟩ := p
    exact .inl (cut (by omega) (by omega) ec oa ob (.inl ea.ge))
  · exact .inr (.inr (.inr p))
  · obtain ⟨ea,eb,ec,oa,ob,_⟩ := p
    exact .inl (cut (by omega) (by omega) ec oa ob (.inl ea.ge))

#print axioms alternate_cut_or_three_profiles_of_adjacent_singleton_twelve_shores

theorem high_of_other_shore_singleton
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (single : Shore C={s})
    {z : V} (zd : z∈Shore D) : 5≤G.degree z := by
  classical
  have sm : s∈Shore C := by simp [single]
  have neq : s≠z := by
    intro h
    exact (Finset.disjoint_left.mp (shore_disjoint cd) sm) (h ▸ zd)
  have sub : G.neighborFinset s⊆{a,b} := by
    intro w wm
    have sw := (SimpleGraph.mem_neighborFinset G s w).mp wm
    rcases shore_closed C s sm w sw with q|q|q
    · simp [q]
    · simp [q]
    · have e : w=s := by simpa [single] using q
      exact (sw.ne e.symm).elim
  have bound := Finset.card_le_card sub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at bound
  have small : ({a,b}:Finset V).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  exact (degree s z neq).resolve_left (by omega)

#print axioms high_of_other_shore_singleton
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
