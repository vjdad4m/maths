import AdjacentCutFiveFourteenSingletonProfiles189
import AdjacentCutFiveSixteenSingletonGeometry189
import DegreeFiveNonadjacentComplete189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private key classSet prof sa sb pa key_facts profile_size from AdjacentCutFiveTopProfiles189
open private local_profile_conditions cut_profile_budget cross_profile_budget key_a_port key_b_port
  from AdjacentCutFiveTopFlatten189
open private d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem compact_graph_fourteen_singleton_profile
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (one : (Shore C).card=1) (big : (Shore D).card=11) :
    ∃ s, Shore C={s} ∧ G.Adj a s ∧ G.Adj b s ∧
      (let y := prof D
       AdjProfile.Singleton14Rows y.ea y.eb y.ec y.oa y.ob y.oc ∨
       AdjProfile.Singleton14Rows y.eb y.ea y.ec y.ob y.oa y.oc) := by
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
  rw [source] at cc cr
  exact ⟨s,eq,as',bs',AdjProfile.compact_fourteen_singleton (prof D)
    ((profile_size D).trans big) local' cc cr⟩



/-- The old singleton-to-nonadjacent transfer also closes three of the
order-fourteen rows, together with swapped terminal labels. -/
theorem traceable_of_adjacent_singleton_eleven_unique_four
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (one : (Shore C).card=1)
    (ea : 0<(prof D).ea) (eb : 0<(prof D).eb)
    (ec : (prof D).ec=0) (oa : (prof D).oa=1) (ob : (prof D).ob=1)
    (four : 4≤(prof D).ea ∨ 4≤(prof D).eb) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨s,eq⟩ := card_eq_one.mp one
  obtain ⟨u,uc,au⟩ := shore_hit_a ab.ne conn C
  obtain ⟨v,vc,bv⟩ := shore_hit_b ab.ne conn C
  have ueq : u=s := by simpa [eq] using uc
  have veq : v=s := by simpa [eq] using vc
  have sc : s∈Shore C := by simp [eq]
  obtain ⟨x,y,xy,non,cut⟩ := nonadjacent_separator_of_common_other_unique_and_four_even
    hc ab even cd sc (ueq ▸ au) (veq ▸ bv) ea eb ec oa ob four
  exact FiveActualCut.traceable_at_actual_five_nonadjacent_cut hc xy non even conn degree cut

#print axioms compact_graph_fourteen_singleton_profile
#print axioms traceable_of_adjacent_singleton_eleven_unique_four
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
