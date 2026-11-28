import AdjacentCutFiveFourteenMulti24Finish189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_hit_a shore_hit_b shore_off from AdjacentCutFiveActual189
open private key classSet from AdjacentCutFiveTopProfiles189
open private key_a_port from AdjacentCutFiveTopFlatten189
open private all_common_of_adjacent_singleton_profile_two from AdjacentCutFiveFifteenSingletonMixed189
open private singleton_multi_all_b_odd_literal literal_port_classes_from_terminal_three singleton_even_cohort_ports
  from AdjacentCutFiveFourteenMultiPorts189
open private impossible_singleton_multi_three_three_two_frame from AdjacentCutFiveFourteenMulti33Two189
open private impossible_singleton_multi_three_three_one_frame from AdjacentCutFiveFourteenMulti33One189
open private impossible_singleton_multi_two_four_two_frame from AdjacentCutFiveFourteenMulti24Finish189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private classSet_swap from AdjacentCutFiveFifteenSingletonResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

/-- The three possible equal-even-free multi-exclusive profiles of the eleven-point shore
are all impossible under the degree-five hypotheses. -/
theorem impossible_actual_adjacent_singleton_multi_empty_even_fourteen
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (CD : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1)
    (zero : (classSet D 2).card=0)
    (profiles :
      ((classSet D 0).card=2 ∧ (classSet D 1).card=4 ∧ (classSet D 3).card=1 ∧
        (classSet D 4).card=2 ∧ (classSet D 5).card=2) ∨
      ((classSet D 0).card=3 ∧ (classSet D 1).card=3 ∧ (classSet D 3).card=1 ∧
        (classSet D 4).card=2 ∧ (classSet D 5).card=2) ∨
      ((classSet D 0).card=3 ∧ (classSet D 1).card=3 ∧ (classSet D 3).card=2 ∧
        (classSet D 4).card=2 ∧ (classSet D 5).card=1)) : False := by
  classical
  obtain ⟨s,S⟩ := card_eq_one.mp one
  obtain ⟨u,um,au⟩ := shore_hit_a ab.ne conn C
  obtain ⟨v,vm,bv⟩ := shore_hit_b ab.ne conn C
  have us : u=s := by simpa [S] using um
  have vs : v=s := by simpa [S] using vm
  have sc : s∈Shore C := by simp [S]
  have as' : G.Adj a s := us ▸ au
  have bs' : G.Adj b s := vs ▸ bv
  obtain ⟨a3,b3,high⟩ := adjacent_singleton_terminal_count ab degree CD cover one
  have oneTwo (positive : 0<(classSet D 0).card) (small : (classSet D 1).card≤4)
      (oa : (classSet D 3).card=1) (ob : (classSet D 4).card=2) (oc : (classSet D 5).card=2) :
      Nonempty (MultiFrame G a b D) := by
    have common := all_common_of_adjacent_singleton_profile_two hc ab a3 oa oc
    have right := singleton_multi_all_b_odd_literal hc ab positive small zero oa ob high common
    have left : ∀ w∈classSet D 3,G.Adj a w := by
      have sub : ((Shore D).filter (G.Adj a))⊆classSet D 3 ∪ classSet D 5 := by
        intro w wm
        obtain ⟨wd,aw⟩ := mem_filter.mp wm
        have wb : w≠b := fun e=>(shore_off D).2 (e ▸ wd)
        rcases key_a_port hc ab wb aw with k|k
        · exact mem_union_left _ (mem_filter.mpr ⟨wd,k⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨wd,k⟩)
      have sz := card_union_le (classSet D 3) (classSet D 5)
      rw [oa,oc] at sz
      have eq := eq_of_subset_of_card_le sub (sz.trans a3)
      intro w wm
      have l : w∈((Shore D).filter (G.Adj a)) := eq ▸ mem_union_left (classSet D 5) wm
      exact (mem_filter.mp l).2
    have cohorts := singleton_even_cohort_ports hc ab left right
    exact ⟨⟨zero,left,right,common,cohorts.1,cohorts.2,high⟩⟩
  rcases profiles with ⟨ea,eb,oa,ob,oc⟩|⟨ea,eb,oa,ob,oc⟩|⟨ea,eb,oa,ob,oc⟩
  · obtain ⟨F⟩ := oneTwo (by omega) (by omega) oa ob oc
    exact impossible_singleton_multi_two_four_two_frame F hc ab even CD sc as' bs' ea eb oa ob oc
  · obtain ⟨F⟩ := oneTwo (by omega) (by omega) oa ob oc
    exact impossible_singleton_multi_three_three_two_frame F hc ab even CD sc as' bs' ea eb oa ob oc
  · have known := literal_port_classes_from_terminal_three hc ab a3 oa oc
    have bs3 : 3≤((Shore (swapCut D)).filter (G.Adj b)).card := by rw [shore_swapCut D]; exact b3
    have ob' : (classSet (swapCut D) 3).card=2 := by rw [classSet_swap]; exact ob
    have oc' : (classSet (swapCut D) 5).card=1 := by rw [classSet_swap]; exact oc
    have kn := literal_port_classes_from_terminal_three hc ab.symm bs3 ob' oc'
    have right : ∀ w∈classSet D 4,G.Adj b w := by
      intro w wm
      apply kn.1
      rw [classSet_swap]
      exact wm
    have cohorts := singleton_even_cohort_ports hc ab known.1 right
    let F : MultiFrame G a b D := ⟨zero,known.1,right,known.2,cohorts.1,cohorts.2,high⟩
    exact impossible_singleton_multi_three_three_one_frame F hc ab even CD sc as' bs' ea eb oa ob oc

#print axioms impossible_actual_adjacent_singleton_multi_empty_even_fourteen
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
