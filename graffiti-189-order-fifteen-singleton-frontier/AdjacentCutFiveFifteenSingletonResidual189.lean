import AdjacentCutFiveFifteenSingletonMixedMap189
import AdjacentCutFiveMixedNineGeom189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore from AdjacentCutFiveActual189
open private key classSet prof from AdjacentCutFiveTopProfiles189
open private compact_graph_singleton_fifteen_profile from AdjacentCutFiveFifteenSingletonProfiles189
open private swapCut from AdjacentCutFiveMixedNineGeom189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private def swapIndex (i : Fin 6) : Fin 6 :=
  if i=0 then 1 else if i=1 then 0 else if i=3 then 4 else if i=4 then 3 else i

private theorem swapIndex_involutive (i : Fin 6) : swapIndex (swapIndex i)=i := by
  fin_cases i <;> decide

private theorem key_swap_index (w : V) : key G b a w=swapIndex (key G a b w) := by
  classical
  by_cases e : G.dist a w<G.dist b w
  · by_cases z : Even (G.dist a w) <;> simp [key,e,not_lt_of_ge e.le,z,swapIndex]
  · by_cases d : G.dist b w<G.dist a w
    · by_cases z : Even (G.dist b w) <;> simp [key,e,d,z,swapIndex]
    · have eq : G.dist a w=G.dist b w := by omega
      by_cases z : Even (G.dist b w) <;> simp [key,e,d,z,eq,swapIndex]

private theorem classSet_swap (D : Cmp G a b) (i : Fin 6) :
    classSet (swapCut D) i=classSet D (swapIndex i) := by
  ext w
  simp only [classSet,mem_filter,shore_swapCut]
  rw [key_swap_index (G:=G) (a:=a) (b:=b) w]
  constructor
  · rintro ⟨m,q⟩
    exact ⟨m,(swapIndex_involutive _).symm.trans (congrArg swapIndex q)⟩
  · rintro ⟨m,q⟩
    exact ⟨m,(congrArg swapIndex q).trans (swapIndex_involutive _)⟩

/-- An adjacent singleton + twelve cut either produces a nonadjacent separator or is balanced (3,3,1,1,1,3). -/
theorem alternate_cut_or_balanced_of_adjacent_singleton_twelve_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) (big : (Shore D).card=12) :
    (∃ x y : V,x≠y ∧ ¬G.Adj x y ∧ ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected) ∨
    ((prof D).ea=3 ∧ (prof D).eb=3 ∧ (prof D).ec=1 ∧ (prof D).oa=1 ∧ (prof D).ob=1 ∧ (prof D).oc=3) := by
  classical
  obtain ⟨s,SC,as',bs',_⟩ := compact_graph_singleton_fifteen_profile hc ab even conn degree cd one big
  have sc : s∈Shore C := by simp [SC]
  rcases alternate_cut_or_three_profiles_of_adjacent_singleton_twelve_shores hc ab even conn degree cd one big with cut|bal|l|r
  · exact .inl cut
  · exact .inr bal
  · obtain ⟨ea,eb,ec,oa,ob,oc⟩ := l
    exact .inl (nonadjacent_separator_of_mixed_singleton_twelve_profile hc ab even degree cd cover sc SC as' bs' ea eb ec oa ob oc)
  · obtain ⟨ea,eb,ec,oa,ob,oc⟩ := r
    have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
    have cv' : ∀ {z : V},z≠b → z≠a → z∈Shore (swapCut C) ∨ z∈Shore (swapCut D) := by
      intro z zb za
      simpa only [shore_swapCut] using cover za zb
    refine .inl (nonadjacent_separator_of_mixed_singleton_twelve_profile hc ab.symm even degree cd' cv' ?_ ?_ bs' as' ?_ ?_ ?_ ?_ ?_ ?_)
    · simpa only [shore_swapCut] using sc
    · simpa only [shore_swapCut] using SC
    · rw [classSet_swap]; exact eb
    · rw [classSet_swap]; exact ea
    · rw [classSet_swap]; exact ec
    · rw [classSet_swap]; exact ob
    · rw [classSet_swap]; exact oa
    · rw [classSet_swap]; exact oc

#print axioms alternate_cut_or_balanced_of_adjacent_singleton_twelve_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
