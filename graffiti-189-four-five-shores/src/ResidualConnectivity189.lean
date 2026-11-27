import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- If a finite graph has no isolates and at most one vertex below
degree d, each component has order at least d+1. -/
theorem connected_of_pair_degree_and_no_isolates (d : ℕ)
    (nonempty : Nonempty V) (size : Fintype.card V≤2*d+1)
    (pair : ∀ u v,u≠v → d≤J.degree u ∨ d≤J.degree v)
    (hit : ∀ u,∃ v,J.Adj u v) :
    J.Connected := by
  classical
  letI : Nonempty V := nonempty
  have big (u : V) : d+1≤((univ : Finset V).filter (J.Reachable u)).card := by
    let S := (univ : Finset V).filter (J.Reachable u)
    obtain ⟨v,uv⟩ := hit u
    have hi : ∃ w∈S,d≤J.degree w := by
      rcases pair u v uv.ne with h|h
      · exact ⟨u,mem_filter.mpr ⟨mem_univ _,SimpleGraph.Reachable.refl _⟩,h⟩
      exact ⟨v,mem_filter.mpr ⟨mem_univ _,uv.reachable⟩,h⟩
    obtain ⟨w,ws,h⟩ := hi
    have reach := (mem_filter.mp ws).2
    have sub : insert w (J.neighborFinset w)⊆S := by
      intro t tm
      rcases mem_insert.mp tm with rfl|tm
      · exact ws
      have wt := (mem_neighborFinset J _ _).mp tm
      exact mem_filter.mpr ⟨mem_univ _,reach.trans wt.reachable⟩
    have no : w∉J.neighborFinset w := fun h=>J.loopless _ ((mem_neighborFinset J _ _).mp h)
    have c := card_le_card sub
    rw [card_insert_of_not_mem no,card_neighborFinset_eq_degree] at c
    exact (Nat.add_le_add_right h 1).trans c
  have pre : J.Preconnected := by
    intro u v
    apply Classical.byContradiction
    intro no
    let A := (univ : Finset V).filter (J.Reachable u)
    let B := (univ : Finset V).filter (J.Reachable v)
    have dis : Disjoint A B := by
      apply disjoint_left.mpr
      intro w wa wb
      exact no ((mem_filter.mp wa).2.trans (mem_filter.mp wb).2.symm)
    have cnt := card_le_card (subset_univ (A∪B))
    rw [card_union_of_disjoint dis,card_univ] at cnt
    have a : d+1≤A.card := big u
    have b : d+1≤B.card := big v
    omega
  exact ⟨pre⟩

#print axioms connected_of_pair_degree_and_no_isolates
end Graffiti189LongestPath.CrossSaturation
