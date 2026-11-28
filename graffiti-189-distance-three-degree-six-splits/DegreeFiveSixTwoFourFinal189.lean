import DegreeFiveSixTwoInnerClose189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

theorem traceable_six_two_four (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (l2 : S.localA.card=2) (r4 : S.foreignA.card=4)
    (rc : (G.induce (↑S.R : Set V)).Connected)
    (ra : ∃ x∈S.R,G.Adj a x) (rb : ∃ x∈S.R,G.Adj b x) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_cases easy : S.R.card≤8 ∨ ¬portBridge S
  · exact traceable_six_two_four_small_or_no_bridge S hc far even conn degree l2 r4 rc ra rb easy
  have br : portBridge S := Classical.byContradiction (fun h=>easy (.inr h))
  have large : 8<S.R.card := by omega
  have term := bridge_route_at_two_four S hc far even degree l2 r4 rc ra rb br
  obtain ⟨showI,profiles⟩ := large_opposite_profiles_at_two_four S hc far even degree l2 r4 rc ra rb br large
  let T := switch S rc ra rb
  have free : (∃ u v,G.Adj a u ∧ RouteOn G S.R u v) ∨
      (∃ u v,G.Adj b u ∧ RouteOn G S.R u v) := by
    rcases profiles with ⟨i1,b4⟩|⟨nb,i2,b3,b4⟩
    · left
      by_cases rt : portBridge T
      · have limit := (bridge_two_opposite_shell_cap S hc far even degree l2 r4 br).2
        have vis : (visibleBPorts T.L a b G).card≤1 := by
          change (visibleBPorts S.R a b G).card≤1
          omega
        exact four_a_bridge_one_inner_free_foreign_two T hc far even degree r4 b4 i1 vis l2 showI rt
      exact no_bridge_one_inner_free T far degree r4 b4 i1 rt
    exact four_a_no_bridge_two_inner_free T hc far even degree r4 b3 b4 i2 l2 nb showI
  exact traceable_from_far_terminal_and_free S far term free

#print axioms traceable_six_two_four
end Graffiti189LongestPath.CrossSaturation.Split.Five
