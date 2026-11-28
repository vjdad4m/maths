import DegreeFiveSevenNoBridgeTerminal189
import DegreeFiveSmallFarFree189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_secondA_positive secondA_right_and_left_le_five from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem traceable_from_far_terminal_and_free
    (far : 3≤G.dist a b)
    (term : ∃ p q,G.Adj a p ∧ G.Adj b q ∧ RouteOn G S.L p q)
    (free : (∃ u v,G.Adj a u ∧ RouteOn G S.R u v) ∨
      (∃ u v,G.Adj b u ∧ RouteOn G S.R u v)) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ v,v∈p.support := by
  have ab : a≠b := by intro e; rw [e,dist_self] at far; omega
  have p : WingRealizes G a b S.L .terminal := term
  exact traceable_of_complementary_wings ab S.dis S.leftOff.1 S.leftOff.2
    S.rightOff.1 S.rightOff.2 S.cover (.inl ⟨p,free⟩)

theorem traceable_seven_split_without_bridge_on_three (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (localThree : S.localA.card=3) (foreignFour : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (noBridge : ¬portBridge S) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ v,v∈p.support := by
  have term := no_bridge_terminal_three_four S hc far even conn degree localThree
    foreignFour rightConnected rightA rightB noBridge
  let T := switch S rightConnected rightA rightB
  have cap : S.R.card≤8 := by
    have sub := no_bridge_four_foreign_cover S hc far even foreignFour noBridge
    have n := (card_le_card sub).trans (card_union_le _ _)
    have pos := left_secondA_positive S hc far
    have sum := secondA_right_and_left_le_five S even
    omega
  have t4 : T.localA.card=4 := foreignFour
  have free := free_route_small_far_shore T far degree cap (by omega)
  exact traceable_from_far_terminal_and_free S far term (.inl free)

#print axioms traceable_from_far_terminal_and_free
#print axioms traceable_seven_split_without_bridge_on_three
end Graffiti189LongestPath.CrossSaturation.Split.Five
