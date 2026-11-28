import DegreeFiveSixThreeThreeDispatch189
import DegreeFiveSixThreeInnerThreeB189
import DegreeFiveBothThreeBridges189
import DegreeFiveNonadjacentCut189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.CrossSaturation.Split.Five
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_at_actual_five_distance_three_cut_degree_six {a b : V}
    (hc : G.Connected) (three : G.dist a b = 3)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V, R.card < 2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    (cut : ¬(G.induce {z : V | z ≠ a ∧ z ≠ b}).Connected)
    (a6 : G.degree a = 6) :
    ∃ r t, ∃ p : G.Walk r t, p.IsPath ∧ ∀ z, z ∈ p.support := by
  have far : 3 ≤ G.dist a b := by omega
  apply traceable_actual_six_of_both_three hc three even conn degree cut a6
  intro S high l3 r3 lc bc rc ra rb
  apply exact_three_three_of_two_remaining S hc three even conn degree high l3 r3 lc bc rc ra rb
  · exact traceable_of_both_three_bridges S hc far even conn degree l3 r3 lc bc rc ra rb
  intro U uR uA uB ul ur _ br nb i3 b3
  exact three_inner_nonbridge_three_b U hc far even conn degree ul ur b3 i3 br uR uA uB nb

theorem traceable_at_actual_five_distance_three_cut {a b : V}
    (hc : G.Connected) (far : 3 ≤ G.dist a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V, R.card < 2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    (cut : ¬(G.induce {z : V | z ≠ a ∧ z ≠ b}).Connected) :
    ∃ r t, ∃ p : G.Walk r t, p.IsPath ∧ ∀ z, z ∈ p.support :=
  traceable_at_actual_five_far_cut_of_degree_six
    (fun {a b} => traceable_at_actual_five_distance_three_cut_degree_six (a:=a) (b:=b))
    hc far even conn degree cut

theorem traceable_at_actual_five_nonadjacent_cut {a b : V}
    (hc : G.Connected) (ne : a ≠ b) (nonedge : ¬G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V, R.card < 2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    (cut : ¬(G.induce {z : V | z ≠ a ∧ z ≠ b}).Connected) :
    ∃ r t, ∃ p : G.Walk r t, p.IsPath ∧ ∀ z, z ∈ p.support :=
  traceable_at_actual_five_nonadjacent_cut_of_degree_six
    (fun {a b} => traceable_at_actual_five_distance_three_cut_degree_six (a:=a) (b:=b))
    hc ne nonedge even conn degree cut

#print axioms traceable_at_actual_five_distance_three_cut_degree_six
#print axioms traceable_at_actual_five_distance_three_cut
#print axioms traceable_at_actual_five_nonadjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
