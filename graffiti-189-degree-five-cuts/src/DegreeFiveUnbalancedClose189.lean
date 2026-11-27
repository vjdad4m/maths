import DegreeFiveSixTerminal189
import DegreeFiveBalancedUniform189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private count_cut_a from DegreeFiveBridgeSize189
open private distance_three_has_bridge from DegreeFiveBalancedUniform189
open private left_can_root_at_one_cut from DegreeFiveSmallSides189
open private order_ge_three_from_dist from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

/-- The unbalanced 4+6 port case at exact degree-five distance-three cut
endpoints. The small shore is rooted at either cut vertex; the other
shore has a verified terminal-to-terminal route. -/
theorem traceable_of_four_six_cut_degree_five (hc : G.Connected)
    (dist : G.dist a b=3) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (a2 : S.localA.card=2) (a3 : S.foreignA.card=3)
    (b2 : (S.L.filter (G.Adj b)).card=2) (b3 : (S.R.filter (G.Adj b)).card=3) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let T := switch S rightConnected rightA rightB
  have far : 3≤G.dist a b := by omega
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have aT := tight_a_second_shells_at_degree_five S hc far even degree rightConnected rightA rightB
    a5 (by omega) (by omega)
  have bT := tight_a_second_shells_at_degree_five S.flip hc far' even degree rightConnected rightB rightA
    b5 (by change (S.L.filter (G.Adj b)).card≤3; omega)
    (by change (S.R.filter (G.Adj b)).card≤3; omega)
  have bridge : portBridge S := by
    rcases distance_three_has_bridge S hc dist rightConnected rightA rightB with h|h
    · exact h
    exact (no_mixed_three_three T hc far degree a3 b3 aT.2.1 bT.2.1 h).elim
  have Lsix := mixed_two_two_le_six S hc far even degree a2 b2 a3 b3 aT.1 bT.1 aT.2.2 bT.2.2 bridge
  have Rnine := (opposite_bridge_shore_le_nine_exact_cut_degree S hc far even degree rightConnected
    rightA rightB a5 b5 (by omega) (by omega) (by omega) (by omega) bridge).1
  have minimum := Graffiti189LongestPath.TwoCut.min_two_from_connectivity conn (order_ge_three_from_dist hc far)
  have r := six_port_shore_has_terminal_route T hc far degree minimum a3 b3 aT.2.1 bT.2.1 Rnine
  change RouteOn G (insert a (insert b S.R)) a b at r
  obtain ⟨x,xl,hit,y,q,qp,qs⟩ := left_can_root_at_one_cut S far (by omega) degree
  have l : RouteOn G S.L x y := ⟨q,qp,qs⟩
  let K := insert a (insert b S.R)
  have dis : Disjoint K S.L := by
    apply disjoint_left.mpr
    intro z zk zl
    simp only [K,mem_insert] at zk
    rcases zk with h|h|h
    · exact S.leftOff.1 (h ▸ zl)
    · exact S.leftOff.2 (h ▸ zl)
    exact disjoint_left.mp S.dis zl h
  have finish {v : V} (path : RouteOn G (K∪S.L) v y) :
      ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
    obtain ⟨p,pp,ps⟩ := path
    refine ⟨v,y,p,pp,?_⟩
    intro z
    apply (ps _).mpr
    rcases S.cover z with h|h|h|h
    · exact mem_union_left _ (by simp [K,h])
    · exact mem_union_left _ (by simp [K,h])
    · exact mem_union_right _ h
    exact mem_union_left _ (by simp [K,h])
  rcases hit with ax|bx
  · exact finish (r.reverse.join l dis ax)
  exact finish (r.join l dis bx)

/-- Exact degree-five distance-three cut endpoints imply traceability
whenever no attachment color class has more than three vertices. -/
theorem traceable_of_exact_five_cut_degrees_without_four_porters (hc : G.Connected)
    (dist : G.dist a b=3) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (aL : S.localA.card≤3) (aR : S.foreignA.card≤3)
    (bL : (S.L.filter (G.Adj b)).card≤3) (bR : (S.R.filter (G.Adj b)).card≤3) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have far : 3≤G.dist a b := by omega
  have ca := count_cut_a S far
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have cb := count_cut_a S.flip far'
  change G.degree b=(S.L.filter (G.Adj b)).card+(S.R.filter (G.Adj b)).card at cb
  by_cases balanced : S.localA.card+(S.L.filter (G.Adj b)).card=5
  · exact traceable_of_balanced_cut_degree_five S hc dist even degree rightConnected rightA rightB a5 b5 balanced
  by_cases l2 : S.localA.card=2
  · exact traceable_of_four_six_cut_degree_five S hc dist even degree conn rightConnected rightA rightB
      a5 b5 l2 (by omega) (by omega) (by omega)
  exact traceable_of_four_six_cut_degree_five (switch S rightConnected rightA rightB) hc dist even degree
    conn S.leftConnected S.leftA S.leftB a5 b5 (by change S.foreignA.card=2; omega)
    (by change S.localA.card=3; omega)
    (by change (S.R.filter (G.Adj b)).card=2; omega)
    (by change (S.L.filter (G.Adj b)).card=3; omega)

#print axioms traceable_of_four_six_cut_degree_five
#print axioms traceable_of_exact_five_cut_degrees_without_four_porters
end Graffiti189LongestPath.CrossSaturation.Split.Five
