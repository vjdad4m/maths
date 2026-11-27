import DegreeFiveSingletonFour189
import DegreeFiveUnbalancedClose189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private count_cut_a from DegreeFiveBridgeSize189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem exact_five_when_foreign_four (hc : G.Connected)
    (dist : G.dist a b=3) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5) (p4 : S.foreignA.card=4) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let T := switch S rightConnected rightA rightB
  have far : 3≤G.dist a b := by omega
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have ca := count_cut_a S far
  have cb := count_cut_a S.flip far'
  change G.degree b=(S.L.filter (G.Adj b)).card+(S.R.filter (G.Adj b)).card at cb
  have p1 : S.localA.card=1 := by omega
  by_cases bf : (S.L.filter (G.Adj b)).card=4
  · exact traceable_of_balanced_cut_degree_five S hc dist even degree rightConnected rightA rightB a5 b5 (by omega)
  have bcap := foreign_a_ports_le_four T.flip hc far' even
  change (S.L.filter (G.Adj b)).card≤4 at bcap
  obtain ⟨L5,B3,highR,RS⟩ := singleton_mixed_shore_size S hc far even degree
    rightConnected rightA rightB p1 p4 (by omega) (by omega)
  exact traceable_of_small_sides T far degree (by change S.R.card≤7; omega)
    (by change S.L.card≤8; omega) highR S.leftConnected S.leftA S.leftB

/-- The degree-five even-distance condition implies traceability whenever
a distance-three separating pair has both endpoint degrees exactly five.
There is no component-size or port-count restriction. -/
theorem traceable_of_exact_five_distance_three_cut (hc : G.Connected)
    (dist : G.dist a b=3) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let T := switch S rightConnected rightA rightB
  have far : 3≤G.dist a b := by omega
  have dist' : G.dist b a=3 := by rwa [SimpleGraph.dist_comm]
  have far' : 3≤G.dist b a := by omega
  have aR := foreign_a_ports_le_four S hc far even
  have aL := foreign_a_ports_le_four T hc far even
  have bR := foreign_a_ports_le_four S.flip hc far' even
  have bL := foreign_a_ports_le_four T.flip hc far' even
  change S.localA.card≤4 at aL
  change (S.R.filter (G.Adj b)).card≤4 at bR
  change (S.L.filter (G.Adj b)).card≤4 at bL
  by_cases pa : S.foreignA.card=4
  · exact exact_five_when_foreign_four S hc dist even degree rightConnected rightA rightB a5 b5 pa
  by_cases qa : S.localA.card=4
  · exact exact_five_when_foreign_four T hc dist even degree S.leftConnected S.leftA S.leftB a5 b5 qa
  by_cases pb : (S.R.filter (G.Adj b)).card=4
  · exact exact_five_when_foreign_four S.flip hc dist' even degree rightConnected rightB rightA b5 a5 pb
  by_cases qb : (S.L.filter (G.Adj b)).card=4
  · exact exact_five_when_foreign_four T.flip hc dist' even degree S.leftConnected S.leftB S.leftA b5 a5 qb
  exact traceable_of_exact_five_cut_degrees_without_four_porters S hc dist even degree conn rightConnected
    rightA rightB a5 b5 (by omega) (by omega) (by omega) (by omega)

#print axioms traceable_of_exact_five_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.Split.Five
