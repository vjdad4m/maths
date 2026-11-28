import SixDistanceThreeEighteen189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private route_at_ordered_shores from SixDistanceThreeShort189
open private join_shore_to_middle route_middle_ten from SixDistanceThreeEighteen189
set_option linter.unusedSectionVars false

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

/-- At threshold six, a distance-three separator whose two shores have
at most ten vertices each always admits a spanning path, including
the 10+10 case not covered by the order-eighteen theorem. -/
theorem traceable_at_distance_three_two_shores_le_ten
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c10 : (Shore C).card≤10) (d10 : (Shore D).card≤10) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have oriented (J K : Cmp G a b) (ne : J≠K)
      (cov : ∀ {z : V},z≠a → z≠b → z∈Shore J ∨ z∈Shore K)
      (j10 : (Shore J).card≤10) (k10 : (Shore K).card≤10)
      (high : ∀ z∈Shore K,6≤G.degree z) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    by_cases small : (Shore K).card≤9
    · exact route_at_ordered_shores far ab conn degree ne cov j10 small high
    · have ten : (Shore K).card=10 := by omega
      obtain ⟨x,y,ax,by',path⟩ := route_middle_ten hc far ab conn even degree ne ten high
      exact join_shore_to_middle far ab conn degree ne cov j10 ax by' path
  by_cases high : ∀ z∈Shore D,6≤G.degree z
  · exact oriented C D cd cover c10 d10 high
  · push_neg at high
    obtain ⟨z,zd,dz⟩ := high
    have hC : ∀ w∈Shore C,6≤G.degree w := by
      intro w wh
      have wz : w≠z := fun e=>disjoint_left.mp (shore_disjoint cd) wh (e.symm ▸ zd)
      exact (degree w z wz).resolve_right (Nat.not_le_of_lt dz)
    exact oriented D C cd.symm (fun za zb => (cover za zb).symm) d10 c10 hC

#print axioms traceable_at_distance_three_two_shores_le_ten
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
