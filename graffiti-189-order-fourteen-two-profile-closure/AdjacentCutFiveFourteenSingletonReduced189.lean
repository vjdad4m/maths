import AdjacentCutFiveFourteenSingletonFrontier189
import AdjacentCutFiveFourteenEC1Exact189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore from AdjacentCutFiveActual189
open private prof from AdjacentCutFiveTopProfiles189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

namespace AdjProfile
def Singleton14AfterEC1 (a b c p q r : Nat) : Prop :=
     (a=2 ∧ b=2 ∧ c=2 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=2 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=2 ∧ q=2 ∧ r=1)

private theorem close_shape {a b c p q r : Nat}
    (h : Singleton14Frontier a b c p q r) :
    Singleton14AfterEC1 a b c p q r ∨
    (2≤a ∧ 2≤b ∧ 5≤a+b ∧ c=1 ∧ p=1 ∧ q=1 ∧ r≤3) := by
  unfold Singleton14Frontier at h
  unfold Singleton14AfterEC1
  rcases h with h|h|h|h|h|h|h <;>
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := h <;> decide
end AdjProfile

theorem narrowed_frontier_of_adjacent_singleton_eleven_counterexample
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) (big : (Shore D).card=11)
    (fail : ¬∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support) :
    (let y := prof D
     AdjProfile.Singleton14AfterEC1 y.ea y.eb y.ec y.oa y.ob y.oc ∨
     AdjProfile.Singleton14AfterEC1 y.eb y.ea y.ec y.ob y.oa y.oc) := by
  rcases frontier_of_adjacent_singleton_eleven_counterexample hc ab even conn degree cd cover one big fail with h|h
  · rcases AdjProfile.close_shape h with r|⟨a2,b2,f,e,p,q,o⟩
    · exact .inl r
    exact (fail (traceable_of_adjacent_singleton_eleven_equal_one_unique hc ab even conn degree cd cover one big
      a2 b2 f e p q o)).elim
  rcases AdjProfile.close_shape h with r|⟨b2,a2,f,e,q,p,o⟩
  · exact .inr r
  exact (fail (traceable_of_adjacent_singleton_eleven_equal_one_unique hc ab even conn degree cd cover one big
    a2 b2 (by omega) e p q o)).elim

#print axioms narrowed_frontier_of_adjacent_singleton_eleven_counterexample
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
