import SingletonSide189
import NontrivialSides189
import ThreeCutLift189
namespace Graffiti189LongestPath.FourCut.Three
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 1700000

theorem component_card_le_two_of_no_singleton_side (hc : G.Connected) (a b : V) (ab : a≠b)
    (d2 : ∀ x, (DistanceTwo G x).card≤4) (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del : ∀ b : V, (G.induce {x : V | x≠b}).Connected)
    (exclude : ∀ (S : Sides G a b) r, S.H 0={r} → False) :
    Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent ≤ 2 := by
  classical
  by_contra! n
  obtain ⟨S⟩ := exists_sides hc a b ab d2 even degree del n
  by_cases yes : ∃ i : Fin 3, (S.H i).card=1
  · obtain ⟨i,hi⟩ := yes
    obtain ⟨r,hr⟩ := card_eq_one.mp hi
    have eq : (S.reorder (Equiv.swap 0 i)).H 0={r} := by simpa [Sides.reorder] using hr
    exact exclude _ r eq
  apply S.no_three_nonsingleton
  intro i
  obtain ⟨x,xi,_⟩ := S.hita i
  have pos := card_pos.mpr (show (S.H i).Nonempty from ⟨x,xi⟩)
  have none : (S.H i).card≠1 := fun h => yes ⟨i,h⟩
  have two := S.size_not_two i
  omega

#print axioms component_card_le_two_of_no_singleton_side

/-- Any two-vertex deletion in the 2-connected degree-four case of #189
leaves at most two connected components. -/
theorem component_card_le_two (hc : G.Connected) (a b : V) (ab : a≠b)
    (d2 : ∀ x, (DistanceTwo G x).card≤4) (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del : ∀ b : V, (G.induce {x : V | x≠b}).Connected) :
    Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent ≤ 2 :=
  component_card_le_two_of_no_singleton_side hc a b ab d2 even degree del
    (fun S _ eq => S.no_singleton_at_zero_189 eq)

#print axioms component_card_le_two
end Graffiti189LongestPath.FourCut.Three
