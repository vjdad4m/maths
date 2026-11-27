import FourSideCase22
import FourSideCase32
import FourSideCase33
import SmallDistThree189
namespace Graffiti189LongestPath.TwoCut.FourSideCtx
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

/-- If a distance-three two-cut leaves a four-vertex component, the other
component has at most six vertices. -/
theorem other_order_le_six : C.H.card≤6 := by
  by_contra! bad
  have large : 7≤C.H.card := by omega
  have ca := C.Acap
  have cb := C.swap.Acap
  change C.B.card≤3 at cb
  have a2 := C.large_no_single large
  have b2 := C.swap.large_no_single large
  change 2≤C.B.card at b2
  have shapes : (C.A.card=2 ∧ C.B.card=2) ∨ (C.A.card=3 ∧ C.B.card=2) ∨
      (C.A.card=2 ∧ C.B.card=3) ∨ (C.A.card=3 ∧ C.B.card=3) := by omega
  rcases shapes with ⟨pa,pb⟩|⟨pa,pb⟩|⟨pa,pb⟩|⟨pa,pb⟩
  · exact C.contra_22 large pa pb
  · exact C.contra_32 large pa pb
  · exact C.swap.contra_32 large pb pa
  · exact C.contra_33 large pa pb

include C in
/-- The degree-four case of Graffiti.pc #189 holds whenever a distance-three
two-cut leaves a component of order four. -/
theorem traceable_of_four_side :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ z,z∈p.support :=
  S.traceable_four_six C.far C.min2 (show C.i≠ !C.i by cases C.i <;> decide)
    C.size C.other_order_le_six

#print axioms other_order_le_six
#print axioms traceable_of_four_side
end Graffiti189LongestPath.TwoCut.FourSideCtx
