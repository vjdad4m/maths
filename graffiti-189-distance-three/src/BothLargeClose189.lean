import BothLargeMixed189
import FourSideClose189
namespace Graffiti189LongestPath.TwoCut.DistThreeCtx
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : DistThreeCtx S)
set_option maxHeartbeats 2700000
set_option linter.unusedSectionVars false

theorem no_both_large (Hlarge : 5≤C.H.card) (Klarge : 5≤C.K.card) : False := by
  have p := C.no_single_large Hlarge Klarge
  have u := C.other.no_single_large Klarge Hlarge
  have q := C.swap.no_single_large Hlarge Klarge
  have w := C.other.swap.no_single_large Klarge Hlarge
  change 2≤C.U.card at u
  change 2≤C.B.card at q
  change 2≤C.W.card at w
  have eA := C.Acap
  have eU := C.Ucap
  have eB := C.swap.Acap
  have eW := C.swap.Ucap
  change C.B.card≤3 at eB
  change C.W.card≤3 at eW
  have a_shape : C.A.card=2 ∨ C.A.card=3 := by omega
  have u_shape : C.U.card=2 ∨ C.U.card=3 := by omega
  have b_shape : C.B.card=2 ∨ C.B.card=3 := by omega
  have w_shape : C.W.card=2 ∨ C.W.card=3 := by omega
  rcases a_shape with pa|pa <;> rcases u_shape with pu|pu <;>
    rcases b_shape with pb|pb <;> rcases w_shape with pw|pw
  · exact C.impossible_22_22 pa pu pb pw Hlarge Klarge
  · exact C.swap.impossible_23_22 pb pw pa pu Hlarge
  · exact C.swap.other.impossible_23_22 pw pb pu pa Klarge
  · exact C.impossible_22_33 pa pu pb pw
  · exact C.impossible_23_22 pa pu pb pw Hlarge
  · exact C.impossible_23_23_same pa pu pb pw Hlarge
  · exact C.impossible_23_23_opposite pa pu pb pw Hlarge Klarge
  · exact C.impossible_23_33 pa pu pb pw Hlarge
  · exact C.other.impossible_23_22 pu pa pw pb Klarge
  · exact C.other.impossible_23_23_opposite pu pa pw pb Klarge Hlarge
  · exact C.other.impossible_23_23_same pu pa pw pb Klarge
  · exact C.other.impossible_23_33 pu pa pw pb Klarge
  · exact C.swap.impossible_22_33 pb pw pa pu
  · exact C.swap.impossible_23_33 pb pw pa pu Hlarge
  · exact C.swap.other.impossible_23_33 pw pb pu pa Klarge
  · exact C.impossible_33_33 pa pu pb pw

#print axioms no_both_large
end Graffiti189LongestPath.TwoCut.DistThreeCtx

namespace Graffiti189LongestPath.TwoCut.CutPair
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} (S : CutPair G a b)
set_option linter.unusedSectionVars false

include S in
/-- The degree-four case of Graffiti.pc #189 when a two-vertex cut consists
of vertices at distance three. -/
theorem traceable_at_dist_three (dist : 3≤G.dist a b)
    (conn : ∀ R : Finset V, R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (min2 : ∀ x, 2≤G.degree x) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ z,z∈p.support := by
  have h0 := S.sides_ge_four dist false
  have h1 := S.sides_ge_four dist true
  let C : DistThreeCtx S := ⟨false,true,(by decide),dist,min2⟩
  by_cases left : (S.H false).card=4
  · let F : FourSideCtx S := ⟨false,left,dist,conn,min2⟩
    exact F.traceable_of_four_side
  by_cases right : (S.H true).card=4
  · let F : FourSideCtx S := ⟨true,right,dist,conn,min2⟩
    exact F.traceable_of_four_side
  exact (C.no_both_large (show 5≤(S.H true).card by omega)
    (show 5≤(S.H false).card by omega)).elim

#print axioms traceable_at_dist_three
end Graffiti189LongestPath.TwoCut.CutPair
