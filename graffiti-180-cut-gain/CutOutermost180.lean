import CutExit180

set_option warningAsError true
namespace Minimal180.CutGain.TightCut
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A limit on the depth of horizontal edges gives an unconditional
positive class: in particular every outermost horizontal cut triangle
at lower deficit one gains an eligible leaf. Only deeper horizontal
edges with no common predecessor have to be excluded. -/
theorem gain_of_deeper_predecessors {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let U := eligible A (parity G r.val odd) r.val
    (∀ q z,J.Adj q z → G.dist x r.val<G.dist q r.val → G.dist q r.val=G.dist z r.val →
      ∃ p,G.Adj q p ∧ G.Adj z p ∧ G.dist q r.val=G.dist p r.val+1) →
    weightedLeaves J U<weightedLeaves G U := by
  intro G U pred
  apply Classical.byContradiction
  intro ng
  obtain ⟨q,z,_,_,_,e,deep,flat,_,no⟩ := h.deeper_chord rank1 ng
  exact no (pred q z e deep flat)

/-- A maximum-depth horizontal chord in the original cut-triangle
branch always gains, with arbitrary eligible-leaf optimization. -/
theorem outermost_gain {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let U := eligible A (parity G r.val odd) r.val
    (∀ q z,J.Adj q z → G.dist q r.val=G.dist z r.val → G.dist q r.val≤G.dist x r.val) →
    weightedLeaves J U<weightedLeaves G U := by
  intro G U bound
  apply h.gain_of_deeper_predecessors rank1
  intro q z e deep flat
  exact (not_lt_of_ge (bound q z e flat) deep).elim

#print axioms gain_of_deeper_predecessors
#print axioms outermost_gain
end Minimal180.CutGain.TightCut
