import BoundedCenters180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At deficit at most three with unequal marks, enumerating no center,
one center, and pairs of centers is exact for all distance-preserving
spanning trees. -/
theorem rank_three_breadth_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t,G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) (rk : Fintype.card V≤bipartiteNum G+3) :
    let P := parity G r odd
    let X := A∪P
    let D := X\(A∩P)
    A≠P → ((∃ T≤G,T.IsTree ∧ (∀ x,T.dist x r=G.dist x r) ∧
      1+A.card+P.card≤(eligible A P r∩leaves T).card+bipartiteNum G) ↔
    ∃ B⊆X.erase r,B.card≤2 ∧ Fintype.card V+B.card≤bipartiteNum G+
      baseScore G r D X+(children G r D B).card) := by
  classical
  intro P X D different
  have nz : D.Nonempty := by
    by_contra! no
    apply different
    ext v
    have z : v∉D := fun m => no ⟨v,m⟩
    simp only [D,X,mem_sdiff,mem_union,mem_inter] at z
    tauto
  have pos := base_pos G hc r D X nz
  refine (breadth_iff G hc hn r two odd A ai).trans ?_
  constructor
  · intro test
    obtain ⟨B,inc,lim,pay⟩ := (small_layer_iff G r A P).mp test
    change B.card≤Fintype.card V-(bipartiteNum G+baseScore G r D X) at lim
    exact ⟨B,inc,by omega,pay⟩
  · rintro ⟨B,inc,_,pay⟩
    refine ⟨B,inc,?_⟩
    change Fintype.card V+B.card≤bipartiteNum G+(if r∈D then 1 else 0)+
      (if r∈X then G.degree r-2 else 0)+score G r D B
    rw [score_formula]
    unfold baseScore at pay
    omega

#print axioms rank_three_breadth_iff
end Minimal180.HigherRank
