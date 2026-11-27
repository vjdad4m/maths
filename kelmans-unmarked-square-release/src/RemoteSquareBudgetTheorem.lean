import RemoteSquareStripAuto
import RemoteSquareBudgetColoring

namespace KelmansCactus.AtomicBridge.RemoteSquareBudgetTheorem
open SimpleGraph
open RemoteRankUnion (Marking)
open RemoteBudgetComponent (Mate cost)
open RemoteSquareBudgetConditional (Square)
open RemoteSquareBudgetFractional (UniformMatchingDistribution from_fractional)
open RemoteSquareBudgetColoring (TriplePartition uniform_of_three)
variable {V I ι : Type*} {G : SimpleGraph V} [Fintype V] [Fintype I]

/-- Local width-four release from a genuine uniform matching representation.
All exterior path strips and rational expectations are derived, rather than
included as independent assumptions. Only existence of the supplied uniform
representation is not a graph theorem inside this Lean module. -/
theorem unmarked_square_release [Fintype ι] (M : Marking G I) (six : Fintype.card I=6)
    (p : Mate G) (A : Square p)
    (min : ∀ q,cost M p≤cost M q) (atMostOne : cost M p≤1)
    (unmarked : ∀ i t,M.a i≠A.corner t) (noDiagonal : A.NoDiagonal)
    (representation : UniformMatchingDistribution G ι) :
    ∃ q : Mate G,A.lost q=2 ∧ cost M q≤1 :=
  from_fractional M six p A min atMostOne unmarked noDiagonal representation
    (fun j=>RemoteSquareStripAuto.automatic A (representation.target j))

/-- An actual partition into three perfect matchings supplies the uniform
representation without any matching-polytope premise. -/
theorem unmarked_square_release_three (M : Marking G I) (six : Fintype.card I=6)
    (p : Mate G) (A : Square p)
    (min : ∀ q,cost M p≤cost M q) (atMostOne : cost M p≤1)
    (unmarked : ∀ i t,M.a i≠A.corner t) (noDiagonal : A.NoDiagonal)
    (colors : Fin 3→Mate G) (partition : TriplePartition colors) :
    ∃ q : Mate G,A.lost q=2 ∧ cost M q≤1 :=
  unmarked_square_release M six p A min atMostOne unmarked noDiagonal
    (uniform_of_three colors partition)

#print axioms unmarked_square_release
#print axioms unmarked_square_release_three
end KelmansCactus.AtomicBridge.RemoteSquareBudgetTheorem
