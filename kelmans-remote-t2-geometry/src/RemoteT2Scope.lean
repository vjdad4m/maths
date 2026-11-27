import SquareCapFactor
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2Scope
open SquareCap (FactorOn SmallTrivial omitEdge)
noncomputable section
universe u

def Remote {V : Type*} (G : SimpleGraph V) (x a b : V) : Prop :=
  a≠x ∧ b≠x ∧ ¬G.Adj x a ∧ ¬G.Adj x b

def DisjointEdges {V : Type*} (x y a b : V) : Prop :=
  a≠x ∧ b≠x ∧ a≠y ∧ b≠y

/-- For two actual disjoint edges xy and ab, this is precisely the
condition that they are opposite edges in at least one four-cycle. -/
def OppositeSquare {V : Type*} (G : SimpleGraph V) (x y a b : V) : Prop :=
  (G.Adj x a∧G.Adj y b) ∨ (G.Adj x b∧G.Adj y a)

theorem either_remote_iff_not_opposite_square {V : Type*} {G : SimpleGraph V}
    {x y a b : V} (disj : DisjointEdges x y a b)
    (common : ∀ z, ¬(G.Adj x z∧G.Adj y z)) :
    Remote G x a b ∨ Remote G y a b ↔ ¬OppositeSquare G x y a b := by
  classical
  constructor
  · rintro (r|r) (⟨xa,yb⟩|⟨xb,ya⟩)
    · exact r.2.2.1 xa
    · exact r.2.2.2 xb
    · exact r.2.2.2 yb
    · exact r.2.2.1 ya
  · intro safe
    by_contra! r
    have hx : G.Adj x a∨G.Adj x b := by
      by_contra! e
      exact r.1 ⟨disj.1,disj.2.1,e.1,e.2⟩
    have hy : G.Adj y a∨G.Adj y b := by
      by_contra! e
      exact r.2 ⟨disj.2.2.1,disj.2.2.2,e.1,e.2⟩
    rcases hx with xa|xb <;> rcases hy with ya|yb
    · exact common a ⟨xa,ya⟩
    · exact safe (Or.inl ⟨xa,yb⟩)
    · exact safe (Or.inr ⟨xb,ya⟩)
    · exact common b ⟨xb,yb⟩

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem cyclic_four_pair_no_common {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (big : 5≤Fintype.card V)
    (cub : ∀ z,G.degree z=3) {x y : V} (xy : G.Adj x y) :
    ∀ z,¬(G.Adj x z ∧ G.Adj y z) := by
  rintro z ⟨xz,yz⟩
  exact TwinObstruction.no_triangle small big xy yz xz.symm
    (cub x).le (cub y).le (cub z).le

/-- In passing from a directed quantification to undirected deleted
edges, the exact exception is adjacency opposite a four-cycle.
This is a restatement, not proof of existence of the factors. -/
theorem directed_remote_iff_nonsquare {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ z,G.degree z=3) :
    (∀ x y a b : V,G.Adj x y→G.Adj a b→DisjointEdges x y a b→Remote G x a b→
      FactorOn (omitEdge G a b) ((univ.erase x).erase y)) ↔
    (∀ x y a b : V,G.Adj x y→G.Adj a b→DisjointEdges x y a b→¬OppositeSquare G x y a b→
      FactorOn (omitEdge G a b) ((univ.erase x).erase y)) := by
  constructor
  · intro h x y a b xy ab disj no
    have law := either_remote_iff_not_opposite_square disj
      (cyclic_four_pair_no_common small big cub xy)
    rcases law.mpr no with dx|dy
    · exact h x y a b xy ab disj dx
    · have flip : DisjointEdges y x a b := ⟨disj.2.2.1,disj.2.2.2,disj.1,disj.2.1⟩
      have fact := h y x a b xy.symm ab flip dy
      have e : (univ.erase y).erase x=(univ.erase x).erase y := by
        ext z
        simp [and_comm]
      rwa [e] at fact
  · intro h x y a b xy ab disj r
    exact h x y a b xy ab disj
      ((either_remote_iff_not_opposite_square disj
        (cyclic_four_pair_no_common small big cub xy)).mp (Or.inl r))

#print axioms either_remote_iff_not_opposite_square
#print axioms directed_remote_iff_nonsquare
end
end KelmansCactus.AtomicBridge.RemoteT2Scope
