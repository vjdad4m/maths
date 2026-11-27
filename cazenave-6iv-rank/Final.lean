import Assembly
import Conventional
import PrincipalRank
import RankTwo
import TwinConnected

namespace CazenaveRank
set_option autoImplicit false

/-- The exact remaining deletion lemma to instantiate (if the imported matrix
    files are present, all other steps of this assembly are formal). -/
def LeafRandicDecrease : Prop :=
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (u v a : V), G.Connected → u ≠ v → G.Adj a u → G.Adj a v →
      G.degree u = 1 → G.degree v = 1 →
      randicRows (G.induce {i | i ≠ u}) < randicRows G

noncomputable def realAdjacencyInterface (hdec : LeafRandicDecrease) : RankInterface where
  rank := by
    intro V _ _ G _
    exact columnRank (G.adjMatrix ℝ)
  witness := by
    intro V _ _ G _
    obtain ⟨I,fi,e,π,hinj,hi,hadj⟩ := rank_neighbor_permutation G
    exact ⟨I,fi,⟨e,hinj⟩,π,hi,hadj⟩
  delete := by
    intro V _ _ G _ u v a hc hne hau hav hdu hdv
    have ht := same_neighbour_of_leaf_twins G hau hav hdu hdv
    have hd := hdec G u v a hc hne hau hav hdu hdv
    exact ⟨connected_remove_twins G hc hne.symm ht,
      rank_remove_twins G hne.symm ht, hd⟩

/-- Cazenave 6(iv), rank inequality; hdec is an explicit unresolved proof input
    until the monotone twin-leaf deletion theorem is imported. -/
theorem rank_bound_assembly (hdec : LeafRandicDecrease)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) ≤ randic G :=
  (realAdjacencyInterface hdec).close (Fintype.card V) V G rfl hn hc

open scoped BigOperators

/-- Identical statement in the usual unordered-edge normalization. -/
theorem rank_bound_assembly_unordered (hdec : LeafRandicDecrease)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) ≤
      ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
  rw [← randic_eq_unordered]
  exact rank_bound_assembly hdec G hn hc

/-- The order ≥3 case without duplicate leaves, requiring no deletion input. -/
theorem rank_bound_distinct_leaf_supports
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V)
    (ht : ∀ v a b, G.Adj v a → G.Adj v b →
      G.degree a = 1 → G.degree b = 1 → a = b) :
    1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) <
      ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
  obtain ⟨I,fi,e,π,hinj,hi,hadj⟩ := rank_neighbor_permutation G
  letI := fi
  rw [← randic_eq_unordered, ← hi]
  exact reduced_from_permutation G ⟨e,hinj⟩ π hc hn hadj ht

/-- The assembled proof's equality claim, with the same explicit deletion input. -/
theorem rank_equality_assembly (hdec : LeafRandicDecrease)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    randic G = 1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) ↔
      Fintype.card V = 2 := by
  constructor
  · intro he
    by_contra! h
    have h3 : 3 ≤ Fintype.card V := by omega
    have hh := (realAdjacencyInterface hdec).close_strict G h3 hc
    change 1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) < randic G at hh
    rw [he] at hh
    exact (lt_irrefl _) hh
  · intro he
    rw [randic_order_two G hc he,rank_order_two G hc he]; norm_num

#print axioms rank_bound_distinct_leaf_supports
#print axioms rank_bound_assembly
#print axioms rank_equality_assembly
end CazenaveRank
