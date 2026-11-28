import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1

-- Credit: @vjdad4m
-- Degree-five order seventeen: decompose by the presence and type of a two-vertex separator.
open SimpleGraph

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1_H2_R1

/-- The graph has no separating pair, hence is 3-connected under the one-vertex
deletion condition. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, G.distEven x ≤ 6) →
    (∀ x y : V, x ≠ y → 5 ≤ G.degree x ∨ 5 ≤ G.degree y) →
    Fintype.card V = 17 →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    (∀ a b : V, a ≠ b → (G.induce {z | z ≠ a ∧ z ≠ b}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Some separating pair consists of nonadjacent vertices. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, G.distEven x ≤ 6) →
    (∀ x y : V, x ≠ y → 5 ≤ G.degree x ∨ 5 ≤ G.degree y) →
    Fintype.card V = 17 →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    (∃ a b : V, a ≠ b ∧ ¬ G.Adj a b ∧
      ¬ (G.induce {z | z ≠ a ∧ z ≠ b}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Some separating pair consists of adjacent vertices. -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, G.distEven x ≤ 6) →
    (∀ x y : V, x ≠ y → 5 ≤ G.degree x ∨ 5 ≤ G.degree y) →
    Fintype.card V = 17 →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    (∃ a b : V, G.Adj a b ∧
      ¬ (G.induce {z | z ≠ a ∧ z ≠ b}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → H3 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H2 := by
  intro noCut nonadjacent adjacent V _ _ _ G _ hc parity _ del upper lower degree
  classical
  have n : Fintype.card V = 17 := by omega
  have cap (x : V) : G.distEven x ≤ 6 := by simpa [degree] using parity x
  have pair (x y : V) (hne : x ≠ y) : 5 ≤ G.degree x ∨ 5 ≤ G.degree y := by
    simpa only [degree] using
      (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair
        (G := G) x y hne)
  by_cases h : ∀ a b : V, a ≠ b → (G.induce {z | z ≠ a ∧ z ≠ b}).Connected
  · exact noCut G hc cap pair n del h
  · push Not at h
    obtain ⟨a,b,ne,cut⟩ := h
    by_cases edge : G.Adj a b
    · exact adjacent G hc cap pair n del ⟨a,b,edge,cut⟩
    · exact nonadjacent G hc cap pair n del ⟨a,b,ne,edge,cut⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1_H2_R1
