import Large
import Small
import LeafStructure

namespace CazenaveRank
set_option autoImplicit false

/-- A connected graph of order at least three with distinct leaf supports
    satisfies the conjectured lower bound strictly when the rank has been
    identified with the size of an adjacent-permutation witness. -/
theorem reduced_from_permutation {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ι ↪ V) (π : Equiv.Perm ι)
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V)
    (hAdj : ∀ i : ι, G.Adj (e i) (e (π i)))
    (ht : ∀ v a b, G.Adj v a → G.Adj v b →
      G.degree a = 1 → G.degree b = 1 → a = b) :
    1+(3/2)*(Real.sqrt (Fintype.card ι)-Real.sqrt 2) < randic G := by
  classical
  have hpos := positive_of_connected G hc (by omega)
  by_cases hlarge : 91 ≤ Fintype.card V
  · exact large_order_from_perm G e π hlarge hpos hAdj
  have horder : Fintype.card V ≤ 90 := by omega
  let n := Fintype.card V
  let p := (Finset.univ.filter (fun v : V => G.degree v = 1)).card
  let d := dSmall n p
  have hs := separate_leaf_supports G hc hn ht
  change 2*p ≤ n ∧ (∀ v, G.degree v ≤ d) ∧ (n=3 → p=0) at hs
  have hp : p ≤ n/2 := by omega
  have hd : 2 ≤ d := by
    dsimp [d, dSmall]
    split <;> omega
  have hL := graph_leaf_interval G d hd hpos hs.2.1 (nonadjacent_leaves G hc hn)
  have hS := small_exceeds n p hn horder hp hs.2.2
  have hcard : Fintype.card ι ≤ n := Fintype.card_le_of_injective e e.injective
  have hr := Real.sqrt_le_sqrt (show (Fintype.card ι : ℝ) ≤ n by dsimp [n]; exact_mod_cast hcard)
  have hi : 1+(3/2)*(Real.sqrt (Fintype.card ι)-Real.sqrt 2) ≤
      1+(3/2)*(Real.sqrt n-Real.sqrt 2) := by linarith
  exact (hi.trans_lt hS).trans_le hL

#print axioms reduced_from_permutation
end CazenaveRank
