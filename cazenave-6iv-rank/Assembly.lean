import Combine
import Two

namespace CazenaveRank
set_option autoImplicit false

/-- Abstract selection, invariance and monotonicity interface for the final assembly.
Once instantiated with the proved real adjacency-column-rank lemmas, the result
is the rank inequality in Cazenave's Conjecture 6(iv). -/
structure RankInterface where
  rank {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ
  witness {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (I : Type) (_ : Fintype I) (e : I ↪ V) (π : Equiv.Perm I),
      Fintype.card I = rank G ∧ ∀ i, G.Adj (e i) (e (π i))
  delete {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (u v a : V) (hc : G.Connected) (huv : u ≠ v) (hau : G.Adj a u) (hav : G.Adj a v)
      (hdu : G.degree u = 1) (hdv : G.degree v = 1) :
    (G.induce {i | i ≠ u}).Connected ∧
    rank (G.induce {i | i ≠ u}) = rank G ∧
    randic (G.induce {i | i ≠ u}) < randic G

theorem RankInterface.close (L : RankInterface) (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 2 ≤ n → G.Connected →
      1+(3/2)*(Real.sqrt (L.rank G)-Real.sqrt 2) ≤ randic G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hcard hn hc
    obtain ⟨I,fi,e,π,hI,hAdj⟩ := L.witness G
    letI := fi
    by_cases hn2 : n=2
    · have hle : Fintype.card I ≤ 2 := by
        calc
          _ ≤ Fintype.card V := Fintype.card_le_of_injective e e.injective
          _ = 2 := hcard.trans hn2
      have hs : Real.sqrt (L.rank G) ≤ Real.sqrt 2 := by
        rw [← hI]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hle)
      rw [randic_order_two G hc (hcard.trans hn2)]
      linarith
    have hn3 : 3≤Fintype.card V := by omega
    by_cases h : ∀ a u v, G.Adj a u → G.Adj a v →
          G.degree u = 1 → G.degree v = 1 → u = v
    · rw [← hI]
      exact (reduced_from_permutation G e π hc hn3 hAdj h).le
    · push_neg at h
      obtain ⟨a,u,v,hau,hav,hdu,hdv,huv⟩ := h
      have ⟨hconn,hrank,hR⟩ := L.delete G u v a hc huv hau hav hdu hdv
      let W := {i : V // i ≠ u}
      let H : SimpleGraph W := G.induce {i | i ≠ u}
      have hW : Fintype.card W = Fintype.card V-1 := by
        simp [W,Fintype.card_subtype_compl]
      have hl : Fintype.card W < n := by omega
      have hh : 2 ≤ Fintype.card W := by omega
      have hIH := ih (Fintype.card W) hl W H rfl hh hconn
      change _ ≤ randic H at hIH
      rw [hrank] at hIH
      exact hIH.trans hR.le


theorem RankInterface.close_strict (L : RankInterface)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (hc : G.Connected) :
    1+(3/2)*(Real.sqrt (L.rank G)-Real.sqrt 2) < randic G := by
  obtain ⟨I,fi,e,π,hI,hAdj⟩ := L.witness G
  letI := fi
  by_cases h : ∀ a u v, G.Adj a u → G.Adj a v →
      G.degree u = 1 → G.degree v = 1 → u = v
  · rw [← hI]
    exact reduced_from_permutation G e π hc hn hAdj h
  · push_neg at h
    obtain ⟨a,u,v,hau,hav,hdu,hdv,huv⟩ := h
    have ⟨hconn,hrank,hR⟩ := L.delete G u v a hc huv hau hav hdu hdv
    let W := {i : V // i ≠ u}
    let H : SimpleGraph W := G.induce {i | i ≠ u}
    have hW : Fintype.card W = Fintype.card V-1 := by
      simp [W,Fintype.card_subtype_compl]
    have hh : 2 ≤ Fintype.card W := by omega
    have hIH := L.close (Fintype.card W) W H rfl hh hconn
    change _ ≤ randic H at hIH
    rw [hrank] at hIH
    exact hIH.trans_lt hR

/-- Two leaves with a common support have identical open neighbourhoods. -/
theorem same_neighbour_of_leaf_twins {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v a : V} (hau : G.Adj a u) (hav : G.Adj a v)
    (hdu : G.degree u = 1) (hdv : G.degree v = 1) :
    ∀ j, G.Adj u j ↔ G.Adj v j := by
  have huniq {x z w : V} (hx : G.degree x = 1)
      (hz : G.Adj x z) (hw : G.Adj x w) : z=w :=
    (Finset.card_le_one_iff.mp (show (G.neighborFinset x).card ≤ 1 from hx.le))
      ((G.mem_neighborFinset _ _).mpr hz) ((G.mem_neighborFinset _ _).mpr hw)
  intro j
  constructor
  · intro h
    rw [huniq hdu h hau.symm]
    exact hav.symm
  · intro h
    rw [huniq hdv h hav.symm]
    exact hau.symm

#print axioms RankInterface.close
#print axioms RankInterface.close_strict
end CazenaveRank
