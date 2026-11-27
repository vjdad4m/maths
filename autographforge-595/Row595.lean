import Packing

namespace RegularHarmonic595
open SimpleGraph Finset Graffiti326

/-- Symmetric edge weight, summed once per unordered edge (row 2598). -/
def harmonicIndex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift
    ⟨fun u v => (2 : ℚ) / ((G.degree u + G.degree v : ℕ) : ℚ),
      fun u v => by dsimp only; rw [Nat.add_comm]⟩ e

theorem harmonic_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) (reg : G.IsRegularOfDegree d) :
    harmonicIndex G = Fintype.card V / (2:ℚ) := by
  have handshake := G.sum_degrees_eq_twice_card_edges
  simp only [reg.degree_eq, sum_const,card_univ,smul_eq_mul] at handshake
  have hand : (Fintype.card V : ℚ) * d = 2 * G.edgeFinset.card := by exact_mod_cast handshake
  have hp : (0:ℚ) < d := by exact_mod_cast hd
  unfold harmonicIndex
  calc
    _ = ∑ _e ∈ G.edgeFinset, (1:ℚ) / d := by
      apply sum_congr rfl
      intro e _
      induction e using Sym2.inductionOn with
      | _ u v =>
        simp only [Sym2.lift_mk,reg.degree_eq,Nat.cast_add]
        field_simp
        linarith
    _ = _ := by
      simp only [sum_const,nsmul_eq_mul]
      have algebra (m N : ℚ) (h : N * d = 2 * m) : m * (1 / d) = N / 2 := by
        field_simp
        linarith
      exact algebra _ _ hand

theorem regular_criterion {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) (reg : G.IsRegularOfDegree d) :
    harmonicIndex G - 1/2 ≤ (matchingNumber G : ℚ) ↔
      Fintype.card V ≤ 2 * matchingNumber G + 1 := by
  rw [harmonic_regular G hd reg]
  constructor
  · intro h
    have : (Fintype.card V : ℚ) ≤ 2 * matchingNumber G + 1 := by linarith
    exact_mod_cast this
  · intro h
    have : (Fintype.card V : ℚ) ≤ 2 * matchingNumber G + 1 := by exact_mod_cast h
    linarith

theorem family (n) : 1 < Fintype.card (Vertex n) ∧ (graph n).Connected ∧
    (∀ v, Even ((graph n).degree v)) ∧ (graph n).IsRegularOfDegree 4 ∧
    harmonicIndex (graph n) - 1/2 - (matchingNumber (graph n) : ℚ) = (n:ℚ)/2 := by
  refine ⟨by rw [order]; omega,connected n,fun v => ?_,regular n,?_⟩
  · rw [(regular n).degree_eq v]
    decide
  · rw [harmonic_regular _ (by decide : 0 < 4) (regular n),order,matching_exact]
    push_cast
    linarith

theorem row595_false : 1 < Fintype.card (Vertex 1) ∧ (graph 1).Connected ∧
    (∀ v, Even ((graph 1).degree v)) ∧ (graph 1).IsRegularOfDegree 4 ∧
    harmonicIndex (graph 1) = 11 ∧ matchingNumber (graph 1) = 10 ∧
    ¬ harmonicIndex (graph 1) + (-1/2) ≤ (matchingNumber (graph 1) : ℚ) := by
  obtain ⟨hn,hc,he,hr,_⟩ := family 1
  have hH : harmonicIndex (graph 1) = 11 := by
    rw [harmonic_regular _ (by decide : 0 < 4) hr,order]
    norm_num
  have hm : matchingNumber (graph 1) = 10 := matching_exact 1
  exact ⟨hn,hc,he,hr,hH,hm,by rw [hH,hm]; norm_num⟩

theorem odd_witness : Fintype.card (Vertex 2) = 33 ∧
    harmonicIndex (graph 2) = 33/2 ∧ matchingNumber (graph 2) = 15 := by
  refine ⟨order 2,?_,matching_exact 2⟩
  rw [harmonic_regular _ (by decide : 0 < 4) (regular 2),order]
  norm_num

/-- Arithmetic consequence of Henning--Yeo (2007), Theorem 2.
The literature's graph-theoretic bound is the explicit hypothesis `bound`.
The counterexample and family above are independent of this theorem. -/
theorem henning_yeo_threshold {N d m : ℕ} (evenDegree : Even d)
    (bound : min ((((d:ℚ)^2 + 4) / ((d:ℚ)^2 + d + 2)) * ((N:ℚ)/2))
      (((N:ℚ)-1)/2) ≤ (m:ℚ))
    (fails : ¬ N ≤ 2*m+1) : 22 ≤ N ∧ (Odd N → 33 ≤ N) := by
  have ratio : (10:ℚ)/11 ≤ ((d:ℚ)^2+4) / ((d:ℚ)^2+d+2) := by
    have hd : (0:ℚ) ≤ d := Nat.cast_nonneg _
    apply (le_div_iff₀ (by nlinarith [sq_nonneg (d:ℚ)])).mpr
    by_cases h : d ≤ 4
    · have hq : (d:ℚ) ≤ 4 := by exact_mod_cast h
      nlinarith [mul_nonneg (show (0:ℚ) ≤ 4-d by linarith) (show (0:ℚ) ≤ 6-d by linarith)]
    · obtain ⟨j,hj⟩ := evenDegree
      have h6 : 6 ≤ d := by omega
      have hq : (6:ℚ) ≤ d := by exact_mod_cast h6
      nlinarith [mul_nonneg (show (0:ℚ) ≤ d-4 by linarith) (show (0:ℚ) ≤ d-6 by linarith)]
  have packing : 5*N ≤ 11*m := by
    rcases min_le_iff.mp bound with h | h
    · have half : (0:ℚ) ≤ N/2 := by linarith [Nat.cast_nonneg (α := ℚ) N]
      have h' := (mul_le_mul_of_nonneg_right ratio half).trans h
      have h'' : 5*(N:ℚ) ≤ 11*m := by linarith
      exact_mod_cast h''
    · have h' : (N:ℚ) ≤ 2*m+1 := by linarith
      exact (fails (by exact_mod_cast h')).elim
  constructor
  · omega
  · rintro ⟨j,hj⟩
    omega

#print axioms henning_yeo_threshold
#print axioms regular_criterion
#print axioms matching_exact
#print axioms odd_witness
#print axioms family
#print axioms row595_false

end RegularHarmonic595
