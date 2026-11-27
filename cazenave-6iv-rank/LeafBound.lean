import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace CazenaveRank
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- Monotonicity of x + 1/x on [1,∞), written without derivatives. -/
private theorem ratio_mono (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    x + 1/x ≤ y + 1/y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hfactor : 0 ≤ (y-x)*(x*y-1) := by
    apply mul_nonneg (sub_nonneg.mpr hxy)
    have hm := mul_le_mul hx (hx.trans hxy) (by norm_num : (0:ℝ) ≤ 1) hx0.le
    linarith
  have h1 : y + 1/y - (x + 1/x) = (y-x)*(x*y-1)/(x*y) := by field_simp; ring
  have h2 := div_nonneg hfactor (mul_nonneg hx0.le hy0.le)
  linarith

/-- Two endpoints with degree roots in [s,T] pay their proportional charges. -/
theorem nonleaf_charge (a b s T : ℝ) (hs : 0 < s)
    (ha : s ≤ a) (hb : s ≤ b) (hA : a ≤ T) (hB : b ≤ T) :
    (s*T/(s^2+T^2)) * (1/a^2 + 1/b^2) ≤ 1/(a*b) := by
  wlog hab : a ≤ b generalizing a b
  · have hh := this b a hb ha hB hA (le_of_not_ge hab)
    rwa [add_comm (1/b^2), mul_comm b a] at hh
  have ha0 : 0 < a := hs.trans_le ha
  have hb0 : 0 < b := hs.trans_le hb
  have ht0 : 0 < T := hb0.trans_le hB
  have hlow : 1 ≤ b/a := (le_div_iff₀ ha0).2 (by simpa using hab)
  have hhi : b/a ≤ T/s := (div_le_div_iff₀ ha0 hs).2 <|
    mul_le_mul hB ha hs.le ht0.le
  have hmono := ratio_mono (b/a) (T/s) hlow hhi
  have h1 : b/a + 1/(b/a) = (a^2+b^2)/(a*b) := by field_simp; ring
  have h2 : T/s + 1/(T/s) = (s^2+T^2)/(s*T) := by field_simp; ring
  rw [h1,h2] at hmono
  have hc : 0 < s^2+T^2 := add_pos (pow_pos hs 2) (pow_pos ht0 2)
  have hmono' := (div_le_div_iff₀ (mul_pos ha0 hb0) (mul_pos hs ht0)).1 hmono
  have h3 : (s*T/(s^2+T^2)) * (1/a^2 + 1/b^2) =
      ((a^2+b^2)*(s*T))/((a*b)^2*(s^2+T^2)) := by field_simp; ring
  rw [h3]
  apply (div_le_div_iff₀ (mul_pos (pow_pos (mul_pos ha0 hb0) 2) hc)
      (mul_pos ha0 hb0)).2
  have hmul := mul_le_mul_of_nonneg_right hmono' (mul_pos ha0 hb0).le
  nlinarith only [hmul]

/-- Leaf endpoints pay b=1/T-c/T². Their neighbours already pay c/x². -/
theorem leaf_charge (x T c : ℝ) (hx : 1 ≤ x) (hT : x ≤ T) (hc : c ≤ 1/2) :
    c/x^2 + (1/T-c/T^2) ≤ 1/x := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < T := by linarith
  have hm₁ := mul_le_mul_of_nonneg_right (show 1 ≤ T by linarith) hx0.le
  have hm₂ := mul_le_mul_of_nonneg_left hx ht0.le
  have hs := mul_le_mul_of_nonneg_right hc (show 0 ≤ x+T by linarith)
  have hpos : 0 ≤ (T-x)*(x*T-c*(x+T)) := by
    apply mul_nonneg (sub_nonneg.mpr hT)
    nlinarith only [hm₁,hm₂,hs]
  have hid : 1/x - (c/x^2 + (1/T-c/T^2)) =
      (T-x)*(x*T-c*(x+T))/(x^2*T^2) := by field_simp; ring
  have hd := div_nonneg hpos (mul_nonneg (sq_nonneg x) (sq_nonneg T))
  linarith

#print axioms nonleaf_charge
#print axioms leaf_charge

open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def randicRows : ℝ :=
    (∑ v : V, ∑ w ∈ G.neighborFinset v,
      (1:ℝ)/(Real.sqrt (G.degree v) * Real.sqrt (G.degree w))) / 2

/-- Charging an amount q(v) for each incident edge end yields a global Randić bound. -/
theorem weighted_end_charge (q : V → ℝ)
    (h : ∀ v w : V, G.Adj v w → q v + q w ≤
      1/(Real.sqrt (G.degree v) * Real.sqrt (G.degree w))) :
    (∑ v : V, (G.degree v : ℝ)*q v) ≤ randicRows G := by
  classical
  have h_s := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) =>
    Finset.sum_le_sum (fun w hw => h v w ((G.mem_neighborFinset _ _).mp hw)))
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h_s
  have h_sym :
      (∑ v : V, ∑ w ∈ G.neighborFinset v, q w) = ∑ w : V, (G.degree w : ℝ)*q w := by
    have h_f (v : V) : G.neighborFinset v = Finset.univ.filter (fun w => G.Adj v w) := by
      ext w
      simp [G.mem_neighborFinset]
    simp_rw [h_f, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he (w : V) :
        (∑ v : V, if G.Adj v w then q w else 0) =
        ∑ v ∈ G.neighborFinset w, q w := by
      rw [h_f, Finset.sum_filter]
      congr 1
      ext v
      exact if_congr (G.adj_comm _ _) rfl rfl
    simp_rw [he, Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
  rw [h_sym] at h_s
  simp_rw [G.card_neighborFinset_eq_degree] at h_s
  change _ ≤ (∑ v : V, ∑ w ∈ G.neighborFinset v,
      (1:ℝ)/(Real.sqrt (G.degree v) * Real.sqrt (G.degree w))) / 2
  linarith only [h_s]

/-- The sharp minimum/maximum degree-end charging inequality. In particular,
setting s=1 and T=sqrt(n-1) gives the Bollobás–Erdős lower bound. -/
theorem graph_degree_interval (s T : ℝ) (hs : 0<s)
    (h₁ : ∀ v : V, s ≤ Real.sqrt (G.degree v))
    (h₂ : ∀ v : V, Real.sqrt (G.degree v) ≤ T) :
    (Fintype.card V : ℝ) * (s*T/(s^2+T^2)) ≤ randicRows G := by
  classical
  let c := s*T/(s^2+T^2)
  let q (v : V) := c/(G.degree v : ℝ)
  have hd (v : V) : (0:ℝ) < G.degree v := Real.sqrt_pos.mp (hs.trans_le (h₁ v))
  have hh := weighted_end_charge G q (by
    intro v w _
    have hh := nonleaf_charge _ _ _ _ hs (h₁ v) (h₁ w) (h₂ v) (h₂ w)
    rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at hh
    dsimp [q,c]
    convert hh using 1; ring)
  have hq (v : V) : (G.degree v : ℝ)*q v = c := by dsimp [q]; field_simp [ne_of_gt (hd v)]
  simpa only [hq, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using hh

/-- Leaf-sensitive charging bound: all degrees are positive; d≥2 is a
maximum-degree upper bound; no leaf-to-leaf edge may occur. -/
theorem graph_leaf_interval (d : ℕ) (hd : 2 ≤ d)
    (hpos : ∀ v : V, 0 < G.degree v) (hmax : ∀ v : V, G.degree v ≤ d)
    (hno : ∀ v w : V, G.Adj v w → G.degree v = 1 → G.degree w ≠ 1) :
    let p : ℝ := ((Finset.univ.filter (fun v : V => G.degree v = 1)).card : ℝ)
    let c : ℝ := Real.sqrt 2*Real.sqrt d/(2+d)
    let b : ℝ := 1/Real.sqrt d - c/d
    ((Fintype.card V : ℝ) - p)*c+p*b ≤ randicRows G := by
  classical
  dsimp only
  let T : ℝ := Real.sqrt d
  let s : ℝ := Real.sqrt 2
  let c : ℝ := s*T/(2+d)
  let b : ℝ := 1/T-c/d
  let q (v : V) : ℝ := if G.degree v = 1 then b else c/(G.degree v : ℝ)
  have hs : 0<s := Real.sqrt_pos.2 (by norm_num)
  have ht : 0<T := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hss : s^2=2 := Real.sq_sqrt (by norm_num)
  have htt : T^2=d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : c ≤ 1/2 := by
    dsimp [c]
    apply (div_le_iff₀ (show (0:ℝ) < 2+d by linarith [Nat.cast_nonneg (α := ℝ) d])).2
    nlinarith only [sq_nonneg (s-T), hss, htt]
  have hT (v : V) : Real.sqrt (G.degree v) ≤ T := Real.sqrt_le_sqrt (by exact_mod_cast hmax v)
  have hn (v : V) (hnv : G.degree v ≠ 1) : s ≤ Real.sqrt (G.degree v) := by
    have hh : 2 ≤ G.degree v := by have := hpos v; omega
    apply Real.sqrt_le_sqrt
    exact_mod_cast hh
  have h1 (v : V) : 1 ≤ Real.sqrt (G.degree v) := by
    apply Real.le_sqrt_of_sq_le
    have hh : (1:ℝ) ≤ G.degree v := by exact_mod_cast hpos v
    simpa using hh
  have hdpos (v : V) : (0:ℝ) < G.degree v := by exact_mod_cast hpos v
  have hh := weighted_end_charge G q (by
    intro v w h
    by_cases hv : G.degree v = 1
    · have hw := hno v w h hv
      have hh := leaf_charge _ _ c (h1 w) (hT w) hc
      rw [Real.sq_sqrt (Nat.cast_nonneg _), htt] at hh
      simpa [q,hv,hw,add_comm,b] using hh
    · by_cases hw : G.degree w = 1
      · have hh := leaf_charge _ _ c (h1 v) (hT v) hc
        rw [Real.sq_sqrt (Nat.cast_nonneg _), htt] at hh
        simpa [q,hv,hw,b] using hh
      · have hh := nonleaf_charge _ _ _ _ hs (hn v hv) (hn w hw) (hT v) (hT w)
        rw [hss,htt,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)] at hh
        dsimp [q]; rw [if_neg hv, if_neg hw]
        convert hh using 1; dsimp [c]; ring)
  have hq (v : V) : (G.degree v : ℝ)*q v = if G.degree v = 1 then b else c := by
    by_cases he : G.degree v = 1
    · simp [q,he]
    · simp only [q,he,if_false]
      field_simp [ne_of_gt (hdpos v)]
  simp_rw [hq] at hh
  have he (v : V) : (if G.degree v = 1 then b else c) =
      c + (if G.degree v = 1 then b-c else 0) := by split <;> ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ] at hh
  convert hh using 1
  dsimp [b,c,T,s]; ring


theorem graph_sqrt_order (hpos : ∀ v : V, 0 < G.degree v)
    (hcard : 2 ≤ Fintype.card V) : Real.sqrt ((Fintype.card V : ℝ)-1) ≤ randicRows G := by
  let n := (Fintype.card V : ℝ)
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast hcard
  let T : ℝ := Real.sqrt (n-1)
  have hT2 : T^2=n-1 := Real.sq_sqrt (by linarith)
  have hh := graph_degree_interval G 1 T (by norm_num) (fun v => by
    apply Real.le_sqrt_of_sq_le
    have hv : (1:ℝ) ≤ G.degree v := by exact_mod_cast hpos v
    simpa using hv) (fun v => by
    apply Real.sqrt_le_sqrt
    have hv' : G.degree v + 1 ≤ Fintype.card V := Nat.succ_le_of_lt (G.degree_lt_card_verts v)
    have hi : (G.degree v : ℝ) + 1 ≤ n := by dsimp [n]; exact_mod_cast hv'
    linarith)
  have ident : n * (1*T/(1^2+T^2)) = T := by
    rw [hT2]
    have h : 1^2+(n-1)=n := by ring
    rw [h]
    field_simp [show n ≠ 0 by linarith]
  change n * (1*T/(1^2+T^2)) ≤ _ at hh
  rwa [ident] at hh

#print axioms graph_sqrt_order
#print axioms graph_degree_interval
#print axioms graph_leaf_interval
end CazenaveRank
