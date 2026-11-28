import Base7
import Verified

open scoped BigOperators
open Finset
namespace BadScienceSeven.Formal

def excess (w : Coord → ℤ) (t : ℕ) : ℕ := ∑ i : Input, ((doti w i).natAbs - t)

set_option maxHeartbeats 2000000 in
theorem signedSum_budget (s : Finset Input) (b : Input → ℤ) (t : ℕ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) :
    normi (signedSum s b) ≤ (s.card * t + excess (signedSum s b) t : ℕ) := by
  let w := signedSum s b
  have h1 : normi w ≤ ∑ i ∈ s, ((doti w i).natAbs : ℤ) :=
    (normi_signed_identity s b).le.trans (Finset.sum_le_sum (fun i _ => signed_dot_le w b hb i))
  have h2 : (∑ i ∈ s, (doti w i).natAbs) ≤ s.card * t + excess w t := by
    calc
      (∑ i ∈ s, (doti w i).natAbs) ≤ ∑ i ∈ s, (t + ((doti w i).natAbs - t)) :=
        Finset.sum_le_sum (fun i _ => by omega)
      _ = s.card * t + ∑ i ∈ s, ((doti w i).natAbs - t) := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ ≤ _ := Nat.add_le_add_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => Nat.zero_le _)) _
  exact h1.trans (by exact_mod_cast h2)

theorem signedSum_abs_le_parity (s : Finset Input) (b : Input → ℤ) (j : Coord)
    (hb : ∀ i, b i = 1 ∨ b i = -1) :
    (signedSum s b j).natAbs ≤ s.card ∧ (signedSum s b j).natAbs % 2 = s.card % 2 := by
  classical
  have h eachInput : b eachInput * X eachInput j = 1 ∨ b eachInput * X eachInput j = -1 := by
    have hz : X eachInput j = 1 ∨ X eachInput j = -1 := by
      unfold X signed
      split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
    rcases hb eachInput with h|h <;> rcases hz with g|g <;> simp [h,g]
  induction s using Finset.induction_on with
  | empty => simp [signedSum]
  | @insert i s hi ih =>
      rw [show signedSum (insert i s) b j = b i * X i j + signedSum s b j by
        simp [signedSum, Finset.sum_insert hi], Finset.card_insert_of_not_mem hi]
      rcases h i with h|h <;> rw [h] <;> omega

end BadScienceSeven.Formal

namespace BadScienceSeven.Formal

abbrev Cube := Coord → Bool

def bitSign (b : Bool) : ℤ := if b then -1 else 1

def encode (p : Input × Bool) (j : Coord) : Bool :=
  Bool.xor (decide (X p.1 j = -1)) p.2

theorem X_pm (i : Input) (j : Coord) : X i j = 1 ∨ X i j = -1 := by
  unfold X signed
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem encode_spec (p : Input × Bool) (j : Coord) :
    bitSign (encode p j) = bitSign p.2 * X p.1 j := by
  rcases p with ⟨i, b⟩
  rcases X_pm i j with h|h <;> cases b <;> simp [encode, bitSign, h]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem encode_inj : Function.Injective encode := by
  have h : ∀ a b : Input × Bool, (∀ j : Coord, encode a j = encode b j) → a = b := by
    decide +kernel
  intro a b e
  exact h a b (congrFun e)

set_option maxRecDepth 16000 in
noncomputable def cubeEquiv : Input × Bool ≃ Cube :=
  Equiv.ofBijective encode ((Fintype.bijective_iff_injective_and_card encode).mpr ⟨encode_inj, by decide⟩)

theorem cubeEquiv_eq (p : Input × Bool) : cubeEquiv p = encode p := rfl

def cubedot (w : Coord → ℤ) (x : Cube) : ℤ := ∑ j, w j * bitSign (x j)

theorem bitSign_xor (x y : Bool) : bitSign (Bool.xor x y) = bitSign x * bitSign y := by
  cases x <;> cases y <;> decide

theorem full_excess (w : Coord → ℤ) (t : ℕ) :
    (∑ x : Cube, ((cubedot w x).natAbs - t)) = 2 * excess w t := by
  rw [← Equiv.sum_comp cubeEquiv, Fintype.sum_prod_type]
  simp only [cubeEquiv_eq, cubedot, encode_spec]
  have h (i : Input) (b : Bool) :
      (∑ j : Coord, w j * (bitSign b * X i j)).natAbs = (doti w i).natAbs := by
    cases b
    · simp [bitSign, doti]
    · have he : (∑ j : Coord, w j * (bitSign true * X i j)) = - doti w i := by
        simp [doti, bitSign, Finset.sum_neg_distrib]
      rw [he, Int.natAbs_neg]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat, excess]
  rw [Finset.mul_sum]

def transform (σ : Equiv.Perm Coord) (f : Cube) : Cube ≃ Cube where
  toFun x j := Bool.xor (x (σ j)) (f j)
  invFun y j := Bool.xor (y (σ.symm j)) (f (σ.symm j))
  left_inv x := by
    funext j
    simp only [Equiv.apply_symm_apply]
    cases f (σ.symm j) <;> cases x j <;> decide
  right_inv y := by
    funext j
    simp only [Equiv.symm_apply_apply]
    cases f j <;> cases y j <;> decide

theorem excess_eq_of_permute_abs (w : Coord → ℤ) (σ : Equiv.Perm Coord) (t : ℕ) :
    excess w t = excess (fun j => ((w (σ j)).natAbs : ℤ)) t := by
  let f : Cube := fun j => decide (w (σ j) < 0)
  let u : Coord → ℤ := fun j => ((w (σ j)).natAbs : ℤ)
  have he (x : Cube) : cubedot w x = cubedot u (transform σ f x) := by
    unfold cubedot
    rw [← Equiv.sum_comp σ (fun j => w j * bitSign (x j))]
    apply Finset.sum_congr rfl
    intro j hj
    change _ = u j * bitSign (Bool.xor (x (σ j)) (f j))
    have h (a : ℤ) : a = (a.natAbs : ℤ) * bitSign (decide (a < 0)) := by
      rw [← Int.abs_eq_natAbs]
      by_cases ha : a < 0
      · simp [bitSign, ha, abs_of_neg ha]
      · simp [bitSign, ha, abs_of_nonneg (le_of_not_gt ha)]
    rw [bitSign_xor, h (w (σ j))]
    unfold u f
    ring
  have hsum := Fintype.sum_equiv (transform σ f)
    (fun x => (cubedot w x).natAbs - t)
    (fun x => (cubedot u x).natAbs - t) (fun x => by simp only [he])
  simp only [] at hsum
  rw [full_excess, full_excess] at hsum
  change 2 * excess w t = 2 * excess u t at hsum
  change excess w t = excess u t
  omega

theorem norm_eq_of_permute_abs (w : Coord → ℤ) (σ : Equiv.Perm Coord) :
    normi w = normi (fun j => ((w (σ j)).natAbs : ℤ)) := by
  unfold normi
  rw [← Equiv.sum_comp σ (fun j => (w j)^2)]
  apply Finset.sum_congr rfl
  intro j hj
  have h (a : ℤ) : a ^ 2 = (a.natAbs : ℤ)^2 := by
    rw [← Int.abs_eq_natAbs, sq_abs]
  exact h _

end BadScienceSeven.Formal

namespace BadScienceSeven.Formal

theorem doti_eq_dot (u : Coord → ℕ) (i : Input) :
    doti (fun j => (u j : ℤ)) i  = dot7 (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) i.val := by
  simp [doti, X, dot7, Fin.sum_univ_succ]
  ring

theorem normi_eq_norm7 (u : Coord → ℕ) :
    normi (fun j => (u j : ℤ)) = (norm7 (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) : ℤ) := by
  simp [normi, norm7, Fin.sum_univ_succ]
  ring

theorem card_small_bound (s : Finset Input) (b : Input → ℤ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hk : s.card < 24) :
    normi (signedSum s b) ≤ (lineSq s.card : ℤ) := by
  let w := signedSum s b
  let σ := Tuple.sort (fun j => (w j).natAbs)
  let u : Coord → ℕ := fun j => (w (σ j)).natAbs
  let v : Coord → ℕ := fun j => u j / 2
  have hm : Monotone u := Tuple.monotone_sort (fun j => (w j).natAbs)
  have hmono : Monotone v := fun _ _ hj => Nat.div_le_div_right (hm hj)
  have hk6 : v 6 ≤ s.card / 2 := Nat.div_le_div_right (signedSum_abs_le_parity s b (σ 6) hb).1
  have hv (j : Coord) : 2 * v j + s.card % 2 = u j := by
    have hpar : u j % 2 = s.card % 2 := (signedSum_abs_le_parity s b (σ j) hb).2
    change 2 * (u j / 2) + s.card % 2 = u j
    rw [← hpar]
    exact Nat.div_add_mod _ _
  let k : Fin 24 := ⟨s.card, hk⟩
  let t : ℕ := if s.card < 14 then 26 else 30
  have hn := signedSum_budget s b t hb
  change normi w ≤ (s.card * t + excess w t : ℕ) at hn
  rw [norm_eq_of_permute_abs w σ, excess_eq_of_permute_abs w σ t] at hn
  change normi (fun j => (u j : ℤ)) ≤ (s.card * t + excess (fun j => (u j : ℤ)) t : ℕ) at hn
  rw [normi_eq_norm7] at hn
  have hnum := Int.ofNat_le.mp hn
  have he : excess (fun j => (u j : ℤ)) t =
      ((List.range 64).map (fun i => (dot7 (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) i).natAbs-t)).sum := by
    simp only [excess, doti_eq_dot, Fin.sum_univ_eq_sum_range]
    rfl
  rw [he] at hnum
  have hP := card_square_bound s b hb
  have hP' : normi w ≤ ((64 * s.card : ℕ) : ℤ) := by exact_mod_cast hP
  rw [norm_eq_of_permute_abs w σ] at hP'
  change normi (fun j => (u j : ℤ)) ≤ _ at hP'
  rw [normi_eq_norm7] at hP'
  have hPnum := Int.ofNat_le.mp hP'
  have hchk := sound_prefix s.card (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    (verified k (v 0) (by have := hmono (show (0:Coord) ≤ 6 by decide); change v 0 ≤ v 6 at this; change v 0 < s.card/2 + 1; omega))
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
    (hmono (by decide)) (hmono (by decide)) hk6
  dsimp only at hchk
  simp only [hv] at hchk
  have hfin := hchk hPnum hnum
  change normi w ≤ _
  rw [norm_eq_of_permute_abs w σ]
  change normi (fun j => (u j : ℤ)) ≤ _
  rw [normi_eq_norm7]
  exact_mod_cast hfin

theorem signed_row_chord (s : Finset Input) (b : Input → ℤ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) :
    Real.sqrt (normi (signedSum s b) : ℝ) ≤ chord s.card := by
  by_cases h : s.card < 24
  · have hin := card_small_bound s b hb h
    have hreal : (normi (signedSum s b) : ℝ) ≤ (lineSq s.card : ℝ) := by exact_mod_cast hin
    exact (Real.sqrt_le_sqrt hreal).trans (small_chord ⟨s.card,h⟩)
  · exact (Real.sqrt_le_sqrt (card_square_bound s b hb)).trans (large_chord _ (by omega))

end BadScienceSeven.Formal

namespace BadScienceSeven.Formal

theorem upper (A : Matrix) (hA : UnitRows A) :
    average A ≤ (6 + Real.sqrt 3)/4 := by
  classical
  have hbest (i : Input) : ∃ j : Coord, maxEval A i = |rowEval (A j) i| := by
    obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => |rowEval (A j) i|)
    exact ⟨j,h⟩
  choose g hg using hbest
  let b : Input → ℤ := fun i => if rowEval (A (g i)) i < 0 then -1 else 1
  let s : Coord → Finset Input := fun j => Finset.univ.filter (fun i => g i = j)
  have hb (i : Input) : b i = 1 ∨ b i = -1  := by unfold b; split <;> simp
  have hsign (i : Input) :
      maxEval A i = (b i : ℝ) * rowEval (A (g i)) i := by
    rw [hg]
    by_cases h : rowEval (A (g i)) i < 0
    · simp [b, h, abs_of_neg h]
    · simp [b, h, abs_of_nonneg (le_of_not_gt h)]
  have hrow (j : Coord) : ∑ i ∈ s j, maxEval A i ≤ chord (s j).card := by
    calc
      _ = ∑ i ∈ s j, (b i : ℝ) * rowEval (A j) i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hj : g i = j := (Finset.mem_filter.mp hi).2
        rw [hsign i, hj]
      _ = ∑ k : Coord, A j k * (signedSum (s j) b k : ℤ) := by
        unfold rowEval signedSum
        simp only [Finset.mul_sum, Int.cast_sum, Int.cast_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ Real.sqrt (normi (signedSum (s j) b) : ℝ) := sum_dot_le_sqrt _ _ (hA j)
      _ ≤ _ := signed_row_chord _ _ hb
  have hc : ∑ j, (s j).card = 64 := by
    simpa only [s, Finset.mem_univ, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
      using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Input)
        (Finset.univ : Finset Coord) g
  have hcR : (∑ j, ((s j).card : ℝ)) = 64 := by exact_mod_cast hc
  have hf : ∑ j, ∑ i ∈ s j, maxEval A i = ∑ i, maxEval A i :=
    Finset.sum_fiberwise _ g _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  rw [hf] at hsum
  unfold chord at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hcR] at hsum
  unfold average
  norm_num only [Nat.cast_ofNat] at hsum
  linarith

def wr (r j : Coord) : ℤ :=
  match j.val with
  | 0 => 1
  | 1 => if r.val = 0 then 1 else signed ((r.val+1)/2)
  | 2 => if r.val = 0 then 1 else signed ((r.val+1)/4)
  | 3 => if r.val = 0 then 0 else signed (r.val+1)
  | _ => 0

def denomSq (r : Coord) : ℕ := if r.val = 0 then 3 else 4

def pick (i : Input) : Coord :=
  ⟨if i.val % 4 = 0 then 0 else (i.val%4)*2 - 1 + (i.val/4)%2, by split <;> omega⟩

theorem wr_norm (r : Coord) : normi (wr r) = (denomSq r : ℤ) := by
  fin_cases r <;> decide +kernel

theorem picked_eval : ∀ i : Input, doti (wr (pick i)) i = (denomSq (pick i) : ℤ) := by
  decide +kernel

noncomputable def witness : Matrix := fun r j => (wr r j : ℝ) / Real.sqrt (denomSq r : ℝ)

theorem witness_rows : UnitRows witness := by
  intro r
  have hd : 0 < (denomSq r : ℝ) := by unfold denomSq; split <;> norm_num
  have hnorm : (∑ j, (wr r j : ℝ)^2) = (denomSq r : ℝ) := by
    exact_mod_cast wr_norm r
  simp only [witness, div_pow, Real.sq_sqrt hd.le]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, hnorm]
  rw [← div_eq_mul_inv]
  exact div_self hd.ne'

noncomputable def witnessValue (i : Input) : ℝ :=
  if i.val % 4 = 0 then Real.sqrt 3 else 2

theorem witness_eval_eq (i : Input) : rowEval (witness (pick i)) i = witnessValue i := by
  have hd : 0 < (denomSq (pick i) : ℝ) := by unfold denomSq; split <;> norm_num
  have hdot : (∑ j, (wr (pick i) j : ℝ) * (X i j : ℝ)) = (denomSq (pick i) : ℝ) := by
    exact_mod_cast picked_eval i
  have hfact : rowEval (witness (pick i)) i =
      (∑ j, (wr (pick i) j : ℝ) * (X i j : ℝ)) /
        Real.sqrt (denomSq (pick i) : ℝ) := by
    simp only [rowEval, witness, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfact, hdot, show (denomSq (pick i) : ℝ) / Real.sqrt (denomSq (pick i) : ℝ) =
        Real.sqrt (denomSq (pick i) : ℝ) from
        (div_eq_iff (Real.sqrt_pos.2 hd).ne').2 (Real.mul_self_sqrt hd.le).symm]
  have hsel : ∀ j : Input, (pick j).val = 0 ↔ j.val % 4 = 0 := by decide +kernel
  unfold witnessValue denomSq
  by_cases h : i.val % 4 = 0
  · have h' := (hsel i).mpr h
    simp [h, h']
  · have h' := mt (hsel i).mp h
    simp only [h, h', if_false, Nat.cast_ofNat]
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

theorem lower_witness : (6 + Real.sqrt 3)/4 ≤ average witness := by
  have h (i : Input) : witnessValue i ≤ maxEval witness i := by
    rw [← witness_eval_eq]
    exact (le_abs_self _).trans (Finset.le_sup' (fun r => |rowEval (witness r) i|) (Finset.mem_univ (pick i)))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  have hEven : (Finset.univ.filter (fun i : Input => i.val % 4 = 0)).card = 16 := by decide +kernel
  have hOdd : (Finset.univ.filter (fun i : Input => i.val % 4 ≠ 0)).card = 48 := by decide +kernel
  have hsum : ∑ i : Input, witnessValue i = 16 * Real.sqrt 3 + 48 * 2 := by
    have he (i : Input) : witnessValue i =
        (if i.val % 4 = 0 then Real.sqrt 3 else 0) +
        (if i.val % 4 ≠ 0 then (2 : ℝ) else 0) := by
      by_cases h : i.val % 4 = 0 <;> simp [witnessValue, h]
    simp only [he, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
      hEven, hOdd, nsmul_eq_mul, Nat.cast_ofNat]
  rw [hsum] at hs
  unfold average
  linarith

theorem exact_optimum : IsGreatest {v : ℝ | ∃ A, UnitRows A ∧ average A = v}
    ((6 + Real.sqrt 3)/4) := by
  refine ⟨⟨witness, witness_rows, le_antisymm (upper witness witness_rows) lower_witness⟩, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  exact upper A hA

end BadScienceSeven.Formal

namespace BadScienceSeven.Formal

noncomputable def cubeMax (A : Matrix) (x : Cube) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun r => |∑ j, A r j * (bitSign (x j) : ℝ)|)

noncomputable def beta (A : Matrix) : ℝ := (∑ x : Cube, cubeMax A x) / 128

theorem cubeMax_eq (A : Matrix) (p : Input × Bool) :
    cubeMax A (cubeEquiv p) = maxEval A p.1 := by
  unfold cubeMax maxEval
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro r hr
  simp only [cubeEquiv_eq, encode_spec, Int.cast_mul]
  rcases p with ⟨i,b⟩
  cases b
  · simp [bitSign, rowEval]
  · have he : (∑ j : Coord, A r j * ((bitSign true : ℝ) * (X i j : ℝ))) = - rowEval (A r) i := by
      simp [bitSign, rowEval, Finset.sum_neg_distrib]
    rw [he, abs_neg]

theorem beta_eq_average (A : Matrix) : beta A = average A := by
  unfold beta average
  rw [← Equiv.sum_comp cubeEquiv, Fintype.sum_prod_type]
  simp only [cubeMax_eq, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Steinerberger's exact objective on the full sign cube in dimension seven. -/
theorem exact_full_cube_optimum : IsGreatest {v : ℝ | ∃ A, UnitRows A ∧ beta A = v}
    ((6 + Real.sqrt 3)/4) := by
  simpa only [beta_eq_average] using exact_optimum

#print axioms exact_full_cube_optimum

end BadScienceSeven.Formal
