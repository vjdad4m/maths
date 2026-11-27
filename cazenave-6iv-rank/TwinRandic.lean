import LeafBound
import LeafStructure

open scoped BigOperators
open Finset SimpleGraph
namespace CazenaveRank
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem lift_neighbors {u : V} (a : {i : V // i ≠ u}) :
    ((G.induce {i | i ≠ u}).neighborFinset a).map
      ⟨Subtype.val, Subtype.val_injective⟩ = (G.neighborFinset a.val).erase u := by
  ext b
  simp only [Finset.mem_map, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hu,hw⟩
    exact ⟨⟨b,hu⟩,hw,rfl⟩

private theorem leaf_difference_positive {d : ℕ} (h : 2 ≤ d) :
    0 < 1/Real.sqrt (d:ℝ) -
      ((d:ℝ)-1) * (1/Real.sqrt ((d:ℝ)-1)-1/Real.sqrt (d:ℝ)) := by
  let x := Real.sqrt (d:ℝ)
  let y := Real.sqrt ((d:ℝ)-1)
  have hd : (2:ℝ) ≤ d := by exact_mod_cast h
  have hx : 0 < x := Real.sqrt_pos.2 (by linarith)
  have hy : 0 < y := Real.sqrt_pos.2 (by linarith)
  have hx2 : x*x = d := by rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hy2 : y*y = (d:ℝ)-1 := by rw [← pow_two, Real.sq_sqrt (by linarith)]
  have gap : 0 < x-y := sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith : 0 ≤ (d:ℝ)-1) (by linarith))
  change 0 < 1/x - ((d:ℝ)-1)*(1/y-1/x)
  have H : 1/x - ((d:ℝ)-1)*(1/y-1/x) = x-y := by
    field_simp [hx.ne',hy.ne']
    calc
      _ = y * (d:ℝ) - x * ((d:ℝ)-1) := by ring
      _ = y * (x*x) - x * (y*y) := by rw [hx2,hy2]
      _ = _ := by ring
  rw [H]
  exact gap

private noncomputable def totalWeight (q : V → ℝ) : ℝ :=
  ∑ a : V, ∑ b : V, if G.Adj a b then q a * q b else 0

private theorem totalWeight_add_vertex (q : V → ℝ) (u : V) (t : ℝ) :
    totalWeight G (fun a => q a + if a = u then t else 0) =
      totalWeight G q + 2 * t * ∑ b ∈ G.neighborFinset u, q b := by
  classical
  let d (a : V) : ℝ := if a = u then t else 0
  have spread (a b : V) :
      (if G.Adj a b then (q a + d a) * (q b + d b) else 0) =
        (if G.Adj a b then q a * q b else 0) +
        ((if a = u then (if G.Adj u b then t * q b else 0) else 0) +
         (if b = u then (if G.Adj u a then t * q a else 0) else 0)) := by
    by_cases ha : a = u <;> by_cases hb : b = u
    · subst a; subst b; simp
    · subst a
      by_cases e : G.Adj u b
      · simp [d,hb,e]; ring
      · simp [d,hb,e]
    · subst b; by_cases e : G.Adj u a
      · simp [d,ha,e,e.symm]; ring
      · have ee : ¬G.Adj a u := fun h => e h.symm
        simp [d,ha,e,ee]
    · simp [d,ha,hb]
  change (∑ a : V, ∑ b : V, if G.Adj a b then (q a + d a) * (q b + d b) else 0) = _
  simp_rw [spread, Finset.sum_add_distrib]
  have h₁ : (∑ a : V, ∑ b : V,
      if a = u then (if G.Adj u b then t*q b else 0) else 0) =
      t * ∑ b ∈ G.neighborFinset u, q b := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1
    ext b
    simp [G.mem_neighborFinset]
  have h₂ : (∑ a : V, ∑ b : V,
      if b = u then (if G.Adj u a then t*q a else 0) else 0) =
      t * ∑ b ∈ G.neighborFinset u, q b := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1
    ext b
    simp [G.mem_neighborFinset]
  rw [h₁,h₂]
  unfold totalWeight
  ring

omit [DecidableEq V] in
private theorem totalWeight_recip :
    totalWeight G (fun a => 1/Real.sqrt (G.degree a)) = 2 * randicRows G := by
  unfold totalWeight randicRows
  dsimp only
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext b
    simp [G.mem_neighborFinset]
  · intro b _
    rw [one_div_mul_one_div]

private theorem totalWeight_induce {u : V} (q : V → ℝ) (hq : q u = 0) :
    totalWeight (G.induce {i | i ≠ u}) (fun a => q a.val) = totalWeight G q := by
  classical
  let S : Finset V := Finset.univ.erase u
  have hS (x : V) : x ∈ S ↔ x ≠ u := by simp [S]
  let f (a b : V) : ℝ := if G.Adj a b then q a * q b else 0
  have left (b : V) : f u b = 0 := by simp [f,hq]
  have right (a : V) : f a u = 0 := by simp [f,hq]
  change (∑ a : {i : V // i ≠ u}, ∑ b : {i : V // i ≠ u}, f a.val b.val) = ∑ a, ∑ b, f a b
  simp_rw [← Finset.sum_subtype S hS]
  rw [← Finset.sum_subtype S hS (fun a => ∑ b ∈ S, f a b)]
  calc
    _ = ∑ a ∈ S, ∑ b, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_subset (Finset.subset_univ S)
      intro b _ hb
      have eq : b = u := not_ne_iff.mp (fun e => hb ((hS b).2 e))
      simp [eq,right]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro a _ ha
      have eq : a = u := not_ne_iff.mp (fun e => ha ((hS a).2 e))
      simp [eq,left]

/-- Deleting a leaf sharing its support with another leaf decreases the Randić index. -/
theorem randicRows_remove_twin_leaf {u v a : V} (hc : G.Connected)
    (huv : u ≠ v) (hau : G.Adj a u) (hav : G.Adj a v) (hdu : G.degree u = 1) :
    randicRows (G.induce {i | i ≠ u}) < randicRows G := by
  classical
  let H := G.induce {i | i ≠ u}
  have hna := G.ne_of_adj hau
  have only (b : V) (h : G.Adj u b) : b = a := by
    apply (Finset.card_le_one_iff.mp (show (G.neighborFinset u).card ≤ 1 from hdu.le))
    · exact (G.mem_neighborFinset _ _).2 h
    · exact (G.mem_neighborFinset _ _).2 hau.symm
  have huN : G.neighborFinset u = {a} := by
    ext b
    simp only [G.mem_neighborFinset, Finset.mem_singleton]
    exact ⟨only b,fun e => e ▸ hau.symm⟩
  have hmau : u ∈ G.neighborFinset a := (G.mem_neighborFinset _ _).2 hau
  have hd : 2 ≤ G.degree a := by
    by_contra! bad
    exact huv (Finset.card_le_one_iff.mp (show (G.neighborFinset a).card ≤ 1 by
      change G.degree a ≤ 1; omega) hmau ((G.mem_neighborFinset _ _).2 hav))
  have hnv : 2 ≤ Fintype.card V :=
    Finset.one_lt_card_iff.mpr ⟨u, v, Finset.mem_univ _, Finset.mem_univ _, huv⟩
  have positive (b : V) : 0 < G.degree b := positive_of_connected G hc hnv b
  let q (b : V) : ℝ := 1/Real.sqrt (G.degree b)
  let r (b : V) : ℝ := q b + if b = u then -1 else 0
  let delta : ℝ := 1/Real.sqrt ((G.degree a : ℝ)-1) - q a
  let r' (b : V) : ℝ := r b + if b = a then delta else 0
  have hqu : q u = 1 := by simp [q,hdu]
  have rzero : r u = 0 := by simp [r,hqu]
  have r'zero : r' u = 0 := by simp [r',rzero,hna.symm]
  have deg (b : {i : V // i ≠ u}) :
      H.degree b = ((G.neighborFinset b.val).erase u).card := by
    rw [← lift_neighbors G b,Finset.card_map]
    rfl
  have eqH (b : {i : V // i ≠ u}) : r' b.val = 1/Real.sqrt (H.degree b) := by
    by_cases hb : b.val = a
    · have hcard := Finset.card_erase_add_one hmau
      change ((G.neighborFinset a).erase u).card + 1 = G.degree a at hcard
      have hNat : H.degree b + 1 = G.degree a := by rw [deg,hb,hcard]
      have hReal : (H.degree b : ℝ) + 1 = G.degree a := by exact_mod_cast hNat
      have he : (H.degree b : ℝ) = (G.degree a : ℝ)-1 := by linarith
      simp [r',r,delta,hb,hna,he]
    · have non : u ∉ G.neighborFinset b.val := by
        intro hh
        exact hb (only b.val ((G.mem_neighborFinset _ _).mp hh).symm)
      have dEq : H.degree b = G.degree b.val := by
        rw [deg,Finset.erase_eq_of_not_mem non]
        rfl
      simp [r',r,hb,b.property,q,dEq]
  have hp : (0:ℝ) ≤ delta := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 ?_) (Real.sqrt_le_sqrt (by linarith))
    have hh : (2:ℝ) ≤ G.degree a := by exact_mod_cast hd
    linarith
  have hsum : (∑ b ∈ G.neighborFinset a, r b) ≤ (G.degree a:ℝ)-1 := by
    rw [← Finset.sum_erase_add _ _ hmau,rzero,add_zero]
    have he : ∀ b ∈ (G.neighborFinset a).erase u, r b ≤ 1 := by
      intro b hb
      have nb := (Finset.mem_erase.mp hb).1
      simp only [r,nb,if_false,add_zero,q]
      have hd' : (1:ℝ) ≤ G.degree b := by exact_mod_cast positive b
      have hx : (1:ℝ) ≤ Real.sqrt (G.degree b) := Real.le_sqrt_of_sq_le (by simpa using hd')
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hx)).2 (by simpa using hx)
    have h := Finset.sum_le_sum he
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at h
    have hn := Finset.card_erase_add_one hmau
    change ((G.neighborFinset a).erase u).card + 1 = G.degree a at hn
    have hr : (((G.neighborFinset a).erase u).card : ℝ)+1 = G.degree a := by exact_mod_cast hn
    linarith
  have e₁ : totalWeight G r = totalWeight G q - 2*q a := by
    rw [show r = (fun b => q b + if b = u then -1 else 0) from rfl, totalWeight_add_vertex,huN]
    simp only [Finset.sum_singleton]
    ring
  have e₂ : totalWeight G r' = totalWeight G r + 2*delta*∑ b ∈ G.neighborFinset a, r b :=
    totalWeight_add_vertex G r a delta
  have ereal : totalWeight G r' = 2*randicRows H := by
    rw [← totalWeight_induce G r' r'zero,← totalWeight_recip H]
    congr 1
    funext b
    exact eqH b
  have eqold : totalWeight G q = 2*randicRows G := totalWeight_recip G
  have strict : 0 < q a - ((G.degree a:ℝ)-1)*delta := leaf_difference_positive hd
  have le := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*delta by positivity)
  rw [e₁,eqold,ereal] at e₂
  change randicRows H < randicRows G
  nlinarith only [e₂,strict,le]

#print axioms CazenaveRank.randicRows_remove_twin_leaf

#print axioms CazenaveRank.leaf_difference_positive
end CazenaveRank
