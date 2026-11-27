import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped BigOperators
namespace CazenaveRank
universe u v

noncomputable def columnRank {K V : Type*} [Field K] [Fintype V] (A : Matrix V V K) : ℕ :=
  Module.finrank K (Submodule.span K (Set.range A.col))

theorem symmetric_principal_minor {K : Type u} {V : Type v} [Field K] [Fintype V]
    (A : Matrix V V K) (hA : ∀ i j, A i j = A j i) :
    ∃ (I : Type v) (_ : Fintype I) (_ : DecidableEq I) (a : I → V), Function.Injective a ∧
      Fintype.card I = columnRank A ∧ (A.submatrix a a).det ≠ 0 := by
  classical
  obtain ⟨I,a,ha,hs,hli⟩ := exists_linearIndependent' K A.col
  letI : Finite I := Finite.of_injective a ha
  letI : Fintype I := Fintype.ofFinite I
  refine ⟨I,inferInstance,Classical.decEq I,a,ha,?_,?_⟩
  · unfold columnRank
    rw [← hs, Module.finrank_eq_card_basis (Basis.span hli)]
  let B := A.submatrix a a
  have bli : LinearIndependent K B.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have zeroAt (i : I) : ∑ j, g j * A (a j) (a i) = 0 := by
      have hi := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      simpa [B, Matrix.col, Matrix.submatrix, hA (a i)] using hi
    let L : (V → K) →ₗ[K] K :=
      ∑ j, g j • LinearMap.proj (R:=K) (ι:=V) (φ:=fun _ => K) (a j)
    have la (x : V → K) : L x = ∑ j, g j * x (a j) := by
      simp [L, smul_eq_mul]
    have vanishes : Submodule.span K (Set.range (A.col ∘ a)) ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      rintro x ⟨i,rfl⟩
      change L (A.col (a i)) = 0
      simpa only [la,Matrix.col_apply] using zeroAt i
    apply (Fintype.linearIndependent_iff.mp hli) g
    funext v
    have hv : A.col v ∈ LinearMap.ker L :=
      vanishes (hs ▸ Submodule.subset_span (show A.col v ∈ Set.range A.col from ⟨v,rfl⟩))
    rw [LinearMap.mem_ker, la] at hv
    simp only [Matrix.col_apply] at hv
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      Matrix.col_apply, Pi.zero_apply]
    simpa only [hA v] using hv
  have top : Submodule.span K (Set.range B.col) = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ Submodule.span K (Set.range B.col)
    · exact hx
    exfalso
    have hcard := linearIndependent_le_basis (Pi.basisFun K I) _ (bli.option hx)
    have hcard' := Cardinal.toNat_le_toNat hcard (Cardinal.lt_aleph0_of_finite I)
    simp only [Cardinal.mk_fintype,Cardinal.toNat_natCast,Fintype.card_option] at hcard'
    omega
  have exists_col (j : I) : ∃ c : I → K,
      ∑ i, c i • B.col i = fun k => (1 : Matrix I I K) k j :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (by rw [top]; exact Submodule.mem_top)
  choose c hc using exists_col
  let D : Matrix I I K := fun i j => c j i
  have mulD : B * D = 1 := by
    ext i j
    have eq := congrFun (hc j) i
    simpa [Matrix.mul_apply,D,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.col_apply,mul_comm] using eq
  intro z
  have impossible := congrArg Matrix.det mulD
  rw [Matrix.det_mul,z,zero_mul,Matrix.det_one] at impossible
  exact zero_ne_one impossible

theorem rank_neighbor_permutation {V : Type v} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (I : Type v) (_ : Fintype I) (a : I → V) (p : Equiv.Perm I),
      Function.Injective a ∧ Fintype.card I = columnRank (G.adjMatrix ℝ) ∧
      ∀ i, G.Adj (a i) (a (p i)) := by
  classical
  obtain ⟨I,fi,di,a,ha,hr,hdet⟩ := symmetric_principal_minor (G.adjMatrix ℝ)
    (fun i j => by simp [SimpleGraph.adjMatrix_apply, G.adj_comm i j])
  letI := fi
  letI := di
  rw [Matrix.det_apply] at hdet
  have hw : ∃ p : Equiv.Perm I, ∀ i, G.Adj (a i) (a (p i)) := by
    by_contra! h
    apply hdet
    apply Finset.sum_eq_zero
    intro p _
    obtain ⟨i,hi⟩ := h p
    have hzero : (∏ i, ((G.adjMatrix ℝ).submatrix a a) (p i) i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change (G.adjMatrix ℝ) (a (p i)) (a i) = 0
      simp [SimpleGraph.adjMatrix_apply, G.adj_comm, hi]
    rw [hzero, smul_zero]
  obtain ⟨p,hp⟩ := hw
  exact ⟨I,fi,a,p,ha,hr,hp⟩


/-- Removing a duplicated row and its matching column preserves symmetric column rank. -/
theorem columnRank_remove_duplicate {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (A : Matrix V V K) (hA : ∀ i j, A i j = A j i) {u v : V} (hvu : v ≠ u)
    (hdupe : ∀ i, A u i = A v i) :
    columnRank (A.submatrix (Subtype.val : {i // i ≠ u} → V) Subtype.val) =
      columnRank A := by
  classical
  let W := {i : V // i ≠ u}
  let vv : W := ⟨v,hvu⟩
  let q (i : V) : W := if h : i = u then vv else ⟨i,h⟩
  have hq (i : W) : q i.val = i := by simp [q,i.property]
  have hr (i j : V) : A (q i).val j = A i j := by
    by_cases hi : i = u
    · subst i; simpa [q,vv] using (hdupe j).symm
    · simp [q,hi]
  let B : Matrix W W K := A.submatrix Subtype.val Subtype.val
  let L : (W → K) →ₗ[K] (V → K) :=
    { toFun := fun f i => f (q i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have inj : Function.Injective L := by
    intro x y h
    funext i
    have hi := congrFun h i.val
    change x (q i.val) = y (q i.val) at hi
    rwa [hq] at hi
  have liftCol (i : W) : L (B.col i) = A.col i.val := by
    funext j
    exact hr j i.val
  have hrange : L '' Set.range B.col = Set.range A.col := by
    ext x; constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i.val,(liftCol i).symm⟩
    · rintro ⟨i,rfl⟩
      refine ⟨B.col (q i),⟨q i,rfl⟩,?_⟩
      rw [liftCol]
      funext j
      change A j (q i).val = A j i
      rw [hA j (q i).val, hA j i, hr]
  have H := Submodule.equivMapOfInjective L inj (Submodule.span K (Set.range B.col))
  have he := LinearEquiv.finrank_eq H
  rw [Submodule.map_span, hrange] at he
  exact he

/-- Adjacency-matrix rank is unchanged on deleting one of two open-neighborhood twins. -/
theorem rank_remove_twins {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (hvu : v ≠ u)
    (h : ∀ j, G.Adj u j ↔ G.Adj v j) :
    columnRank ((G.induce {i | i ≠ u}).adjMatrix ℝ) = columnRank (G.adjMatrix ℝ) := by
  apply columnRank_remove_duplicate (G.adjMatrix ℝ)
    (fun i j => by simp [SimpleGraph.adjMatrix_apply, G.adj_comm i j]) hvu
  intro j
  simp [SimpleGraph.adjMatrix_apply, h j]

#print axioms CazenaveRank.rank_neighbor_permutation
#print axioms CazenaveRank.rank_remove_twins
end CazenaveRank
