import NearClique

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def crossPairs (S T : Finset V) : Finset (V×V) :=
  (T ×ˢ S).filter (fun uv => G.Adj uv.1 uv.2)

theorem cross_block_sq_edges (S T : Finset V) (z : V→ℝ) :
    (2*block G T S z)^2 ≤
      4*((crossPairs G S T).card:ℝ)*lengthSq S z*lengthSq T z := by
  classical
  let f (uv : V×V) := z uv.1*z uv.2
  have hblock : block G T S z = ∑ uv ∈ crossPairs G S T, f uv := by
    unfold crossPairs
    rw [Finset.sum_filter,Finset.sum_product]
    unfold block
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases e : G.Adj u v <;> simp [coeff,f,e]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (crossPairs G S T) (fun _ => (1:ℝ)) f
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,← hblock] at hh
  have hs : (∑ uv ∈ T ×ˢ S, (f uv)^2) = lengthSq T z*lengthSq S z := by
    unfold lengthSq
    rw [Finset.sum_product,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [f]
    ring
  have hp : (∑ uv ∈ crossPairs G S T, (f uv)^2) ≤ lengthSq T z*lengthSq S z := by
    rw [← hs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have h := hh.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
  nlinarith only [h]

theorem clique_plus_cross (S : Finset V) (hcl : IsCliqueSet G S) :
    (S.card:ℝ)*((S.card:ℝ)-1) + 2*((crossPairs G S (univ \ S)).card:ℝ) ≤
      2*(G.edgeFinset.card:ℝ) := by
  classical
  let T := (univ : Finset V) \ S
  let C := crossPairs G S T
  let H := restrict G S
  let f (p : V×V) := s(p.1,p.2)
  let E := C.image f
  have hm (p : V×V) (h : p∈C) : p.1∉S ∧ p.2∈S ∧ G.Adj p.1 p.2 := by
    have h' := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp h'.1
    exact ⟨(Finset.mem_sdiff.mp hp.1).2,hp.2,h'.2⟩
  have hinj : Set.InjOn f C := by
    intro p hp q hq h
    rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext h1 h2
    · exact ((hm p hp).1 (h1 ▸ (hm q hq).2.1)).elim
  have hEC : E.card = C.card := Finset.card_image_of_injOn hinj
  have he : E ⊆ G.edgeFinset := by
    intro e h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    exact mem_edgeFinset.mpr (hm p hp).2.2
  have hi : H.edgeFinset ⊆ G.edgeFinset := fun _ he =>
    mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G S))
      (mem_edgeFinset.mp he))
  have hdis : Disjoint E H.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e h h'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    have hH : (restrict G S).Adj p.1 p.2 := mem_edgeFinset.mp h'
    exact (hm p hp).1 hH.2.1
  have hcard := Finset.card_le_card (Finset.union_subset he hi)
  rw [Finset.card_union_of_disjoint hdis,hEC] at hcard
  have hHcl : IsCliqueSet H S := fun u hu v hv ne => ⟨hcl u hu v hv ne,hu,hv⟩
  have hh := clique_edge_card_lower H S hHcl
  have hc : (C.card:ℝ)+H.edgeFinset.card≤G.edgeFinset.card := by exact_mod_cast hcard
  change (S.card:ℝ)*((S.card:ℝ)-1) + 2*(C.card:ℝ)≤2*(G.edgeFinset.card:ℝ)
  linarith only [hh,hc]

#print axioms cross_block_sq_edges
#print axioms clique_plus_cross
theorem clique_cross_spectral (S : Finset V) (hcl : IsCliqueSet G S)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0)
    (q : ℝ) (hqr : (((univ : Finset V) \ S).card:ℝ) ≤ q)
    (hq : ((crossPairs G S (univ \ S)).card:ℝ) ≤
      q*(q-(((univ : Finset V) \ S).card:ℝ))) :
    t+1≤q := by
  obtain ⟨z,hz,hp,heq⟩ := rayleigh_zero_sum G S ht he hE hx hy ho
  let T := (univ : Finset V) \ S
  let a := lengthSq S z
  let b := lengthSq T z
  let c := 2*block G T S z
  let r : ℝ := T.card
  have ha : 0≤a := lengthSq_nonneg S z
  have hb : 0≤b := lengthSq_nonneg T z
  have hqpos : 0≤q := (Nat.cast_nonneg T.card).trans hqr
  have hcomp : 0≤q-r := sub_nonneg.mpr hqr
  have hlen : lengthSq univ z=b+a := length_partition S z
  have hsq : c^2 ≤ 4*((crossPairs G S T).card:ℝ)*a*b := cross_block_sq_edges G S T z
  have hq4 : 4*((crossPairs G S T).card:ℝ) ≤ 4*q*(q-r) := by
    nlinarith only [hq]
  have hsq' : c^2≤4*q*(q-r)*a*b :=
    hsq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq4 ha) hb)
  have hcross : c≤q*a+(q-r)*b := by
    have hright := add_nonneg (mul_nonneg hqpos ha) (mul_nonneg hcomp hb)
    by_contra! hn
    have hpos : 0≤c := hright.trans hn.le
    have hpow := (sq_lt_sq₀ hright hpos).2 hn
    nlinarith only [sq_nonneg (q*a-(q-r)*b),hsq',hpow]
  have hBB : block G T T z ≤ (r-1)*b := arbitrary_block_bound G T z
  have hEn : energy G z ≤ (q-1)*(b+a) := by
    rw [block_partition G S z,clique_block G S hcl z hz]
    change -a+block G T T z+c ≤ _
    nlinarith only [hBB,hcross]
  have hlenpos : 0<b+a := hlen ▸ hp
  rw [hlen] at heq
  have ht' : t ≤ q-1 := le_of_mul_le_mul_right (heq.trans hEn) hlenpos
  linarith only [ht']

#print axioms clique_cross_spectral
end CazenaveOne
