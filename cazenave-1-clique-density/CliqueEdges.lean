import Block

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem randic_nonneg : 0≤randic G := by
  unfold randic
  apply Finset.sum_nonneg
  intro e _
  induction e using Sym2.inductionOn with
  | hf a b =>
      change 0≤1/Real.sqrt ((G.degree a:ℝ)*G.degree b)
      positivity

theorem randic_edge_card_lower (hn : 1 < Fintype.card V) :
    (G.edgeFinset.card:ℝ)/((Fintype.card V:ℝ)-1) ≤ randic G := by
  have hpos : 0 < (Fintype.card V:ℝ)-1 := by
    exact sub_pos.mpr (by exact_mod_cast hn)
  unfold randic
  have hv : ∀ v, (G.degree v:ℝ) ≤ (Fintype.card V:ℝ)-1 := by
    intro v
    have h := G.degree_lt_card_verts v
    have h' : G.degree v+1≤Fintype.card V := by omega
    have h'' : (G.degree v:ℝ)+1≤(Fintype.card V:ℝ) := by exact_mod_cast h'
    linarith only [h'']
  have hsum : ∑ _ ∈ G.edgeFinset, 1/((Fintype.card V:ℝ)-1) ≤
      ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
    apply Finset.sum_le_sum
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      change 1/((Fintype.card V:ℝ)-1) ≤ 1/Real.sqrt ((G.degree a:ℝ)*G.degree b)
      have hab : G.Adj a b := mem_edgeFinset.mp he
      have hda : 0<(G.degree a:ℝ) := by
        exact_mod_cast (G.degree_pos_iff_exists_adj a).2 ⟨b,hab⟩
      have hdb : 0<(G.degree b:ℝ) := by
        exact_mod_cast (G.degree_pos_iff_exists_adj b).2 ⟨a,hab.symm⟩
      apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (mul_pos hda hdb))
      apply Real.sqrt_le_iff.2
      refine ⟨hpos.le,?_⟩
      rw [pow_two]
      exact mul_le_mul (hv a) (hv b) hdb.le hpos.le
  simpa [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv] using hsum

theorem clique_edge_card_lower (S : Finset V) (h : IsCliqueSet G S) :
    (S.card:ℝ)*((S.card:ℝ)-1) ≤ 2*(G.edgeFinset.card:ℝ) := by
  classical
  let H := restrict G S
  have he : H.edgeFinset ⊆ G.edgeFinset := fun _ he =>
    mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G S))
      (mem_edgeFinset.mp he))
  have hN (u : V) : H.neighborFinset u = if u∈S then S.erase u else ∅ := by
    ext v
    rw [H.mem_neighborFinset]
    change (G.Adj u v ∧ u ∈ S ∧ v∈S) ↔ _
    by_cases hu : u∈S
    · simp only [hu,if_true,Finset.mem_erase,true_and]
      constructor
      · exact fun a => ⟨a.1.ne.symm,a.2⟩
      · exact fun a => ⟨h u hu v a.2 (Ne.symm a.1),a.2⟩
    · simp [hu]
  have hD (u : V) : H.degree u = if u∈S then S.card-1 else 0 := by
    simp only [← H.card_neighborFinset_eq_degree,hN]
    split
    next hu => exact Finset.card_erase_of_mem hu
    next _ => rfl
  have hs := H.sum_degrees_eq_twice_card_edges
  simp_rw [hD] at hs
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,
    nsmul_eq_mul] at hs
  have hc := Finset.card_le_card he
  by_cases h0 : S.card=0
  · simp [h0]
  have hs' : (S.card:ℝ)*((S.card:ℝ)-1) = 2*(H.edgeFinset.card:ℝ) := by
    have h1 : 1≤S.card := by omega
    rw [← Nat.cast_one (R:=ℝ),← Nat.cast_sub h1]
    exact_mod_cast hs
  exact hs'.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by norm_num))

#print axioms randic_edge_card_lower
#print axioms clique_edge_card_lower
end CazenaveOne
