import Excess

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degrees in a vertex set count every incident edge once, with only
internal edges possibly counting twice. -/
theorem sum_degrees_le_edges_plus_internal (s : Finset V) :
    (∑ v ∈ s, G.degree v) ≤ G.edgeFinset.card + (restrict G s).edgeFinset.card := by
  classical
  let lex := Fintype.equivFin V
  let D := (Finset.univ : Finset G.Dart).filter (fun d => d.fst ∈ s)
  let test (d : G.Dart) := d.snd ∈ s ∧ lex d.snd < lex d.fst
  let K := D.filter test
  let M := D.filter (fun d => ¬test d)
  have hMaps : Set.MapsTo (fun d : G.Dart => d.fst) D s :=
    fun d hd => (Finset.mem_filter.mp hd).2
  have hfiber := Finset.card_eq_sum_card_fiberwise hMaps
  have sumeq : D.card = ∑ v ∈ s, G.degree v := by
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← G.dart_fst_fiber_card_eq_degree v]
    congr 1
    ext d
    simp [D,show d.fst ∈ s ∧ d.fst = v ↔ d.fst = v by
      constructor
      · exact And.right
      · intro e; exact ⟨e ▸ hv,e⟩]
  have hkm : K.card+M.card=D.card := Finset.filter_card_add_filter_neg_card_eq_card test
  have hk : Set.InjOn (fun d : G.Dart => d.edge) K := by
    intro a ha b hb eq
    rcases (G.dart_edge_eq_iff a b).mp eq with rfl | haeq
    · rfl
    · exfalso
      have ap : lex a.snd < lex a.fst := (Finset.mem_filter.mp ha).2.2
      have bp : lex b.snd < lex b.fst := (Finset.mem_filter.mp hb).2.2
      rw [haeq] at ap
      exact (not_lt_of_ge bp.le) ap
  have hm : Set.InjOn (fun d : G.Dart => d.edge) M := by
    intro a ha b hb eq
    rcases (G.dart_edge_eq_iff a b).mp eq with rfl | haeq
    · rfl
    · exfalso
      have haS : a.fst ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      have hbS : b.fst ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
      have haNS : a.snd ∈ s := by simpa [haeq] using hbS
      have hbNS : b.snd ∈ s := by simpa [haeq] using haS
      have l1 : ¬ lex a.snd < lex a.fst := fun h => (Finset.mem_filter.mp ha).2 ⟨haNS,h⟩
      have l2 : ¬ lex b.snd < lex b.fst := fun h => (Finset.mem_filter.mp hb).2 ⟨hbNS,h⟩
      rw [haeq] at l1
      rcases lt_trichotomy (lex b.fst) (lex b.snd) with h | h | h
      · exact l1 h
      · exact G.loopless b.fst ((lex.injective h).symm ▸ b.adj)
      · exact l2 h
  have hKsub : K.image (fun d : G.Dart => d.edge) ⊆ (restrict G s).edgeFinset := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have haS := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have haN := (Finset.mem_filter.mp ha).2.1
    exact mem_edgeFinset.mpr (show (restrict G s).Adj a.fst a.snd from ⟨a.adj,haS,haN⟩)
  have hMsub : M.image (fun d : G.Dart => d.edge) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    exact mem_edgeFinset.mpr a.edge_mem
  have hk' := Finset.card_le_card hKsub
  have hm' := Finset.card_le_card hMsub
  rw [Finset.card_image_of_injOn hk] at hk'
  rw [Finset.card_image_of_injOn hm] at hm'
  omega

/-- `k` bounds the number of triangles through any individual vertex. -/
theorem triangles_bound_neighbor_excess (k : ℕ)
    (h : ∀ u : V, (restrict G (G.neighborFinset u)).edgeFinset.card ≤ k) :
    ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k := by
  intro u
  exact (sum_degrees_le_edges_plus_internal G _).trans (Nat.add_le_add_left (h u) _)

#print axioms sum_degrees_le_edges_plus_internal
#print axioms triangles_bound_neighbor_excess

private theorem induced_neighborhood_le {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H≤G) (u : V) : restrict H (H.neighborFinset u) ≤ restrict G (G.neighborFinset u) := by
  intro a b h
  refine ⟨hHG h.1, ?_, ?_⟩
  · exact (G.mem_neighborFinset u a).2 (hHG ((H.mem_neighborFinset u a).1 h.2.1))
  · exact (G.mem_neighborFinset u b).2 (hHG ((H.mem_neighborFinset u b).1 h.2.2))

/-- Pure-original-graph version: at most k triangles pass through any vertex,
and the lower eigenvalue lies above the threshold 3k ≤ t(t−2). There is no
triangle-freeness assumption on the graph or sign supports. -/
theorem bounded_triangles (hc : G.Connected) (k : ℕ) {t L : ℝ} {x y : V → ℝ}
    (ht : t≤L) (hpos : 0<t) (hk : 3*(k:ℝ)≤t*(t-2))
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (hort : (∑ v : V,x v*y v)=0)
    (hne : ∀ u : V, (restrict G (G.neighborFinset u)).edgeFinset.card ≤ k) :
    t+1 ≤ randic G := by
  have hNodal (s : Finset V) (u : V) :
      (restrict (restrict G s) ((restrict G s).neighborFinset u)).edgeFinset.card ≤ k := by
    refine (Finset.card_le_card ?_).trans (hne u)
    exact fun e he => mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr
      (induced_neighborhood_le G (restrict_le G s) u)) (mem_edgeFinset.mp he))
  have hk' : (k:ℝ)+k+k ≤ t*(t-2) := by linarith only [hk]
  exact nodal_neighbor_excess G hc k k k ht hpos hk' he hE hx hy hort
    (triangles_bound_neighbor_excess _ k (hNodal _))
    (triangles_bound_neighbor_excess _ k (hNodal _))
    (triangles_bound_neighbor_excess G k hne)

#print axioms bounded_triangles

/-- For bounded local triangle counts, sufficiently many edges suffice without
any lower bound on the eigenvalue or conditions on its nodal supports. -/
theorem bounded_triangles_many_edges (hc : G.Connected) (k : ℕ) {t L : ℝ} {x y : V → ℝ}
    (ht : t≤L) (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (hort : (∑ v : V,x v*y v)=0)
    (hne : ∀ u : V, (restrict G (G.neighborFinset u)).edgeFinset.card ≤ k)
    (hm : (2+Real.sqrt (1+3*(k:ℝ)))^2+k ≤ G.edgeFinset.card) :
    t+1 ≤ randic G := by
  let s := Real.sqrt (1+3*(k:ℝ))
  have hs : 0≤s := Real.sqrt_nonneg _
  have hsq : s^2=1+3*(k:ℝ) := Real.sq_sqrt (by positivity)
  by_cases h : 1+s≤t
  · have htpos : 0<t := by linarith only [h,hs]
    have hcomp := mul_nonneg (sub_nonneg.mpr h) (show 0≤t+s-1 by linarith only [h,hs])
    have hu : 3*(k:ℝ)≤t*(t-2) := by nlinarith only [hcomp,hsq]
    exact bounded_triangles G hc k ht htpos hu he hE hx hy hort hne
  · let m : ℝ := G.edgeFinset.card
    change (2+s)^2+k≤m at hm
    have hm' : 0<m := by nlinarith only [hm,sq_nonneg (2+s),hs,Nat.cast_nonneg (α:=ℝ) k]
    have hsqrt : 0<Real.sqrt (m+k) := Real.sqrt_pos.2 (by positivity)
    apply le_trans ?_ (randic_of_neighbor_excess G k (triangles_bound_neighbor_excess G k hne))
    have hc' : 2+s≤m/Real.sqrt (m+k) := by
      apply (le_div_iff₀ hsqrt).2
      apply (sq_le_sq₀ (by positivity : 0≤(2+s)*Real.sqrt (m+k)) hm'.le).mp
      rw [mul_pow,Real.sq_sqrt (by positivity : 0≤m+k)]
      have haux := mul_le_mul_of_nonneg_right
        (show (2+s)^2≤m-k by linarith only [hm]) (show 0≤m+k by positivity)
      nlinarith only [haux,sq_nonneg (k:ℝ)]
    exact (show t+1≤2+s by linarith only [h]).trans hc'

#print axioms bounded_triangles_many_edges
end CazenaveOne
