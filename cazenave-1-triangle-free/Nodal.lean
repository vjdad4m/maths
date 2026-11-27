import Core

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An adjacency eigen-equation, represented by a neighbor sum. -/
def AdjEigen (t : ℝ) (x : V → ℝ) : Prop :=
  ∀ v, t*x v = ∑ w ∈ G.neighborFinset v, x w

/-- The induced graph on s, keeping all outside vertices isolated. -/
def restrict (s : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ s ∧ w ∈ s
  symm := fun {_ _} h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless v h := G.loopless v h.1

instance (s : Finset V) : DecidableRel (restrict G s).Adj :=
  fun v w => by change Decidable (G.Adj v w ∧ v ∈ s ∧ w ∈ s); infer_instance

theorem restrict_le (s : Finset V) : restrict G s ≤ G :=
  fun _ _ h => h.1

theorem restrict_triangleFree (h : TriangleFree G) (s : Finset V) :
    TriangleFree (restrict G s) :=
  fun u v w huv huw hvw => h u v w huv.1 huw.1 hvw.1

private theorem restrict_neighbors (s : Finset V) {v : V} (hv : v ∈ s) :
    (restrict G s).neighborFinset v = (G.neighborFinset v).filter (· ∈ s) := by
  ext w
  simp [SimpleGraph.mem_neighborFinset,restrict,hv]

private theorem restrict_neighbors_out (s : Finset V) {v : V} (hv : v ∉ s) :
    (restrict G s).neighborFinset v = ∅ := by
  ext w
  simp [SimpleGraph.mem_neighborFinset,restrict,hv]

/-- Nosal's neighborhood estimate applies directly to a nonzero nonnegative
sub-eigenvector (no existence or irreducibility theorem is needed). -/
theorem triangleFree_subEigen_sq (h : TriangleFree G) (t : ℝ) (ht : 0<t)
    (x : V → ℝ) (hex : ∃ v, 0<x v)
    (hrow : ∀ v, t*x v ≤ ∑ w ∈ G.neighborFinset v, x w) :
    t^2 ≤ G.edgeFinset.card := by
  obtain ⟨a,ha⟩ := hex
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image (Finset.univ : Finset V) x ⟨a,mem_univ _⟩
  have hu' : 0<x u := ha.trans_le (hu _ (mem_univ _))
  apply le_of_mul_le_mul_right ?_ hu'
  calc
    t^2*x u = t*(t*x u) := by ring
    _ ≤ t*(∑ v ∈ G.neighborFinset u, x v) := mul_le_mul_of_nonneg_left (hrow u) ht.le
    _ = ∑ v ∈ G.neighborFinset u, t*x v := by rw [Finset.mul_sum]
    _ ≤ ∑ v ∈ G.neighborFinset u, ∑ w ∈ G.neighborFinset v, x w :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ ≤ ∑ v ∈ G.neighborFinset u, (G.degree v : ℝ)*x u := by
      apply Finset.sum_le_sum
      intro v _
      have h' := Finset.sum_le_sum
        (fun w (_ : w ∈ G.neighborFinset v) => hu w (mem_univ w))
      simpa [Finset.sum_const,nsmul_eq_mul, G.card_neighborFinset_eq_degree] using h'
    _ = (∑ v ∈ G.neighborFinset u, (G.degree v : ℝ))*x u := by rw [Finset.sum_mul]
    _ ≤ (G.edgeFinset.card : ℝ)*x u := by
      apply mul_le_mul_of_nonneg_right _ hu'.le
      have hc : ((∑ v ∈ G.neighborFinset u, G.degree v : ℕ) : ℝ) ≤ G.edgeFinset.card := by
        exact_mod_cast triangleFree_neighbor_mass G h u
      push_cast at hc
      exact hc

noncomputable def posSet (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => 0 < x v)
noncomputable def negSet (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < 0)

private theorem restrict_positive_subEigen (t : ℝ) (x : V → ℝ) (hx : AdjEigen G t x) :
    ∀ v, t*(max (x v) 0) ≤
      ∑ w ∈ (restrict G (posSet x)).neighborFinset v, max (x w) 0 := by
  intro v
  let P := posSet x
  by_cases hv : v ∈ P
  · have hpos : 0 < x v := by simpa [P,posSet] using hv
    rw [restrict_neighbors G P hv,max_eq_left hpos.le,hx v,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w ∈ P
    · have hwp : 0 < x w := by simpa [P,posSet] using hw
      simp [hw,max_eq_left hwp.le]
    · have hwp : x w ≤ 0 := by simpa [P,posSet,not_lt] using hw
      simpa [hw] using hwp
  · have hvp : x v ≤ 0 := by simpa [P,posSet,not_lt] using hv
    rw [restrict_neighbors_out G P hv,max_eq_right hvp, mul_zero, Finset.sum_empty]

theorem positive_support_edges (h : TriangleFree G) (t : ℝ) (ht : 0<t)
    (x : V → ℝ) (he : AdjEigen G t x) (hx : ∃ v, 0<x v) :
    t^2 ≤ (restrict G (posSet x)).edgeFinset.card :=
  triangleFree_subEigen_sq (restrict G (posSet x))
    (restrict_triangleFree G h _) t ht (fun v => max (x v) 0)
    (by obtain ⟨v,hv⟩ := hx; exact ⟨v,hv.trans_le (le_max_left _ _)⟩)
    (restrict_positive_subEigen G t x he)

theorem negative_support_edges (h : TriangleFree G) (t : ℝ) (ht : 0<t)
    (x : V → ℝ) (he : AdjEigen G t x) (hx : ∃ v, x v<0) :
    t^2 ≤ (restrict G (negSet x)).edgeFinset.card := by
  have he' : AdjEigen G t (fun v => - x v) := by
    intro v
    simp_rw [Finset.sum_neg_distrib, mul_neg, he v]
  have hx' : ∃ v, 0< -x v := by obtain ⟨v,hv⟩ := hx; exact ⟨v,neg_pos.mpr hv⟩
  have hh := positive_support_edges G h t ht (fun v => -x v) he' hx'
  have hset : posSet (fun v => -x v) = negSet x := by
    ext v; simp [posSet,negSet]
  rwa [hset] at hh

theorem crossing_of_walk {u v : V} (p : G.Walk u v) (s : Finset V)
    (hu : u ∈ s) (hv : v ∉ s) : ∃ a b, G.Adj a b ∧ a ∈ s ∧ b ∉ s := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ s
      · exact ih hb hv
      · exact ⟨a,b,hab,hu,hb⟩

theorem support_edge_budget (hc : G.Connected) (x : V → ℝ)
    (hx : ∃ v, 0<x v) (hx' : ∃ v, x v<0) :
    (restrict G (posSet x)).edgeFinset.card+(restrict G (negSet x)).edgeFinset.card+1 ≤
      G.edgeFinset.card := by
  classical
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hx'
  obtain ⟨p⟩ := hc.preconnected u v
  let P := posSet x
  let N := negSet x
  let PS := (restrict G P).edgeFinset
  let NS := (restrict G N).edgeFinset
  have dis : Disjoint PS NS := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp [PS,NS,SimpleGraph.mem_edgeFinset,restrict,P,N,posSet,negSet]
      intro had hp _ _ hn
      exact ((not_lt_of_ge hp.le) hn).elim
  obtain ⟨a,b,had,pa,npb⟩ := crossing_of_walk G p P
    (by simpa [P,posSet] using hu) (by simpa [P,posSet] using hv.le)
  have heb : s(a,b) ∈ G.edgeFinset := by simpa [SimpleGraph.mem_edgeFinset] using had
  have ho : s(a,b) ∉ PS ∪ NS := by
    simp [PS,NS,SimpleGraph.mem_edgeFinset,restrict,P,N,posSet,negSet]
    have pa' : 0<x a := by simpa [P,posSet] using pa
    have npb' : x b≤0 := by simpa [P,posSet,not_lt] using npb
    exact ⟨fun _ _ => npb',fun _ h => (not_lt_of_ge pa'.le h).elim⟩
  have hs : insert s(a,b) (PS ∪ NS) ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact heb
    · rcases Finset.mem_union.mp h with h | h
      · exact mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G P))
          (mem_edgeFinset.mp h))
      · exact mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G N))
          (mem_edgeFinset.mp h))
  have hh := Finset.card_le_card hs
  rw [Finset.card_insert_of_not_mem ho,Finset.card_union_of_disjoint dis] at hh
  exact hh

#print axioms positive_support_edges
#print axioms negative_support_edges
#print axioms support_edge_budget
end CazenaveOne
