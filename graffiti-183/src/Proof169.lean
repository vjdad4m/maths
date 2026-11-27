import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Graffiti.pc 169. Keep all edges crossing a root's distance-parity cut.
A shortest walk descends one level at a time, so this cut spans a connected
graph. In a spanning tree each parity class is independent. -/
set_option warningAsError true
namespace Graffiti169
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/- Definitions reused from the repository proofs of #177 and #318. -/
def Indep (X : Finset V) := ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬G.Adj u v

noncomputable def leaves (T : SimpleGraph V) : Finset V := by
  classical exact univ.filter (fun v => T.degree v = 1)

noncomputable def maxLeaves := by
  classical
  exact (univ.filter (fun T : SimpleGraph V => T ≤ G ∧ T.IsTree)).sup
    (fun T => (leaves T).card)

noncomputable def evenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact ((univ : Finset V).filter (fun x => G.dist v x % 2 = 0)).card

noncomputable def maxEven (G : SimpleGraph V) : ℕ :=
  (univ : Finset V).sup (evenCount G)

noncomputable def minEven (h : Nonempty V) : ℕ := by
  letI := h
  exact univ.inf' univ_nonempty (evenCount G)

private def cross (r : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ G.dist x r % 2 ≠ G.dist y r % 2
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := h.2 rfl

omit [Fintype V] [DecidableEq V] in
theorem exists_predecessor (h : G.Connected) (r x : V) (eq : x ≠ r) :
    ∃ y, G.Adj x y ∧ G.dist x r = G.dist y r + 1 := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist x r
  cases p with
  | nil => exact (eq rfl).elim
  | @cons _ y _ e p =>
    have lower := G.dist_le p
    have upper := h.dist_triangle (u := x) (v := y) (w := r)
    rw [dist_eq_one_iff_adj.mpr e] at upper
    rw [Walk.length_cons] at hp
    exact ⟨y,e,by omega⟩

omit [Fintype V] [DecidableEq V] in
private theorem reach_root (h : G.Connected) (r x : V) : (cross G r).Reachable x r := by
  by_cases eq : x = r
  · subst x; exact Reachable.refl _
  obtain ⟨y,adj,dist⟩ := exists_predecessor G h r x eq
  have down : G.dist y r < G.dist x r := by omega
  have e : (cross G r).Adj x y := ⟨adj,by omega⟩
  exact e.reachable.trans (reach_root h r y)
termination_by G.dist x r

/-- Double counting incident edges of an independent set in a tree. -/
theorem tree_budget (T : SimpleGraph V) (ht : T.IsTree)
    (hn : 1 < Fintype.card V) (A : Finset V) (hi : Indep T A) :
    2 * A.card + 1 ≤ Fintype.card V + (leaves T).card := by
  classical
  let E := A.biUnion (fun x => T.incidenceFinset x)
  have dis : (↑A : Set V).PairwiseDisjoint (fun x => T.incidenceFinset x) := by
    intro u hu v hv ne
    apply Finset.disjoint_left.mpr
    intro e h₁ h₂
    change e ∈ T.incidenceFinset u at h₁
    change e ∈ T.incidenceFinset v at h₂
    rw [T.incidenceFinset_eq_filter] at h₁ h₂
    obtain ⟨he,hu'⟩ := mem_filter.mp h₁
    rw [(Sym2.mem_and_mem_iff ne).mp ⟨hu',(mem_filter.mp h₂).2⟩] at he
    exact hi u hu v hv ne (mem_edgeFinset.mp he)
  have sub : E ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp he
    rw [T.incidenceFinset_eq_filter] at hu
    exact (mem_filter.mp hu).1
  have count : ∑ x ∈ A, T.degree x ≤ T.edgeFinset.card := by
    simpa [E,card_biUnion dis] using card_le_card sub
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have point (x : V) : 2 ≤ T.degree x + (if x ∈ leaves T then 1 else 0) := by
    obtain ⟨y,hy⟩ := exists_ne x
    obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist x y
    have pos : 0 < p.length := hp ▸ ht.isConnected.pos_dist_of_ne hy.symm
    have edge : T.Adj x (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) pos
    have deg := (T.degree_pos_iff_exists_adj x).mpr ⟨_,edge⟩
    have mem : x ∈ leaves T ↔ T.degree x = 1 := by
      simp [leaves, SimpleGraph.degree, SimpleGraph.neighborFinset]
    split_ifs with hx
    · omega
    · have := mt mem.mpr hx; omega
  have sum := sum_le_sum (s := A) (fun x _ => point x)
  rw [sum_add_distrib] at sum
  have lc : (∑ x ∈ A, if x ∈ leaves T then 1 else 0 : ℕ) ≤ (leaves T).card := by
    simpa [filter_mem_eq_inter] using (card_le_card (inter_subset_right : A ∩ leaves T ⊆ leaves T))
  simp only [sum_const, smul_eq_mul] at sum
  have edges := ht.card_edgeFinset
  omega

/-- Both the even and odd distance counts have the same upper budget. -/
theorem parity_bounds (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) :
    2 * evenCount G r + 1 ≤ Fintype.card V + maxLeaves G ∧
    Fintype.card V + 1 ≤ 2 * evenCount G r + maxLeaves G := by
  classical
  have hcross : (cross G r).Connected :=
    (connected_iff_exists_forall_reachable _).mpr ⟨r,fun x => (reach_root G hc r x).symm⟩
  obtain ⟨T,sub,ht⟩ := hcross.exists_isTree_le
  have leaves_le : (leaves T).card ≤ maxLeaves G := le_sup
    (f := fun S => (leaves S).card) (mem_filter.mpr ⟨mem_univ _,fun _ _ e => (sub e).1,ht⟩)
  let A := univ.filter (fun v => G.dist v r % 2 = 0)
  have hi : Indep T A := by
    intro x hx y hy _ e
    exact (sub e).2 ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  have hj : Indep T (univ \ A) := by
    intro x hx y hy _ e
    have hx' : G.dist x r % 2 ≠ 0 := fun h => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hy' : G.dist y r % 2 ≠ 0 := fun h => (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    exact (sub e).2 (by omega)
  have eq : A.card = evenCount G r := by simp only [A,evenCount,dist_comm (u := r)]
  have p := tree_budget T ht hn A hi
  have q := tree_budget T ht hn _ hj
  have part := card_sdiff_add_card_eq_card (subset_univ A)
  rw [card_univ] at part
  omega

/-- Exact range bound with extrema over all vertices. -/
theorem conjecture169 (hc : G.Connected) (hn : 1 < Fintype.card V) :
    1 + (maxEven G - minEven G hc.nonempty) ≤ maxLeaves G := by
  classical
  letI := hc.nonempty
  obtain ⟨u,_,hu⟩ := exists_max_image univ (evenCount G) univ_nonempty
  obtain ⟨v,_,hv⟩ := exists_min_image univ (evenCount G) univ_nonempty
  have hm : maxEven G = evenCount G u :=
    le_antisymm (Finset.sup_le hu) (le_sup (mem_univ u))
  have hl : minEven G hc.nonempty = evenCount G v :=
    le_antisymm (inf'_le _ (mem_univ v)) (le_inf' _ _ hv)
  have a := (parity_bounds G hc hn u).1
  have b := (parity_bounds G hc hn v).2
  have c := hv u (mem_univ _)
  rw [hm,hl]
  omega

/-- Under the degree-one definition the singleton has zero leaves and range zero. -/
theorem singleton_degree_one (G : SimpleGraph Unit) :
    maxLeaves G = 0 ∧ maxEven G = 1 ∧ minEven G ⟨()⟩ = 1 := by
  classical
  have count (v : Unit) : evenCount G v = 1 := by
    cases v
    simp [evenCount, Finset.univ_unique, dist_self]
  have zero (T : SimpleGraph Unit) : leaves T = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro v hv
    have hd : T.degree v = 1 := (mem_filter.mp hv).2
    have lt := T.degree_lt_card_verts v
    simp at lt
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.eq_zero_of_le_zero
    exact Finset.sup_le (fun T _ => by simp [zero T])
  · simp [maxEven,Finset.univ_unique,count]
  · simp [minEven,Finset.univ_unique,count]

/-- The literal extension to a singleton fails if a leaf must have degree one. -/
theorem singleton_refutes_degree_one (G : SimpleGraph Unit) :
    ¬ 1 + (maxEven G - minEven G ⟨()⟩) ≤ maxLeaves G := by
  obtain ⟨hl,hu,hd⟩ := singleton_degree_one G
  rw [hl,hu,hd]
  decide

#print axioms singleton_refutes_degree_one
#print axioms singleton_degree_one
#print axioms parity_bounds
#print axioms conjecture169
end Graffiti169
