import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Ján Pastorek's AutoGraphForge, normalized row 370, ID 1754b1ab.
The proof of Theorem 7 in Joanna Cyman, Australas. J. Combin. 38 (2007),
uses the same uniqueness of a neighbor across the boundary of a tree.
Here that observation gives an injection from any independent set. -/

namespace AutoGraphForge370

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Every cycle of length at least four has a chord: an ambient edge between
two cycle vertices that is absent from its edge sequence. -/
def Chordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v⦄ (p : G.Walk v v), p.IsCycle → 4 ≤ p.length →
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ s(x,y) ∉ p.edges

omit [Fintype V] in
private theorem two_le_of_missing_edge {a b : V} (p : G.Walk a b) (hne : a ≠ b)
    (hm : s(a,b) ∉ p.edges) : 2 ≤ p.length := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons e q =>
    cases q with
    | nil => simp at hm
    | cons e' t => simp

omit [Fintype V] in
theorem forest_of_bipartite_chordal (hB : G.Colorable 2) (hC : Chordal G) :
    G.IsAcyclic := by
  classical
  obtain ⟨color⟩ := hB
  intro v p hp
  suffices aux : ∀ n (u : V) (w : G.Walk u u), w.length = n → w.IsCycle → False by
    exact aux _ _ _ rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u w hl hc
    have hthree := hc.three_le_length
    have hfour : 4 ≤ w.length := by
      by_contra! hsmall
      have len : w.length = 3 := by omega
      have a := color.valid (w.adj_getVert_succ (i := 0) (by omega))
      have b := color.valid (w.adj_getVert_succ (i := 1) (by omega))
      have c := color.valid (w.adj_getVert_succ (i := 2) (by omega))
      have hend : w.getVert 3 = u := len ▸ w.getVert_length
      simp only [Nat.reduceAdd, Walk.getVert_zero, hend] at a b c
      have noTriangle : ∀ i j k : Fin 2, i ≠ j → j ≠ k → k ≠ i → False := by decide
      exact noTriangle _ _ _ a b c
    obtain ⟨x, hx, y, hy, e, hchord⟩ := hC w hc hfour
    let rot := w.rotate hx
    have hrot := hc.rotate hx
    have hy' : y ∈ rot.support := by
      rwa [← Walk.mem_verts_toSubgraph, show rot.toSubgraph = w.toSubgraph from w.toSubgraph_rotate hx,
        Walk.mem_verts_toSubgraph]
    have hmiss : s(x,y) ∉ rot.edges := fun h => hchord ((w.rotate_edges hx).mem_iff.mp h)
    let first := rot.takeUntil y hy'
    let last := rot.dropUntil y hy'
    have hlast : 2 ≤ last.length := two_le_of_missing_edge last e.ne.symm (by
      rw [Sym2.eq_swap]; exact fun h => hmiss (rot.edges_dropUntil_subset hy' h))
    have hcycle : (Walk.cons e.symm first).IsCycle := (Walk.cons_isCycle_iff _ _).mpr
      ⟨hrot.isPath_takeUntil hy', by
        rw [Sym2.eq_swap]; exact fun h => hmiss (rot.edges_takeUntil_subset hy' h)⟩
    have hsum : first.length + last.length = rot.length := by
      rw [← Walk.length_append, Walk.take_spec]
    have hlen : rot.length = w.length := by
      change (w.rotate hx).length = w.length
      rw [Walk.rotate, Walk.length_append, add_comm,
        ← Walk.length_append, Walk.take_spec]
    exact ih _ (by rw [Walk.length_cons]; omega) _ _ rfl hcycle

omit [Fintype V] in
/-- A vertex outside a connected induced subgraph of a forest has at most
one neighbor inside it. -/
theorem boundary_unique (hG : G.IsAcyclic) {C : Set V} (hC : (G.induce C).Preconnected)
    {x y z : V} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∉ C)
    (hex : G.Adj z x) (hey : G.Adj z y) : x = y := by
  classical
  by_contra hxy
  obtain ⟨w⟩ := hC ⟨x,hx⟩ ⟨y,hy⟩
  let inc : G.induce C ↪g G := Embedding.induce C
  let q := w.toPath.map inc.toHom inc.injective
  let p : G.Walk x y := Walk.cons hex.symm (Walk.cons hey Walk.nil)
  have hp : p.IsPath := by simp [p, Walk.cons_isPath_iff, hey.ne, hex.ne.symm, hxy]
  have heq : q.val = p := congrArg Subtype.val (hG.path_unique q ⟨p,hp⟩)
  have hmem : z ∈ q.val.support := by rw [heq]; simp [p]
  change z ∈ (w.toPath.val.map inc.toHom).support at hmem
  rw [Walk.support_map, List.mem_map] at hmem
  obtain ⟨a, _, ha⟩ := hmem
  exact hz ((show (a : V) = z from ha) ▸ a.property)

/-- The complement of an outer-connected dominating set induces a connected graph. -/
def OuterDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  (∀ x ∉ D, ∃ y ∈ D, G.Adj x y) ∧ (G.induce (D : Set V)ᶜ).Connected

theorem forest_indep_le_outer_card (hG : G.IsAcyclic) (D : Finset V)
    (hD : OuterDominating G D) : G.indepNum ≤ D.card := by
  classical
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  let f (x : V) : V := if hx : x ∈ D then x else (hD.1 x hx).choose
  have mem (x : V) : f x ∈ D := by
    by_cases hx : x ∈ D
    · simp [f,hx]
    · simpa [f,hx] using (hD.1 x hx).choose_spec.1
  have adj (x : V) (hx : x ∉ D) : G.Adj x (f x) := by
    simpa [f,hx] using (hD.1 x hx).choose_spec.2
  have avoid (x : V) (hx : x ∈ A) (hout : x ∉ D) : f x ∉ A := by
    intro hfx
    have e := adj x hout
    exact ((G.isIndepSet_iff).mp hA.isIndepSet) hx hfx e.ne e
  rw [← hA.card_eq]
  apply Finset.card_le_card_of_injOn f (fun x _ => mem x)
  intro x hx y hy he
  by_cases hxd : x ∈ D <;> by_cases hyd : y ∈ D
  · simpa [f,hxd,hyd] using he
  · exact False.elim (avoid y hy hyd (he ▸ (by simpa [f,hxd] using hx : f x ∈ A)))
  · exact False.elim (avoid x hx hxd (he.symm ▸ (by simpa [f,hyd] using hy : f y ∈ A)))
  · exact boundary_unique hG hD.2.preconnected hxd hyd
      (show f x ∉ (D : Set V)ᶜ from fun h => h (mem x))
      (adj x hxd).symm (he.symm ▸ (adj y hyd).symm)

/-- A proper outer-connected dominating set exists exactly when there is an edge. -/
theorem feasible_iff_edge : (∃ D : Finset V, OuterDominating G D) ↔ ∃ x y, G.Adj x y := by
  classical
  constructor
  · rintro ⟨D, hD⟩
    obtain ⟨x⟩ := hD.2.nonempty
    obtain ⟨y, _, e⟩ := hD.1 x x.property
    exact ⟨_, _, e⟩
  · rintro ⟨x, y, e⟩
    let D := Finset.univ.erase x
    have outside (z : V) : z ∉ D ↔ z = x := by simp [D]
    refine ⟨D, ?_, ?_⟩
    · intro z hz
      obtain rfl := (outside z).mp hz
      exact ⟨y, by simp [D, e.ne.symm], e⟩
    · have uniq (z : ↥((D : Set V)ᶜ)) : (z : V) = x := (outside z).mp z.property
      rw [connected_iff]
      refine ⟨?_, ⟨⟨x, (outside x).mpr rfl⟩⟩⟩
      intro a b
      have hab : a = b := Subtype.ext ((uniq a).trans (uniq b).symm)
      subst b
      exact Reachable.rfl

/-- GraphCalc enumerates set sizes in increasing order. An absent numeric
value represents that the routine has no proper feasible set. -/
noncomputable def outerNumber (G : SimpleGraph V) : Option ℕ := by
  classical
  exact if h : ∃ n, ∃ D : Finset V, OuterDominating G D ∧ D.card = n
    then some (Nat.find h) else none

theorem outerNumber_defined_iff : (∃ k, outerNumber G = some k) ↔ ∃ x y, G.Adj x y := by
  classical
  rw [← feasible_iff_edge, outerNumber]
  split
  · rename_i h
    obtain ⟨n,D,hd,_⟩ := h
    exact iff_of_true ⟨_, rfl⟩ ⟨D, hd⟩
  · rename_i h
    simp only [reduceCtorEq, exists_const, false_iff]
    rintro ⟨D,hd⟩
    exact h ⟨D.card,D,hd,rfl⟩

/-- The exact numerical inequality at every defined input of normalized row 370. -/
theorem row370 (_hn : 2 ≤ Fintype.card V) (hb : G.Colorable 2) (hc : Chordal G)
    {k : ℕ} (hk : outerNumber G = some k) : G.indepNum ≤ k := by
  classical
  unfold outerNumber at hk
  split at hk
  · rename_i h
    cases hk
    obtain ⟨D,hd,he⟩ := Nat.find_spec h
    exact he ▸ forest_indep_le_outer_card (forest_of_bipartite_chordal hb hc) D hd
  · contradiction

#print axioms forest_of_bipartite_chordal
#print axioms forest_indep_le_outer_card
#print axioms outerNumber_defined_iff
#print axioms row370

end AutoGraphForge370
