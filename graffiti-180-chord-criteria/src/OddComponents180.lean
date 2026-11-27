import Proof180

/-! A component bound for any eccentricity. The growth lemma from 177 is
applied to the graph obtained by deleting only even-to-even edges. -/
set_option warningAsError true
namespace Graffiti180
open SimpleGraph Finset Graffiti177 Graffiti318
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Retain precisely the edges incident to the specified support. -/
noncomputable def incidentGraph (S : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ S ∨ y ∈ S)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := G.loopless _ h.1

private theorem odd_reach (hc : G.Connected) (r v : V) : (incidentGraph G (oddSet G r)).Reachable v r := by
  by_cases eq : v = r
  · subst v; exact Reachable.refl _
  obtain ⟨u,e,d⟩ := Graffiti169.exists_predecessor G hc r v eq
  have down : G.dist u r < G.dist v r := by omega
  have f : (incidentGraph G (oddSet G r)).Adj v u := by
    refine ⟨e,?_⟩
    classical
    simp only [oddSet,mem_filter,mem_univ,true_and]
    omega
  exact f.reachable.trans (odd_reach hc r u)
termination_by G.dist v r

/-- A support whose incident edges connect the graph uses at most one extra
connector per component after the first. -/
theorem incident_leaf (S : Finset V) (hs : S.Nonempty) (hn : 1 < Fintype.card V)
    (jc : (incidentGraph G S).Connected) :
    Fintype.card V + 1 ≤ maxLeaves G + S.card + compCount G S := by
  classical
  let J := incidentGraph G S
  have ind : Indep J (univ \ S) := by
    intro x hx y hy _ e
    exact e.2.elim (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2
  obtain ⟨u,hu⟩ := hs
  have mark : Marked J {u} ∅ := by
    refine ⟨empty_subset _,?_,by simp⟩
    simpa using con_single J u
  obtain ⟨D,N,sub,_,nc,marked,bd⟩ := grow_cover J S jc ind {u} ∅
    (singleton_nonempty _) (empty_subset _) mark
  have nz : N = ∅ := card_eq_zero.mp (by simpa using nc)
  rw [nz] at marked
  have cd : Con J D := by simpa using marked.2.1
  have seenpos : 0 < (seen J S {u}).card := card_pos.mpr
    ⟨_,(mem_seen J).mpr ⟨⟨u,hu⟩,by simp,rfl⟩⟩
  have small : ({u} \ S : Finset V) = ∅ := sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hu)
  rw [small,card_empty,zero_add] at bd
  have dom (x : V) (out : x ∉ D) : Dominates J D x := by
    obtain ⟨y,e⟩ := exists_adj J jc hn x
    have ox : x ∉ S := fun h => out (sub h)
    exact ⟨y,sub (e.2.resolve_left ox),e⟩
  have leaf := conDom_leaves J D cd dom
  have mono : maxLeaves J ≤ maxLeaves G := by
    apply Finset.sup_le
    intro T hT
    obtain ⟨le,tree⟩ := (mem_filter.mp hT).2
    exact le_sup (f := fun T => (leaves T).card)
      (mem_filter.mpr ⟨mem_univ _,fun _ _ e => (le e).1,tree⟩)
  have same : J.induce (S : Set V) = G.induce (S : Set V) := by
    ext x y
    exact ⟨fun e => e.1,fun e => ⟨e,Or.inl x.property⟩⟩
  have cs : compCount J S = compCount G S := by unfold compCount; rw [same]
  have d := card_sdiff_add_card_eq_card sub
  have n := card_sdiff_add_card_eq_card (subset_univ D)
  rw [card_univ] at n
  omega

/-- For every root r, the odd set's component count pays for all connectors. -/
theorem odd_components_leaf (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) :
    evenCount G r + 1 ≤ maxLeaves G + compCount G (oddSet G r) := by
  classical
  let O := oddSet G r
  have jc : (incidentGraph G O).Connected := (connected_iff_exists_forall_reachable _).mpr
    ⟨r,fun x => (odd_reach G hc r x).symm⟩
  obtain ⟨u,eu⟩ := exists_adj G hc hn r
  have hu : u ∈ O := by simp [O,oddSet,dist_eq_one_iff_adj.mpr eu.symm]
  have leaf := incident_leaf G O ⟨u,hu⟩ hn jc
  have part : evenCount G r + O.card = Fintype.card V := by
    simpa only [evenCount,O,oddSet,dist_comm (u := r),card_univ] using
      (filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V))
        (p := fun x => G.dist x r % 2 = 0))
  change evenCount G r + 1 ≤ maxLeaves G + compCount G O
  omega

/-- A proper subset of the odd layers can use omitted vertices as extra leaves. -/
theorem of_odd_support (hn : 1 < Fintype.card V) (r : V)
    (mx : evenCount G r = maxEven G) (S : Finset V) (hs : S.Nonempty)
    (jc : (incidentGraph G S).Connected)
    (pay : independence G + S.card + compCount G S ≤ bipartiteNum G + (oddSet G r).card) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  have leaf := incident_leaf G S hs hn jc
  have part : evenCount G r + (oddSet G r).card = Fintype.card V := by
    simpa only [evenCount,oddSet,dist_comm (u := r),card_univ] using
      (filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V))
        (p := fun x => G.dist x r % 2 = 0))
  omega

theorem of_odd_components (hc : G.Connected) (hn : 1 < Fintype.card V)
    (r : V) (mx : evenCount G r = maxEven G)
    (h : independence G + compCount G (oddSet G r) ≤ bipartiteNum G) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  have := odd_components_leaf G hc hn r
  omega

/-- Odd leaves in a parity-respecting spanning tree give additional units in
the transversal bound. Even-to-even edges are the only forbidden tree edges. -/
theorem of_tree_surplus (hn : 1 < Fintype.card V) (r : V)
    (mx : evenCount G r = maxEven G) (T : SimpleGraph V) [DecidableRel T.Adj] (tree : T.IsTree) (sub : T ≤ G)
    (edges : ∀ ⦃x y⦄, T.Adj x y → x ∈ oddSet G r ∨ y ∈ oddSet G r)
    (pay : Fintype.card V + independence G ≤ maxEven G + bipartiteNum G +
      (leaves T ∩ oddSet G r).card + ∑ x ∈ univ \ oddSet G r, (T.degree x - 2)) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  let O := oddSet G r
  let A : Finset V := univ \ O
  have ind : Short177.Indep T A := by
    intro x hx y hy _ e
    exact (edges e).elim (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2
  have eq : A.card = evenCount G r := by
    unfold evenCount
    congr 1
    ext x
    simp [A,O,oddSet,dist_comm (u := r)]
  have shar := Graffiti169.tree_budget_excess T tree hn A ind
  rw [eq] at shar
  have disj : A ∩ Short177.leaves T = leaves T \ O := by
    ext x
    change x ∈ A ∩ leaves T ↔ x ∈ leaves T \ O
    simp [A,and_comm]
  rw [disj] at shar
  have parts := card_sdiff_add_card_inter (leaves T) O
  have bound : (leaves T).card ≤ maxLeaves G := le_sup
    (f := fun H => (leaves H).card) (mem_filter.mpr ⟨mem_univ _,sub,tree⟩)
  change Fintype.card V + independence G ≤ maxEven G + bipartiteNum G +
    (leaves T ∩ O).card + ∑ x ∈ A, (T.degree x - 2) at pay
  omega

theorem of_odd_leaves (hn : 1 < Fintype.card V) (r : V)
    (mx : evenCount G r = maxEven G) (T : SimpleGraph V) (tree : T.IsTree) (sub : T ≤ G)
    (edges : ∀ ⦃x y⦄, T.Adj x y → x ∈ oddSet G r ∨ y ∈ oddSet G r)
    (pay : Fintype.card V + independence G ≤ maxEven G + bipartiteNum G +
      (leaves T ∩ oddSet G r).card) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  apply of_tree_surplus G hn r mx T tree sub edges
  omega

#print axioms of_tree_surplus
#print axioms of_odd_leaves
#print axioms incident_leaf
#print axioms of_odd_support
#print axioms odd_components_leaf
#print axioms of_odd_components
end Graffiti180
