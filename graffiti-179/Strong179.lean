import Proof179
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The maximum-degree formulation of Graffiti.pc #179. -/
namespace Graffiti179.Strong

open Finset SimpleGraph
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- Every independent set can be enlarged to a maximal one; such a set
dominates. We use only the singleton extension. -/
theorem independent_dominating_through (v : V) :
    ∃ B : Finset V, v ∈ B ∧ Short177.Indep G B ∧ IsDom G B := by
  classical
  let F := (univ : Finset (Finset V)).filter (fun B => v ∈ B ∧ Short177.Indep G B)
  have hF : F.Nonempty := ⟨{v},mem_filter.mpr ⟨mem_univ _,by simp [Short177.Indep]⟩⟩
  obtain ⟨B,hB,top⟩ := exists_mem_eq_sup (s := F) (f := Finset.card) hF
  obtain ⟨hv,bi⟩ := (mem_filter.mp hB).2
  refine ⟨B,hv,bi,?_⟩
  intro x
  by_cases hx : x ∈ B
  · exact Or.inl hx
  · right
    by_contra hn
    push_neg at hn
    have ins : Short177.Indep G (insert x B) := by
      intro a ha b hb ab hadj
      rcases mem_insert.mp ha with hax | ha' <;> rcases mem_insert.mp hb with hbx | hb'
      · exact ab (hax.trans hbx.symm)
      · exact hn _ hb' (hax ▸ hadj)
      · exact hn _ ha' (hbx ▸ hadj.symm)
      · exact bi _ ha' _ hb' ab hadj
    have mem : insert x B ∈ F :=
      mem_filter.mpr ⟨mem_univ _,mem_insert_of_mem hv,ins⟩
    have bound := le_sup (f := Finset.card) mem
    rw [top,card_insert_of_not_mem hx] at bound
    omega

/-- Choose a maximum independent set in one neighborhood and extend its center
to an independent dominating set. The two sets are disjoint. -/
theorem gamma_add_lambda_le_bipartite (hv : Nonempty V) :
    gamma G + lambda G ≤ Short177.bipartiteNum G := by
  classical
  obtain ⟨v,_,veq⟩ := exists_mem_eq_sup (s := univ) (f := localInd G)
    (univ_nonempty (α := V))
  let F := (G.neighborFinset v).powerset.filter (Short177.Indep G)
  have hF : F.Nonempty :=
    ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [Short177.Indep]⟩⟩
  obtain ⟨A,hA,aeq⟩ := exists_mem_eq_sup (s := F) (f := Finset.card) hF
  have an : A ∈ (G.neighborFinset v).powerset := (mem_filter.mp hA).1
  have ai : Short177.Indep G A := (mem_filter.mp hA).2
  obtain ⟨B,hvB,bi,bd⟩ := independent_dominating_through G v
  have d : Disjoint B A := disjoint_left.mpr fun x hx hxa =>
    let e := (G.mem_neighborFinset v x).mp (mem_powerset.mp an hxa)
    bi _ hvB _ hx e.ne e
  have hab : B.card + A.card ≤ Short177.bipartiteNum G := by
    rw [← card_union_of_disjoint d]
    exact le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, B, A, d, rfl, bi, ai⟩)
  exact (Nat.add_le_add (gamma_le G bd)
    (show lambda G ≤ A.card from (veq.trans aeq).le)).trans hab

private theorem extend_forest {G F : SimpleGraph V} (hc : G.Connected)
    (hFG : F ≤ G) (hf : F.IsAcyclic) : ∃ T, F ≤ T ∧ T ≤ G ∧ T.IsTree := by
  classical
  obtain ⟨T, hTG, hm⟩ := {H : SimpleGraph V | H.Connected ∧ F ≤ H}.toFinite.exists_minimal_le
    (show G.Connected ∧ F ≤ G from ⟨hc, hFG⟩)
  refine ⟨T, hm.prop.2, hTG, ⟨hm.prop.1, ?_⟩⟩
  intro v p hp
  by_cases hall : ∀ e ∈ p.edges, e ∈ F.edgeSet
  · exact hf (p.transfer F hall) (hp.transfer hall)
  push_neg at hall
  obtain ⟨e, hep, heF⟩ := hall
  induction e using Sym2.ind with
  | _ a b =>
    have heT := p.edges_subset_edgeSet hep
    have hbridge : ¬T.IsBridge s(a,b) :=
      fun h => (isBridge_iff_mem_and_forall_cycle_not_mem.mp h).2 p hp hep
    have hlt : T.deleteEdges {s(a,b)} < T := lt_of_le_of_ne (T.deleteEdges_le _) (by
      intro heq
      have hnot : ¬(T.deleteEdges {s(a,b)}).Adj a b := by simp
      rw [heq] at hnot
      exact hnot ((mem_edgeSet T).mp heT))
    apply hm.not_prop_of_lt hlt
    refine ⟨hm.prop.1.connected_delete_edge_of_not_isBridge hbridge, ?_⟩
    intro a' b' hab
    refine deleteEdges_adj.mpr ⟨hm.prop.2 hab, ?_⟩
    intro hEq
    exact heF ((Set.mem_singleton_iff.mp hEq) ▸ ((mem_edgeSet F).mpr hab))

def starAt (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ (a = v ∨ b = v)
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun a h => G.loopless a h.1

omit [Fintype V] in
private theorem starAt_acyclic (G : SimpleGraph V) (v : V) :
    (starAt G v).IsAcyclic := by
  classical
  intro a p hp
  have hout (w : V) (hw : w ∈ p.support) (hv : w ≠ v) : False := by
    let q := p.rotate hw
    have hq : q.IsCycle := hp.rotate hw
    have hs : q.snd = v := (q.adj_snd hq.not_nil).2.resolve_left hv
    have hpen : q.penultimate = v := (q.adj_penultimate hq.not_nil).2.resolve_right hv
    exact hq.snd_ne_penultimate (hs.trans hpen.symm)
  by_cases ha : a = v
  · have hAdj := p.adj_snd hp.not_nil
    exact hout p.snd (p.getVert_mem_support 1) (fun h => hAdj.ne (ha.trans h.symm))
  · exact hout a (by simpa only [Walk.getVert_zero] using p.getVert_mem_support 0) ha

private theorem tree_leaf_bounds {T : SimpleGraph V} [Nontrivial V] (ht : T.IsTree) :
    letI : DecidableRel T.Adj := Classical.decRel _
    2 ≤ (univ.filter (fun v => T.degree v = 1)).card ∧
      ∀ v, T.degree v ≤ (univ.filter (fun v => T.degree v = 1)).card := by
  classical
  let L := univ.filter (fun v => T.degree v = 1)
  let d (v : V) := T.degree v + if v ∈ L then 1 else 0
  have hpoint (v : V) : 2 ≤ d v := by
    have hpos : 0 < T.degree v := by
      obtain ⟨w, hw⟩ := exists_ne v
      obtain ⟨p⟩ := ht.isConnected.preconnected v w
      exact (T.degree_pos_iff_exists_adj v).mpr ⟨_, p.adj_snd (Walk.not_nil_of_ne hw.symm)⟩
    by_cases hd : T.degree v = 1
    · simp [d, L, hd]
    · simp [d, L, hd]
      omega
  have hsum : (∑ v, d v) + 2 = 2*Fintype.card V + L.card := by
    have he := ht.card_edgeFinset
    have hleaf : (∑ v : V, (if v ∈ L then 1 else 0 : ℕ)) = L.card := by simp
    unfold d
    rw [sum_add_distrib, T.sum_degrees_eq_twice_card_edges, hleaf]
    omega
  have hleft : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by simp [Nat.mul_comm]
  change 2 ≤ L.card ∧ ∀ v, T.degree v ≤ L.card
  refine ⟨?_, ?_⟩
  · have he : (∑ _v : V, (2 : ℕ)) ≤ ∑ v, d v := sum_le_sum (fun v _ => hpoint v)
    rw [hleft] at he
    omega
  · intro v
    have hle : (∑ w : V, (2 + if w = v then T.degree v - 2 else 0)) ≤ ∑ w, d w := by
      apply sum_le_sum
      intro w _
      by_cases h : w = v
      · subst w
        rw [if_pos rfl]
        have hpv := hpoint v
        have hdeg : T.degree v ≤ d v := Nat.le_add_right _ _
        omega
      · simpa [h] using hpoint w
    rw [sum_add_distrib, hleft] at hle
    simp only [sum_ite_eq', mem_univ, if_true] at hle
    omega


theorem degree_le_maxLeaves [Nontrivial V] (hc : G.Connected) (v : V) :
    G.degree v ≤ Short177.maxLeaves G := by
  classical
  obtain ⟨T,hstar,hTG,ht⟩ := extend_forest hc
    (show starAt G v ≤ G from fun _ _ h => h.1) (starAt_acyclic G v)
  have hd : G.degree v ≤ T.degree v := by
    apply card_le_card
    intro w hw
    exact (T.mem_neighborFinset _ _).mpr (hstar ⟨(G.mem_neighborFinset _ _).mp hw,Or.inl rfl⟩)
  exact hd.trans (((tree_leaf_bounds ht).2 v).trans
    (le_sup (f := fun T => (Short177.leaves T).card)
      (mem_filter.mpr ⟨mem_univ _,hTG,ht⟩)))

/-- West's maximum-degree reading, with the original domination number. -/
theorem conjecture179_max [Nontrivial V] (hc : G.Connected) :
    G.maxDegree + gamma G + lambda G ≤ Short177.maxLeaves G + Short177.bipartiteNum G := by
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have dl := degree_le_maxLeaves G hc v
  have gb := gamma_add_lambda_le_bipartite G (inferInstance : Nonempty V)
  omega

/-- The printed minimum-degree form follows from the maximum-degree version. -/
theorem conjecture179_min [Nontrivial V] (hc : G.Connected) :
    G.minDegree + gamma G + lambda G ≤ Short177.maxLeaves G + Short177.bipartiteNum G := by
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have hdeg : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
  have hmax := conjecture179_max G hc
  omega

#print axioms gamma_add_lambda_le_bipartite
#print axioms conjecture179_max
#print axioms conjecture179_min
end
end Graffiti179.Strong
