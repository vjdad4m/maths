import Proof169
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The star-extension and degree-to-leaves proof from vjdad4m/maths,
graffiti-179/Strong179.lean, reproduced as a standalone dependency. -/
set_option warningAsError true
namespace Graffiti179.Strong
open Finset SimpleGraph
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

theorem extend_forest {G F : SimpleGraph V} (hc : G.Connected)
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

noncomputable def starAt (G : SimpleGraph V) (v : V) : SimpleGraph V where
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

#print axioms degree_le_maxLeaves
end
end Graffiti179.Strong
