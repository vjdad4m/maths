import PortPrune180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected graph of maximum degree at most two with a pendant vertex
has a proper two-coloring. The degree sum forces a parity tree to exhaust
its edges. -/
theorem path_color (H : SimpleGraph V) [DecidableRel H.Adj] (hc : H.Connected)
    (u : V) (pendant : H.degree u=1) (cap : ∀ z,H.degree z≤2) : TwoColor H univ := by
  classical
  have small : (∑ z : V, H.degree z) < ∑ _z : V, (2:ℕ) :=
    sum_lt_sum (fun z _ => cap z) ⟨u,mem_univ _,by omega⟩
  rw [H.sum_degrees_eq_twice_card_edges] at small
  have rhs : (∑ _z : V, (2:ℕ))=2*Fintype.card V := by simp [Nat.mul_comm]
  rw [rhs] at small
  obtain ⟨T,th,tree,par⟩ := Graffiti169.exists_parity_tree H hc u
  have count := tree.card_edgeFinset
  have equal : T=H := edgeFinset_inj.mp (eq_of_subset_of_card_le (edgeFinset_mono th) (by omega))
  subst T
  apply (color_function H _).mpr
  refine ⟨fun v => decide (H.dist v u%2=0),?_⟩
  intro a _ b _ e
  have diff := par e
  by_cases ca : H.dist a u%2=0 <;> by_cases cb : H.dist b u%2=0 <;> simp [ca,cb] <;> omega

/-- Deleting any one vertex must leave an odd obstruction in a failed marking. -/
theorem erase_odd {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (u : V) : ¬TwoColor G (univ.erase u) := by
  classical
  intro color
  have size := card_erase_add_one (mem_univ u)
  rw [card_univ] at size
  have n := size_bip G color
  have bound := rank_one_rooted G h.connected (by have := h.order; omega) r
    (block_neighbors G h.connected h.order h.block r) (by omega) odd A h.independent
  exact (Nat.not_lt_of_ge bound) h.bad

/-- Each root neighbor, when pruned to its one root edge, still leaves a
spanning tree with at least three leaves. -/
theorem port_three {G : SimpleGraph V} {r u : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (ur : G.Adj u r) : 3≤Short177.maxLeaves (prune G u {r}) := by
  classical
  let H := prune G u {r}
  have hc := prune_one G h.block ur
  have hn : 1<Fintype.card V := by have := h.order; omega
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have ul := leaf_of_unique H hc hn u (fun {a b} ua ub =>
    (mem_singleton.mp (ua.2.1 rfl)).trans (mem_singleton.mp (ub.2.1 rfl)).symm)
  have one : H.degree u=1 := (mem_filter.mp ul).2
  by_contra! small
  change Short177.maxLeaves H<3 at small
  have cap (z : V) : H.degree z≤2 := (Graffiti179.Strong.degree_le_maxLeaves H hc z).trans (by omega)
  obtain ⟨c,proper⟩ := (color_function H univ).mp (path_color H hc u one cap)
  apply erase_odd h u
  apply (color_function G _).mpr
  exact ⟨c,fun a am b bm e => proper a (mem_univ _) b (mem_univ _)
    (prune_away (mem_erase.mp am).1 (mem_erase.mp bm).1 e)⟩

/-- Full rooted rank-two inequality when the independent and parity marks
are disjoint, including a singly marked degree-two root. -/
theorem disjoint_marks (G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    (order : 2<Fintype.card V) (rank : Fintype.card V≤bipartiteNum G+2)
    (r : V) (odd : Bool) (A : Finset V) (ind : Indep G A)
    (dis : Disjoint A (parity G r odd)) :
    1+A.card+(parity G r odd).card ≤ weightedLeaves G (eligible A (parity G r odd) r)+bipartiteNum G := by
  classical
  by_contra! bad
  have h : FailedTwo G r odd A := ⟨gc,block,order,rank,ind,bad⟩
  obtain ⟨u,ru⟩ := exists_adj G gc (by omega) r
  have upper := port_leaves h u
  rw [disjoint_iff_inter_eq_empty.mp dis,card_empty] at upper
  have lower := port_three h ru.symm
  omega

#print axioms path_color
#print axioms erase_odd
#print axioms port_three
#print axioms disjoint_marks
end Minimal180.RootEar
