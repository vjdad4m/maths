import ConnectedCore
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Finset SimpleGraph Graffiti271 GraffitiCore
namespace GraffitiLeaves

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def leafSet (T : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (nbr T v).card = 1)

noncomputable def maxLeaves : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph V)).filter
    (fun T => T ≤ G ∧ T.IsTree)).sup (fun T => (leafSet T).card)

theorem leaf_card_le_maxLeaves {T : SimpleGraph V} (hle : T ≤ G) (hT : T.IsTree) :
    (leafSet T).card ≤ maxLeaves G := by
  classical
  unfold maxLeaves
  exact Finset.le_sup (f := fun T => (leafSet T).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hle,hT⟩)

omit [Fintype V] in
theorem adj_exists_of_connected {x y : V} (h : G.Connected) (hne : x ≠ y) :
    ∃ w : V, G.Adj x w := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist x y
  have hz : 0 < p.length := by rw [hp]; exact h.pos_dist_of_ne hne
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hz⟩

/-- Every vertex outside a connected dominating set can simultaneously be a leaf
    of a single spanning tree. -/
theorem complement_card_le_maxLeaves (D : Finset V)
    (hd : TotalDominates G D) (hD : (G.induce (D : Set V)).Connected) :
    Fintype.card V - D.card ≤ maxLeaves G := by
  classical
  let par (v : V) := (hd v).choose
  have hpar (v : V) : par v ∈ D ∧ G.Adj v (par v) := (hd v).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧
        ((u ∈ D ∧ v ∈ D) ∨ (u ∉ D ∧ par u = v) ∨ (v ∉ D ∧ par v = u))
      symm := by
        intro u v h
        obtain ⟨huv, h | h | h⟩ := h
        · exact ⟨huv.symm, Or.inl h.symm⟩
        · exact ⟨huv.symm, Or.inr (Or.inr h)⟩
        · exact ⟨huv.symm, Or.inr (Or.inl h)⟩
      loopless := fun u h => G.loopless u h.1 }
  let inc : G.induce (D : Set V) →g H :=
    ⟨fun v => v.1, fun {a b} h => ⟨h,Or.inl ⟨a.2,b.2⟩⟩⟩
  let lift (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨par v,(hpar v).1⟩
  have reach (v : V) : H.Reachable v (lift v).1 := by
    by_cases h : v ∈ D
    · have he : (lift v).1 = v := by simp [lift,h]
      rw [he]
    · have he : (lift v).1 = par v := by simp [lift,h]
      rw [he]
      exact (show H.Adj v (par v) from ⟨(hpar v).2, Or.inr (Or.inl ⟨h,rfl⟩)⟩).reachable
  have hH : H.Connected := by
    have : Nonempty V := ⟨(Classical.choice hD.nonempty).1⟩
    refine ⟨fun u v => ?_⟩
    exact (reach u).trans (((hD (lift u) (lift v)).map inc).trans (reach v).symm)
  obtain ⟨T, hT, ht⟩ := hH.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hT h).1
  have hleaf : (Finset.univ : Finset V) \ D ⊆ leafSet T := by
    intro v hv
    have hn : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hpne : v ≠ par v := fun h => hn (h ▸ (hpar v).1)
    obtain ⟨z,hz⟩ := adj_exists_of_connected T ht.isConnected hpne
    have single {w : V} (h : T.Adj v w) : w = par v := by
      have h' := (hT h).2
      rcases h' with h' | h' | h'
      · exact (hn h'.1).elim
      · exact h'.2.symm
      · exact (hn (h'.2 ▸ (hpar w).1)).elim
    have hs : nbr T v = {par v} := by
      ext w
      simp only [mem_nbr, Finset.mem_singleton]
      refine ⟨single, fun h => ?_⟩
      rwa [h, ← single hz]
    simp [leafSet, hs]
  have hcount := Finset.card_le_card hleaf
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hcount
  exact hcount.trans (leaf_card_le_maxLeaves G hTG ht)

theorem domination_leaves_bound
    (hc : G.Connected) (D : Finset V) (hd : TotalDominates G D) :
    Fintype.card V ≤ maxLeaves G + D.card + 2 * (D.card / 2 - 1) := by
  obtain ⟨E,hsub,hcon,hcard⟩ := exists_connected_core G hc D hd
  have he : TotalDominates G E := by
    intro v
    obtain ⟨u,hu,ha⟩ := hd v
    exact ⟨u,hsub hu,ha⟩
  have ht := complement_card_le_maxLeaves G E he hcon
  have hcc := components_le_half G D hd
  omega

#print axioms domination_leaves_bound
end GraffitiLeaves
