import CageRows189

namespace GraphPathLift
open SimpleGraph

theorem degree_iso {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) (r : V) : G.degree r = H.degree (e r) := by
  classical
  rw [← G.card_neighborFinset_eq_degree,← H.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simpa only [SimpleGraph.mem_neighborFinset] using e.toHom.map_adj ((G.mem_neighborFinset r x).mp hx)
  · intro a _ b _ h; exact e.injective h
  · intro y hy
    obtain ⟨x,rfl⟩ := e.surjective y
    refine ⟨x,?_,rfl⟩
    exact (G.mem_neighborFinset r x).mpr (e.map_rel_iff.mp ((H.mem_neighborFinset _ _).mp hy))

theorem card_low_degree_iso {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) (k : ℕ) :
    (Finset.univ.filter (fun x => G.degree x<k)).card =
      (Finset.univ.filter (fun y => H.degree y<k)).card := by
  classical
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,← degree_iso G H e x] using hx
  · intro a _ b _ he; exact e.injective he
  · intro y hy
    obtain ⟨x,rfl⟩ := e.surjective y
    refine ⟨x,?_,rfl⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,degree_iso G H e x] using hy

/-- The validated SAT input exclusion lifts to unlabelled finite graphs when
the exact distance-layer cardinalities agree with a prescribed sorted shape. -/
theorem exclude_unlabelled_shape {n : ℕ} (hn : 0 < n) (L : Fin n → ℕ)
    (hs : ∀ i j, i ≤ j → L i ≤ L j)
    (hNo : ∀ H : SimpleGraph (Fin n), ∀ _ : DecidableRel H.Adj,
      H.Connected → (∀ i, H.dist ⟨0,hn⟩ i = L i) →
      (∀ i, 2 ≤ H.degree i) →
      (∀ i, (Finset.univ.filter (fun j => H.dist i j=2)).card ≤ 3) →
      (Finset.univ.filter (fun j => H.degree j<3)).card ≤ 1 → False)
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (hCard : Fintype.card V = n) (hc : G.Connected)
    (hLayerCard : ∀ d, (Finset.univ.filter (fun v => G.dist r v=d)).card =
      (Finset.univ.filter (fun i => L i=d)).card)
    (hMin : ∀ i, 2 ≤ G.degree i)
    (hD2 : ∀ i, (Finset.univ.filter (fun j => G.dist i j=2)).card ≤ 3)
    (hLow : (Finset.univ.filter (fun j => G.degree j<3)).card ≤ 1) : False := by
  classical
  subst n
  let z : Fin (Fintype.card V) := ⟨0,hn⟩
  obtain ⟨H,e,hr,hH,hm,_⟩ := exists_labelled_bfs_graph G hc r
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hL : ∀ i, H.dist z i = L i := by
    apply ordered_layers_eq_of_card _ _ hm hs
    intro d
    rw [card_distance_filter_iso H G e hH z (fun a => a=d),hr]
    exact hLayerCard d
  have hMh (i : Fin (Fintype.card V)) : 2 ≤ H.degree i := by
    rw [degree_iso H G e]; exact hMin (e i)
  have hDh (i : Fin (Fintype.card V)) : (Finset.univ.filter (fun j => H.dist i j=2)).card ≤ 3 := by
    rw [card_distance_filter_iso H G e hH i (fun a => a=2)]; exact hD2 (e i)
  have hLh : (Finset.univ.filter (fun j => H.degree j<3)).card ≤ 1 := by
    rw [card_low_degree_iso H G e]; exact hLow
  exact hNo H inferInstance hH hL hMh hDh hLh

#print axioms exclude_unlabelled_shape
end GraphPathLift
