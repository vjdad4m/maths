import LeavesCore

open Finset SimpleGraph Graffiti271 GraffitiLeaves
namespace GraffitiBFS
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem one_step_toward (hc : G.Connected) (r v : V) (h : v ≠ r) :
    ∃ z, G.Adj v z ∧ G.dist r z + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  have hpos : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne h
  have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have h1 : G.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
  have h2 := SimpleGraph.dist_le p.tail
  rw [SimpleGraph.dist_comm] at h2
  change G.dist r (p.getVert 1) ≤ p.tail.length at h2
  have h3 := p.length_tail_add_one hn
  rw [hp, SimpleGraph.dist_comm] at h3
  have h4 := dist_step G hc (root := r) h1.symm
  exact ⟨_, h1, by omega⟩

/-- Rooted shortest-path parent relation, producing an actual spanning tree. -/
theorem exists_bfs_tree (hc : G.Connected) (r : V) :
    ∃ (par : V → V) (T : SimpleGraph V),
      T ≤ G ∧ T.IsTree ∧
      (∀ v, v ≠ r → G.dist r (par v) + 1 = G.dist r v) ∧
      (∀ u v, T.Adj u v ↔ (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ∧
      nbr G r = nbr T r := by
  classical
  let par (v : V) : V :=
    if h : v = r then r else (one_step_toward G hc r v h).choose
  have props (v : V) (h : v ≠ r) :
      G.Adj v (par v) ∧ G.dist r (par v) + 1 = G.dist r v := by
    simpa [par, h] using (one_step_toward G hc r v h).choose_spec
  let T : SimpleGraph V :=
    { Adj := fun u v => (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)
      symm := fun _ _ => Or.symm
      loopless := by
        intro v h
        have h := h.elim id id
        have e := (props v h.1).2
        rw [h.2] at e
        omega }
  have hsub : T ≤ G := by
    intro u v h
    change (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u) at h
    rcases h with ⟨h,e⟩ | ⟨h,e⟩
    · rw [← e]
      exact (props u h).1
    · rw [← e]
      exact (props v h).1.symm
  have treeReach : ∀ v, T.Reachable v r := by
    intro v
    generalize h : G.dist r v = d
    induction d using Nat.strong_induction_on generalizing v with
    | h d ih =>
      by_cases he : v = r
      · rw [he]
      · have hlt : G.dist r (par v) < d := by
          have hp := (props v he).2
          omega
        have had : T.Adj v (par v) := Or.inl ⟨he,rfl⟩
        exact had.reachable.trans (ih _ hlt _ rfl)
  have hconn : T.Connected := (connected_iff_exists_forall_reachable _).mpr
      ⟨r,fun v => (treeReach v).symm⟩
  have edgeImage : T.edgeFinset =
      ((Finset.univ : Finset V).erase r).image (fun v => s(v,par v)) := by
    ext e
    refine Sym2.inductionOn e (fun u v => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change ((u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ↔ _
    constructor
    · rintro (⟨hu,e⟩ | ⟨hv,e⟩)
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], by rw [e]⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], by rw [e,Sym2.eq_swap]⟩
    · intro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have hne := (Finset.mem_erase.mp hw).1
      rcases Sym2.eq_iff.mp he with ⟨hu,hparEq⟩ | ⟨hv,hparEq⟩
      · exact Or.inl ⟨by simpa [hu] using hne, by simpa [hu] using hparEq⟩
      · exact Or.inr ⟨by simpa [hv] using hne, by simpa [hv] using hparEq⟩
  have edgeInj : Set.InjOn (fun v => s(v,par v)) (↑((Finset.univ : Finset V).erase r) : Set V) := by
    intro u hu v hv e
    have hu' := (Finset.mem_erase.mp hu).1
    have hv' := (Finset.mem_erase.mp hv).1
    rcases Sym2.eq_iff.mp e with ⟨h,_⟩ | ⟨h,j⟩
    · exact h
    · have p := (props u hu').2
      have q := (props v hv').2
      rw [← h] at q
      rw [j] at p
      omega
  have htree : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      edgeImage, Finset.card_image_of_injOn edgeInj]
    have he := Finset.card_erase_add_one (Finset.mem_univ r)
    simpa using he
  have hnbr : nbr G r = nbr T r := by
    ext v
    simp only [mem_nbr]
    refine ⟨fun ha => ?_,fun h => hsub h⟩
    have hd : G.dist r v = 1 := dist_eq_one_iff_adj.mpr ha
    have he := (props v ha.ne.symm).2
    have hz : G.dist r (par v) = 0 := by omega
    exact Or.inr ⟨ha.ne.symm, (hc.dist_eq_zero_iff.mp hz).symm⟩
  exact ⟨par,T,hsub,htree,fun v h => (props v h).2,fun _ _ => Iff.rfl,hnbr⟩

#print axioms exists_bfs_tree
end GraffitiBFS
