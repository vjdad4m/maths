import Transfer180

/-! Weighted connected domination and the constrained rooted bound when the
independent set stays on one distance parity. The pendant construction adapts
Graffiti177.conDom_leaves; the core growth uses Graffiti177.grow_cover. -/
set_option warningAsError true
namespace Rooted180
open SimpleGraph Finset Graffiti177 Graffiti180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def markedBip (J : Finset V) : ℕ := by
  classical exact (univ.filter (fun S : Finset V => J ⊆ S ∧ TwoColor G S)).sup card

theorem marked_colors {A X J : Finset V} (sub : J ⊆ A) (ia : Indep G A)
    (ix : Indep G X) (dis : Disjoint A X) : A.card + X.card ≤ markedBip G J := by
  classical
  rw [← card_union_of_disjoint dis]
  exact le_sup (f := card) (mem_filter.mpr
    ⟨mem_univ _,sub.trans subset_union_left,A,X,dis,rfl,ia,ix⟩)

theorem weightedCore (D U : Finset V) (hc : Con G D)
    (hD : ∀ v ∉ D, Dominates G D v) : (U \ D).card ≤ weightedLeaves G U := by
  classical
  let par (v : V) : V := if h : v ∉ D then (hD v h).choose else v
  have hpar (v : V) (hv : v ∉ D) : par v ∈ D ∧ G.Adj v (par v) := by
    simpa [par,hv] using (hD v hv).choose_spec
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
    if h : v ∈ D then ⟨v,h⟩ else ⟨par v,(hpar v h).1⟩
  have reach (v : V) : H.Reachable v (lift v).1 := by
    by_cases h : v ∈ D
    · have he : (lift v).1 = v := by simp [lift,h]
      rw [he]
    · have he : (lift v).1 = par v := by simp [lift,h]
      rw [he]
      exact (show H.Adj v (par v) from ⟨(hpar v h).2, Or.inr (Or.inl ⟨h,rfl⟩)⟩).reachable
  have hH : H.Connected := by
    have : Nonempty V := ⟨(Classical.choice hc.nonempty).1⟩
    refine ⟨fun u v => ?_⟩
    exact (reach u).trans (((hc (lift u) (lift v)).map inc).trans (reach v).symm)
  obtain ⟨T, hT, ht⟩ := hH.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hT h).1
  have hleaf : (Finset.univ : Finset V) \ D ⊆ leaves T := by
    intro v hv
    have hn : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hpne : v ≠ par v := fun h => hn (h ▸ (hpar v hn).1)
    obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist v (par v)
    have hpos : 0 < p.length := by rw [hp]; exact ht.isConnected.pos_dist_of_ne hpne
    have hz : T.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
    have single {w : V} (h : T.Adj v w) : w = par v := by
      rcases (hT h).2 with h' | h' | h'
      · exact (hn h'.1).elim
      · exact h'.2.symm
      · exact (hn (h'.2 ▸ (hpar w h'.1).1)).elim
    have hs : T.neighborFinset v = {par v} := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      exact ⟨single, fun h => by rwa [h, ← single hz]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← T.card_neighborFinset_eq_degree,hs,Finset.card_singleton]
  have subset : U \ D ⊆ U ∩ leaves T := by
    intro v hv
    exact mem_inter.mpr ⟨(mem_sdiff.mp hv).1,hleaf (mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hv).2⟩)⟩
  exact (card_le_card subset).trans (le_sup (f := fun T => (U ∩ leaves T).card)
    (mem_filter.mpr ⟨mem_univ _,hTG,ht⟩))

theorem weighted_incident (S : Finset V) (hs : S.Nonempty) (hn : 1 < Fintype.card V)
    (jc : (incidentGraph G S).Connected) :
    (univ \ S).card + 1 ≤ weightedLeaves G (univ \ S) + compCount G S := by
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
  have leaf := weightedCore J D (univ \ S) cd dom
  have mono : weightedLeaves J (univ \ S) ≤ weightedLeaves G (univ \ S) := by
    apply Finset.sup_le
    intro T hT
    obtain ⟨le,tree⟩ := (mem_filter.mp hT).2
    exact le_sup (f := fun K => ((univ \ S) ∩ leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,fun _ _ e => (le e).1,tree⟩)
  have same : J.induce (S : Set V) = G.induce (S : Set V) := by
    ext x y
    exact ⟨fun e => e.1,fun e => ⟨e,Or.inl x.property⟩⟩
  have cs : compCount J S = compCount G S := by unfold compCount; rw [same]
  have d := card_sdiff_add_card_eq_card sub
  have n := card_sdiff_add_card_eq_card (subset_univ D)
  rw [card_univ] at n
  have eq : (univ \ S) \ D = univ \ D := by
    ext v
    simp only [mem_sdiff,mem_univ,true_and]
    exact ⟨And.right,fun h => ⟨fun mem => h (sub mem),h⟩⟩
  rw [eq] at leaf
  have p := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ] at p
  omega

/-- Independent sets confined to the complement of a connected incidence
support simultaneously pay the leaf and the marked bipartite terms. -/
theorem supported_color (S A J : Finset V) (hs : S.Nonempty) (hn : 1 < Fintype.card V)
    (jc : (incidentGraph G S).Connected) (dis : Disjoint A S) (ind : Indep G A)
    (mark : J ⊆ A) :
    1+A.card+(univ \ S).card ≤ weightedLeaves G (univ \ S) + markedBip G J := by
  obtain ⟨X,sub,ix,card⟩ := independentReps G S
  have leaf := weighted_incident G S hs hn jc
  have colors := marked_colors G mark ind ix (dis.mono_right sub)
  omega

/-- Both parity tests, with the overlap forced into the bipartite witness,
when every vertex of the given independent set belongs to the chosen class. -/
theorem confined_parity (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) (p : ℕ)
    (A : Finset V) (ind : Indep G A) :
    let P := univ.filter (fun x => G.dist x r % 2 = p)
    A ⊆ P → 1+A.card+P.card ≤ weightedLeaves G (eligible A P r) + markedBip G (A ∩ P) := by
  classical
  dsimp only
  let P := univ.filter (fun x => G.dist x r % 2 = p)
  let S := univ \ P
  intro sub
  change A ⊆ P at sub
  change 1+A.card+P.card ≤ weightedLeaves G (eligible A P r) + markedBip G (A ∩ P)
  have pm (v : V) : v ∈ P ↔ G.dist v r % 2 = p := by simp [P]
  have sm (v : V) : v ∈ S ↔ v ∉ P := by simp [S]
  have opposite : univ \ S = P := by ext v; simp [S]
  obtain ⟨T,st,tr,par⟩ := Graffiti169.exists_parity_tree G hc r
  have edge {v w : V} (e : T.Adj v w) : v ∈ S ∨ w ∈ S := by
    by_cases hv : v ∈ P
    · exact Or.inr ((sm _).mpr (fun hw => par e (((pm _).mp hv).trans ((pm _).mp hw).symm)))
    · exact Or.inl ((sm _).mpr hv)
  have connected := tr.isConnected.mono (show T ≤ incidentGraph G S from
    fun _ _ e => ⟨st e,edge e⟩)
  obtain ⟨v,rv⟩ := exists_adj T tr.isConnected hn r
  have nz : S.Nonempty := (edge rv).elim (fun h => ⟨r,h⟩) (fun h => ⟨v,h⟩)
  have bound (B : Finset V) (bp : B ⊆ P) (bi : Indep G B) (ab : A ⊆ B) :
      1+B.card+P.card ≤ weightedLeaves G P + markedBip G (A ∩ P) := by
    have dis : Disjoint B S := disjoint_left.mpr (fun v hb hs => ((sm v).mp hs) (bp hb))
    simpa only [opposite] using
      supported_color G S B (A ∩ P) nz hn connected dis bi (inter_subset_left.trans ab)
  have u : A ∪ P = P := union_eq_right.mpr sub
  by_cases er : r ∈ P
  · by_cases ar : r ∈ A
    · simpa [eligible,ar,er,u] using bound A sub ind (fun _ h => h)
    · have ip : insert r A ⊆ P := insert_subset er sub
      have na (v : V) (ha : v ∈ A) : ¬ G.Adj r v := by
        intro adj
        have hr := (pm _).mp er
        have hv := (pm _).mp (sub ha)
        rw [dist_self] at hr
        rw [dist_eq_one_iff_adj.mpr adj.symm] at hv
        omega
      have ia : Indep G (insert r A) := by
        intro v hv w hw ne adj
        rcases mem_insert.mp hv with rfl|va <;> rcases mem_insert.mp hw with rfl|wa
        · exact ne rfl
        · exact na _ wa adj
        · exact na _ va adj.symm
        · exact ind _ va _ wa ne adj
      have extra := bound _ ip ia (subset_insert _ _)
      rw [card_insert_of_not_mem ar] at extra
      have one : P \ P.erase r ⊆ {r} := by
        intro v hv
        by_contra h
        exact (mem_sdiff.mp hv).2 (mem_erase.mpr ⟨fun e => h (by simp [e]),(mem_sdiff.mp hv).1⟩)
      have loss := restrict_leaves G P (P.erase r)
      have cost := card_le_card one
      rw [card_singleton] at cost
      simp only [eligible,ar,false_and,if_false,u]
      omega
  · simpa [eligible,er,u] using bound A sub ind (fun _ h => h)

#print axioms confined_parity
#print axioms marked_colors
#print axioms weightedCore
#print axioms weighted_incident
#print axioms supported_color
end Rooted180
