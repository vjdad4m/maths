import OddComponents180

/-! The root correction in the weighted block test, and a witness for components
of an arbitrary support that meet the complement of a maximum independent set. -/
set_option warningAsError true
namespace Rooted180
open SimpleGraph Finset Graffiti177 Graffiti318 Graffiti180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def weightedLeaves (U : Finset V) : ℕ := by
  classical
  exact ((univ : Finset (SimpleGraph V)).filter (fun T => T ≤ G ∧ T.IsTree)).sup
    (fun T => (U ∩ leaves T).card)

noncomputable def eligible (A P : Finset V) (r : V) : Finset V :=
  if r ∈ A ∧ r ∈ P then A ∪ P else (A ∪ P).erase r

omit [Fintype V] in
private theorem leaf_union (A P F : Finset V) (r : V) :
    (A ∩ F).card + (P ∩ F).card ≤ 2 * (eligible A P r ∩ F).card + 1 := by
  classical
  let W := eligible A P r ∩ F
  have cover (B : Finset V) (h : B ⊆ A ∪ P) :
      B ∩ F ⊆ insert r W := by
    intro v hv
    by_cases e : v = r
    · simp [e]
    · apply mem_insert_of_mem
      exact mem_inter.mpr ⟨by
        have hv' := h (mem_inter.mp hv).1
        unfold eligible
        split
        · exact hv'
        · exact mem_erase.mpr ⟨e,hv'⟩,(mem_inter.mp hv).2⟩
  have bound (B : Finset V) (h : B ⊆ A ∪ P) :
      (B ∩ F).card ≤ W.card+1 :=
    (card_le_card (cover B h)).trans (card_insert_le _ _)
  have strict (B : Finset V) (h : B ⊆ A ∪ P) (hr : r ∉ B) :
      (B ∩ F).card ≤ W.card := by
    apply card_le_card
    intro v hv
    exact (mem_insert.mp (cover B h hv)).resolve_left
      (fun eq => hr (eq ▸ (mem_inter.mp hv).1))
  have a := bound A subset_union_left
  have p := bound P subset_union_right
  change (A ∩ F).card + (P ∩ F).card ≤ 2 * W.card + 1
  by_cases h : r ∈ A ∧ r ∈ P
  · have aa : A ∩ F ⊆ W := by
      intro v hv
      exact mem_inter.mpr ⟨by simpa [eligible,h] using
        (Or.inl (mem_inter.mp hv).1 : v ∈ A ∨ v ∈ P),(mem_inter.mp hv).2⟩
    have pp : P ∩ F ⊆ W := by
      intro v hv
      exact mem_inter.mpr ⟨by simpa [eligible,h] using
        (Or.inr (mem_inter.mp hv).1 : v ∈ A ∨ v ∈ P),(mem_inter.mp hv).2⟩
    have := card_le_card aa
    have := card_le_card pp
    omega
  · by_cases ar : r ∈ A
    · have := strict P subset_union_right (fun pr => h ⟨ar,pr⟩)
      omega
    · have := strict A subset_union_left ar
      omega

/-- The local block inequality with graph order on the left in place of b.
Its hypotheses permit arbitrary adjacency within distance layers. -/
theorem weighted_order (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) (p : ℕ)
    (A : Finset V) (ind : Indep G A) :
    let P := univ.filter (fun x => G.dist x r % 2 = p)
    A.card + P.card + 1 ≤ Fintype.card V + weightedLeaves G (eligible A P r) := by
  classical
  dsimp only
  let P := univ.filter (fun x => G.dist x r % 2 = p)
  obtain ⟨T,sub,tree,par⟩ := Graffiti169.exists_parity_tree G hc r
  have ai : Short177.Indep T A := fun x hx y hy ne e => ind x hx y hy ne (sub e)
  have pi : Short177.Indep T P := by
    intro x hx y hy _ e
    exact par e ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  have a := Graffiti169.tree_budget_class T tree hn A ai
  have b := Graffiti169.tree_budget_class T tree hn P pi
  have c := leaf_union A P (leaves T) r
  have bound : (eligible A P r ∩ leaves T).card ≤ weightedLeaves G (eligible A P r) :=
    le_sup (f := fun T => (eligible A P r ∩ leaves T).card)
      (mem_filter.mpr ⟨mem_univ _,sub,tree⟩)
  change 2 * A.card + 1 ≤ Fintype.card V + (A ∩ leaves T).card at a
  change 2 * P.card + 1 ≤ Fintype.card V + (P ∩ leaves T).card at b
  change A.card + P.card + 1 ≤ Fintype.card V + weightedLeaves G (eligible A P r)
  omega

theorem weighted_bipartite (hc : G.Connected) (hn : 1 < Fintype.card V)
    (hb : TwoColor G univ) (r : V) (p : ℕ) (A : Finset V) (ind : Indep G A) :
    let P := univ.filter (fun x => G.dist x r % 2 = p)
    A.card + P.card + 1 ≤ bipartiteNum G + weightedLeaves G (eligible A P r) := by
  classical
  have bn : Fintype.card V ≤ bipartiteNum G := by
    simpa using (Finset.le_sup (f := Finset.card) (s := univ.filter (TwoColor G))
      (mem_filter.mpr ⟨mem_univ _,hb⟩) : (univ : Finset V).card ≤ bipartiteNum G)
  exact (weighted_order G hc hn r p A ind).trans (Nat.add_le_add_right bn _)

noncomputable def exceptional (A S : Finset V) : Finset V := by
  classical exact S.filter (fun x => x ∈ A ∧ ∀ y ∈ S, ¬G.Adj x y)

/-- Pick one representative outside A whenever the component offers one.
Every representative in A must then be isolated in S. -/
theorem charge_components (A S : Finset V) (ind : Indep G A) :
    A.card + compCount G S ≤ bipartiteNum G + (exceptional G A S).card := by
  classical
  let H := G.induce (S : Set V)
  letI : Finite H.ConnectedComponent := Finite.of_surjective H.connectedComponentMk
    (fun c => c.exists_rep)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let good (c : H.ConnectedComponent) := ∃ x : (S : Set V), H.connectedComponentMk x = c ∧ x.val ∉ A
  let rep (c : H.ConnectedComponent) : (S : Set V) :=
    if h : good c then Classical.choose h else Classical.choose c.exists_rep
  have hr (c) : H.connectedComponentMk (rep c) = c := by
    by_cases h : good c
    · simpa [rep,h] using (Classical.choose_spec h).1
    · simpa [rep,h] using Classical.choose_spec c.exists_rep
  let f (c : H.ConnectedComponent) : V := (rep c).val
  let R := univ.image f
  have injective : Function.Injective f := by
    intro c d eq
    have e : rep c = rep d := Subtype.ext eq
    exact (hr c).symm.trans ((congrArg H.connectedComponentMk e).trans (hr d))
  have card : R.card = compCount G S := by
    simp [R,card_image_of_injOn injective.injOn,compCount,H,Nat.card_eq_fintype_card]
  have ir : Indep G (R \ A) := by
    intro x hx y hy ne adj
    obtain ⟨c,_,cx⟩ := mem_image.mp (mem_sdiff.mp hx).1
    obtain ⟨d,_,dy⟩ := mem_image.mp (mem_sdiff.mp hy).1
    have e : H.Adj (rep c) (rep d) := by change G.Adj (f c) (f d); rwa [cx,dy]
    have same := ConnectedComponent.sound e.reachable
    rw [hr c,hr d] at same
    exact ne (cx.symm.trans ((congrArg f same).trans dy))
  have paid : R ∩ A ⊆ exceptional G A S := by
    intro x hx
    obtain ⟨c,_,cx⟩ := mem_image.mp (mem_inter.mp hx).1
    have xa := (mem_inter.mp hx).2
    have ng : ¬good c := by
      intro h
      have out : f c ∉ A := by simpa [f,rep,h] using (Classical.choose_spec h).2
      exact out (cx ▸ xa)
    refine mem_filter.mpr ⟨cx ▸ (rep c).property,xa,?_⟩
    intro y hy e
    have edge : H.Adj (rep c) ⟨y,hy⟩ := by change G.Adj (f c) y; rwa [cx]
    apply ng
    exact ⟨⟨y,hy⟩,(ConnectedComponent.sound edge.reachable).symm.trans (hr c),
      fun ya => ind x xa y ya e.ne e⟩
  have bound := bip_bound G ind ir (disjoint_sdiff_self_right : Disjoint A (R \ A))
  have count := card_sdiff_add_card_inter R A
  have ex := card_le_card paid
  omega

theorem of_component_charge (hn : 1 < Fintype.card V) (r : V)
    (mx : evenCount G r = maxEven G) (A S : Finset V) (ind : Indep G A)
    (maxA : A.card = independence G) (nz : S.Nonempty) (con : (incidentGraph G S).Connected)
    (pay : S.card + (exceptional G A S).card ≤ (oddSet G r).card) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  have cc := charge_components G A S ind
  apply of_odd_support G hn r mx S nz con
  omega

#print axioms weighted_order
#print axioms weighted_bipartite
#print axioms charge_components
#print axioms of_component_charge
end Rooted180

