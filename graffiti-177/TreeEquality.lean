import Proof177

/-! # Equality in Graffiti.pc 177 on trees

The definitions of all four graph invariants are imported directly from
the original formalization. The edge count and the two vertex contributions
in the slack identity are nonnegative natural numbers. -/

open SimpleGraph Finset
open scoped BigOperators

namespace Graffiti177.TreeEquality

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- The original edges with both endpoints in the specified vertex set. -/
noncomputable def insideEdges (B : Finset V) : Finset (Sym2 V) := by
  classical exact T.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B)

private lemma insideEdges_eq_empty_iff (B : Finset V) :
    insideEdges T B = ∅ ↔ Indep T B := by
  classical
  constructor
  · intro he u hu v hv _ hadj
    have hm : s(u,v) ∈ insideEdges T B := by
      refine mem_filter.mpr ⟨mem_edgeFinset.mpr hadj, ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption
    simp [he] at hm
  · intro hi
    apply eq_empty_iff_forall_not_mem.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨hE, hB⟩ := mem_filter.mp he
      have hadj : T.Adj u v := mem_edgeFinset.mp hE
      exact hi u (hB u (by simp)) v (hB v (by simp)) hadj.ne hadj

/-- An independent set counts each incident edge once in its degree sum. -/
private lemma count_edges {A : Finset V} (hi : Indep T A) :
    (∑ v ∈ A, T.degree v) + (insideEdges T (univ \ A)).card = T.edgeFinset.card := by
  classical
  let E := A.biUnion (fun v => T.incidenceFinset v)
  have hdis : (↑A : Set V).PairwiseDisjoint (fun v => T.incidenceFinset v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e h₁ h₂
    change e ∈ T.incidenceFinset u at h₁
    change e ∈ T.incidenceFinset v at h₂
    rw [T.incidenceFinset_eq_filter] at h₁ h₂
    obtain ⟨he, hu'⟩ := mem_filter.mp h₁
    obtain ⟨_, hv'⟩ := mem_filter.mp h₂
    rw [(Sym2.mem_and_mem_iff huv).mp ⟨hu', hv'⟩] at he
    exact hi u hu v hv huv (mem_edgeFinset.mp he)
  have hsize : E.card = ∑ v ∈ A, T.degree v := by
    simp [E, card_biUnion hdis]
  have hsub : E ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp he
    rw [T.incidenceFinset_eq_filter] at hv
    exact (mem_filter.mp hv).1
  have hrest : insideEdges T (univ \ A) = T.edgeFinset \ E := by
    ext e
    constructor
    · intro h
      obtain ⟨he, hb⟩ := mem_filter.mp h
      refine mem_sdiff.mpr ⟨he, ?_⟩
      intro hE
      obtain ⟨v, hv, hv'⟩ := mem_biUnion.mp hE
      rw [T.incidenceFinset_eq_filter] at hv'
      exact (mem_sdiff.mp (hb v (mem_filter.mp hv').2)).2 hv
    · intro h
      obtain ⟨he, hE⟩ := mem_sdiff.mp h
      refine mem_filter.mpr ⟨he, fun v hv => mem_sdiff.mpr ⟨mem_univ _, ?_⟩⟩
      intro ha
      apply hE
      apply mem_biUnion.mpr
      exact ⟨v, ha, by rw [T.incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨he, hv⟩⟩
  rw [← hsize, hrest, card_sdiff hsub]
  have := card_le_card hsub
  omega

omit [DecidableEq V] in
private lemma mem_leaf (v : V) : v ∈ leaves T ↔ T.degree v = 1 := by
  classical
  simp [leaves, SimpleGraph.degree, SimpleGraph.neighborFinset]

/-- Additive form of the paper's slack identity. Natural subtraction in the
summand makes the contribution of vertices of degree one or two zero. -/
theorem degree_sum_slack (ht : T.IsTree) (hn : 1 < Fintype.card V)
    {A : Finset V} (hi : Indep T A) :
    Fintype.card V + (leaves T).card =
      2 * A.card + 1 + (insideEdges T (univ \ A)).card +
        (leaves T \ A).card + ∑ v ∈ A, (T.degree v - 2) := by
  classical
  have hpoint (v : V) :
      T.degree v + (if v ∈ leaves T then 1 else 0) = 2 + (T.degree v - 2) := by
    have hp := (T.degree_pos_iff_exists_adj v).mpr (exists_adj T ht.isConnected hn v)
    by_cases hl : v ∈ leaves T
    · simp [hl, (mem_leaf T v).mp hl]
    · have hd : T.degree v ≠ 1 := fun h => hl ((mem_leaf T v).mpr h)
      simp [hl]
      omega
  have hs := sum_congr (show A = A from rfl) (fun v _ => hpoint v)
  have hcount : (∑ v ∈ A, (if v ∈ leaves T then 1 else 0 : ℕ)) =
      ((leaves T) ∩ A).card := by
    simp [Finset.inter_comm, filter_mem_eq_inter]
  rw [sum_add_distrib, sum_add_distrib, hcount] at hs
  simp only [sum_const, smul_eq_mul] at hs
  have hleaf := card_sdiff_add_card_inter (leaves T) A
  have hedge := count_edges T hi
  have htree := ht.card_edgeFinset
  omega

/-- A tree has just one spanning tree. -/
private lemma maxLeaves_of_tree (ht : T.IsTree) : maxLeaves T = (leaves T).card := by
  classical
  unfold maxLeaves
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    obtain ⟨hST, hs⟩ := (mem_filter.mp hS).2
    have h₁ := ht.card_edgeFinset
    have h₂ := hs.card_edgeFinset
    have heq : S = T := edgeFinset_inj.mp (eq_of_subset_of_card_le (edgeFinset_mono hST) (by omega))
    simp [heq]
  · exact le_sup (f := fun S => (leaves S).card) (mem_filter.mpr ⟨mem_univ T, le_rfl, ht⟩)

omit [DecidableRel T.Adj] in
/-- Root-path lengths at the ends of an edge differ by one. -/
private lemma exists_bipartition (ht : T.IsTree) :
    ∃ A : Finset V, Indep T A ∧ Indep T (univ \ A) := by
  classical
  obtain ⟨r⟩ := ht.isConnected.nonempty
  choose p hp huniq using (ht.existsUnique_path · r)
  have hstep {x y : V} (h : T.Adj x y) :
      (p x).length = (p y).length + 1 ∨ (p y).length = (p x).length + 1 := by
    by_cases hy : y ∈ (p x).support
    · left
      have hpre : (p x).takeUntil y hy = .cons h .nil :=
        (ht.existsUnique_path _ _).unique ((hp _).takeUntil _) (by simp [h.ne])
      have hlen := congrArg Walk.length (Walk.take_spec (p x) hy)
      simpa [hpre, huniq _ _ ((hp _).dropUntil hy), Nat.add_comm] using hlen.symm
    · right
      have heq := huniq y (.cons h.symm (p x)) ((Walk.cons_isPath_iff _ _).mpr ⟨hp _, hy⟩)
      simpa using (congrArg Walk.length heq).symm
  let A := univ.filter (fun x => (p x).length % 2 = 0)
  refine ⟨A, ?_, ?_⟩
  · intro x hx y hy _ h
    have h₁ := (mem_filter.mp hx).2
    have h₂ := (mem_filter.mp hy).2
    rcases hstep h with h | h <;> omega
  · intro x hx y hy _ h
    have h₁ : (p x).length % 2 ≠ 0 := fun he => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_univ _, he⟩)
    have h₂ : (p y).length % 2 ≠ 0 := fun he => (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, he⟩)
    rcases hstep h with h | h <;> omega

omit [DecidableRel T.Adj] in
private lemma bipartiteNum_of_tree (ht : T.IsTree) : bipartiteNum T = Fintype.card V := by
  classical
  obtain ⟨A, ha, hb⟩ := exists_bipartition T ht
  have htwo : TwoColor T univ := ⟨A, univ \ A, disjoint_sdiff, by simp, ha, hb⟩
  apply le_antisymm
  · exact Finset.sup_le (fun X _ => card_le_univ X)
  · simpa using (le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, htwo⟩) :
      (univ : Finset V).card ≤ bipartiteNum T)

private lemma secondDegree_of_tree (ht : T.IsTree) (hn : 1 < Fintype.card V) :
    secondDegree T = 1 := by
  classical
  have hpoint (v : V) : 2 ≤ T.degree v + if v ∈ leaves T then 1 else 0 := by
    have hp := (T.degree_pos_iff_exists_adj v).mpr (exists_adj T ht.isConnected hn v)
    by_cases hl : v ∈ leaves T
    · simp [hl, (mem_leaf T v).mp hl]
    · have hd : T.degree v ≠ 1 := fun h => hl ((mem_leaf T v).mpr h)
      simp [hl]
      omega
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  have hleaf : (∑ v : V, (if v ∈ leaves T then 1 else 0 : ℕ)) = (leaves T).card := by simp
  rw [sum_add_distrib, T.sum_degrees_eq_twice_card_edges, hleaf] at hsum
  simp only [sum_const, card_univ, smul_eq_mul] at hsum
  have htree := ht.card_edgeFinset
  have htwo : 1 < (leaves T).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp htwo
  apply le_antisymm _ (secondDegree_properties T ht.isConnected hn).1
  apply Nat.sInf_le
  exact ⟨u, v, huv, by simp [(mem_leaf T u).mp hu, (mem_leaf T v).mp hv]⟩

/-- In the exact original invariants, the slack is the sum of the three
obstructions exhibited by any maximum independent set. -/
theorem invariant_slack (ht : T.IsTree) (hn : 1 < Fintype.card V)
    {A : Finset V} (hi : Indep T A) (hmax : A.card = independence T) :
    maxLeaves T + bipartiteNum T - (2 * independence T + secondDegree T) =
      (insideEdges T (univ \ A)).card + (leaves T \ A).card +
        ∑ v ∈ A.filter (fun v => 3 ≤ T.degree v), (T.degree v - 2) := by
  classical
  have hfilter : (∑ v ∈ A.filter (fun v => 3 ≤ T.degree v), (T.degree v - 2)) =
      ∑ v ∈ A, (T.degree v - 2) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · omega
  rw [maxLeaves_of_tree T ht, bipartiteNum_of_tree T ht, secondDegree_of_tree T ht hn, hfilter]
  have h := degree_sum_slack T ht hn hi
  omega

/-- The iff uses the exact four invariants of the original #177 statement.
The displayed independent sets partition all vertices. -/
theorem equality_iff (ht : T.IsTree) (hn : 3 ≤ Fintype.card V) :
    maxLeaves T + bipartiteNum T = 2 * independence T + secondDegree T ↔
      ∃ A : Finset V, Indep T A ∧ Indep T (univ \ A) ∧
        (∀ v, T.degree v = 1 → v ∈ A) ∧ (∀ v, 3 ≤ T.degree v → v ∉ A) := by
  classical
  have hn' : 1 < Fintype.card V := by omega
  rw [maxLeaves_of_tree T ht, bipartiteNum_of_tree T ht, secondDegree_of_tree T ht hn']
  constructor
  · intro he
    obtain ⟨A, ha, hcard⟩ := exists_max_indep T
    have hid := degree_sum_slack T ht hn' ha
    have hedge : (insideEdges T (univ \ A)).card = 0 := by omega
    have hleaf : (leaves T \ A).card = 0 := by omega
    have hbranch : ∑ v ∈ A, (T.degree v - 2) = 0 := by omega
    refine ⟨A, ha, (insideEdges_eq_empty_iff T _).mp (card_eq_zero.mp hedge), ?_, ?_⟩
    · intro v hv
      by_contra hnA
      have hm := mem_sdiff.mpr ⟨(mem_leaf T v).mpr hv, hnA⟩
      simp [card_eq_zero.mp hleaf] at hm
    · intro v hd hv
      have hle := single_le_sum (f := fun v => T.degree v - 2) (fun _ _ => Nat.zero_le _) hv
      dsimp only at hle
      rw [hbranch] at hle
      omega
  · rintro ⟨A, ha, hb, hl, hd⟩
    have hid := degree_sum_slack T ht hn' ha
    rw [(insideEdges_eq_empty_iff T _).mpr hb] at hid
    have he : leaves T \ A = ∅ := sdiff_eq_empty_iff_subset.mpr (fun v hv => hl v ((mem_leaf T v).mp hv))
    have hs : ∑ v ∈ A, (T.degree v - 2) = 0 := by
      apply sum_eq_zero
      intro v hv
      have h : ¬3 ≤ T.degree v := fun hd' => hd v hd' hv
      exact Nat.sub_eq_zero_of_le (by omega)
    simp [he, hs] at hid
    obtain ⟨M, hm, hM⟩ := exists_max_indep T
    have hmax := degree_sum_slack T ht hn' hm
    have hle := indep_card_le T ha
    omega

#print axioms degree_sum_slack
#print axioms invariant_slack
#print axioms equality_iff

end Graffiti177.TreeEquality
