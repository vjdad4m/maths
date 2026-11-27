import Proof169
import Proof177

/-! Partial results for Graffiti.pc 180. The parameter and the graph invariants
are those of the repository's 177 and 318 formalizations. -/
set_option warningAsError true
namespace Graffiti180
open SimpleGraph Finset Graffiti177 Graffiti318
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def oddSet (r : V) : Finset V := by
  classical exact univ.filter (fun x => G.dist x r % 2 ≠ 0)

omit [DecidableEq V] in
private theorem odd_mem (r x : V) : x ∈ oddSet G r ↔ G.dist x r % 2 ≠ 0 := by
  classical simp [oddSet]

omit [DecidableEq V] in
private theorem partition (r : V) :
    evenCount G r + (oddSet G r).card = Fintype.card V := by
  classical
  simpa only [evenCount,oddSet,dist_comm (u := r),card_univ] using
    (filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V))
      (p := fun x => G.dist x r % 2 = 0))

private theorem core_budget (r : V) (D : Finset V) (connected : Con G D)
    (dom : ∀ x ∉ D, Dominates G D x) (k : ℕ)
    (bound : D.card ≤ (oddSet G r).card + k) :
    evenCount G r ≤ maxLeaves G + k := by
  classical
  have leaf := conDom_leaves G D connected dom
  have cut := card_sdiff_add_card_eq_card (subset_univ D)
  rw [card_univ] at cut
  have part := partition G r
  omega

/-- A split graph satisfies the stronger pointwise leaf bound for every root. -/
theorem split_leaf_bound (hc : G.Connected) (hn : 1 < Fintype.card V)
    (A : Finset V) (ind : Indep G A)
    (clique : ∀ x ∉ A, ∀ y ∉ A, x ≠ y → G.Adj x y) (r : V) :
    evenCount G r ≤ maxLeaves G := by
  classical
  have other {x y} (hx : x ∈ A) (e : G.Adj x y) : y ∉ A :=
    fun hy => ind x hx y hy e.ne e
  let f (x : V) := if x ∈ A then (exists_adj G hc hn x).choose else x
  have fedge {x} (hx : x ∈ A) : G.Adj x (f x) := by
    simpa [f,hx] using (exists_adj G hc hn x).choose_spec
  have fout (x : V) : f x ∉ A := by
    by_cases hx : x ∈ A
    · exact other hx (fedge hx)
    · simp [f,hx]
  let D := (oddSet G r).image f
  obtain ⟨u,eu⟩ := exists_adj G hc hn r
  have oddU : u ∈ oddSet G r := (odd_mem G r u).mpr (by rw [dist_eq_one_iff_adj.mpr eu.symm]; decide)
  have center : f u ∈ D := mem_image_of_mem _ oddU
  have outside {x} (hx : x ∈ D) : x ∉ A := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact fout y
  have connected : Con G D := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨f u,center⟩,fun y => ?_⟩
    by_cases eq : f u = y.val
    · have he : (⟨f u,center⟩ : ↥(D : Set V)) = y := Subtype.ext eq
      rw [he]
    · exact (show (G.induce (D : Set V)).Adj ⟨f u,center⟩ y from
        clique _ (fout u) _ (outside y.property) eq).reachable
  have dom (v : V) (miss : v ∉ D) : Dominates G D v := by
    by_cases va : v ∈ A
    · by_cases vo : v ∈ oddSet G r
      · exact ⟨f v,mem_image_of_mem _ vo,fedge va⟩
      have oddNbr : ∃ w ∈ oddSet G r, G.Adj v w := by
        by_cases eq : v = r
        · subst v; exact ⟨u,oddU,eu⟩
        obtain ⟨w,e,dist⟩ := Graffiti169.exists_predecessor G hc r v eq
        have ev := mt (odd_mem G r v).mpr vo
        exact ⟨w,(odd_mem G r w).mpr (by omega),e⟩
      obtain ⟨w,wo,e⟩ := oddNbr
      have fw : f w = w := by simp [f,other va e]
      exact ⟨w,fw ▸ mem_image_of_mem f wo,e⟩
    · exact ⟨f u,center,clique v va _ (fout u) (fun eq => miss (eq ▸ center))⟩
  exact core_budget G r D connected dom 0 (by simpa [D] using
    (card_image_le : ((oddSet G r).image f).card ≤ (oddSet G r).card))

/-- A root of eccentricity at most three misses the leaf bound by at most one. -/
theorem leaf_bound_of_ecc_le_three (hc : G.Connected) (r : V)
    (rad : ∀ v, G.dist v r ≤ 3) : evenCount G r ≤ maxLeaves G + 1 := by
  classical
  let f (x : V) := if h : G.dist x r = 3 then
    (Graffiti169.exists_predecessor G hc r x
      (fun eq => by subst x; simp [dist_self] at h)).choose else x
  have parent {x} (hx : G.dist x r = 3) : G.Adj x (f x) ∧ G.dist (f x) r = 2 := by
    have h := (Graffiti169.exists_predecessor G hc r x
      (show x ≠ r from fun eq => by subst x; simp [dist_self] at hx)).choose_spec
    simp only [f,dif_pos hx]
    exact ⟨h.1,by omega⟩
  let D := insert r ((oddSet G r).image f)
  let N := insert r (G.neighborFinset r)
  have first {x} (hx : G.dist x r = 1) : x ∈ D := by
    apply mem_insert_of_mem
    exact mem_image.mpr ⟨x,(odd_mem G r x).mpr (by omega),by simp [f,hx]⟩
  have base : Con G N := con_of_neighbors G (con_single G r) (by simp [N]) (by
    intro v hv miss
    have ne : v ≠ r := by simpa using miss
    exact ⟨r,by simp,((G.mem_neighborFinset r _).mp ((mem_insert.mp hv).resolve_left ne)).symm⟩)
  have sub : N ⊆ D := by
    intro x hx
    rcases mem_insert.mp hx with rfl | h
    · exact mem_insert_self _ _
    · exact first (dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset r _).mp h).symm)
  have step {x} (hx : G.dist x r = 2) : ∃ y ∈ N, G.Adj x y := by
    obtain ⟨y,e,dist⟩ := Graffiti169.exists_predecessor G hc r x
      (show x ≠ r from fun eq => by subst x; simp [dist_self] at hx)
    exact ⟨y,mem_insert_of_mem ((G.mem_neighborFinset r y).mpr
      (dist_eq_one_iff_adj.mp (show G.dist y r = 1 by omega)).symm),e⟩
  have conn : Con G D := con_of_neighbors G base sub (by
    intro v hv miss
    rcases mem_insert.mp hv with eq | hi
    · subst v; exact (miss (mem_insert_self _ _)).elim
    obtain ⟨x,ox,rfl⟩ := mem_image.mp hi
    by_cases h : G.dist x r = 3
    · exact step (parent h).2
    · have odd := (odd_mem G r x).mp ox
      have lim := rad x
      have one : G.dist x r = 1 := by omega
      have hN : x ∈ N := mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp one).symm)
      exact (miss (by simpa [f,h] using hN)).elim)
  refine core_budget G r D conn ?_ 1 ?_
  · intro x miss
    have xr : x ≠ r := fun eq => miss (eq ▸ mem_insert_self _ _)
    have pos := hc.pos_dist_of_ne xr
    have lim := rad x
    by_cases three : G.dist x r = 3
    · have ox := (odd_mem G r x).mpr (show G.dist x r % 2 ≠ 0 by omega)
      exact ⟨f x,mem_insert_of_mem (mem_image_of_mem f ox),(parent three).1⟩
    by_cases two : G.dist x r = 2
    · obtain ⟨y,hy,e⟩ := step two
      exact ⟨y,sub hy,e⟩
    · exact (miss (first (by omega))).elim
  · exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1)

omit [Fintype V] in
private theorem pair_ind {x y : V} (e : ¬G.Adj x y) : Indep G {x,y} := by
  intro u hu v hv ne edge
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact ne rfl
  · exact e edge
  · exact e edge.symm
  · exact ne rfl

/-- Exact pointwise right-hand side at any root of eccentricity at most three. -/
theorem pointwise_ecc_le_three (hc : G.Connected) (hn : 1 < Fintype.card V)
    (r : V) (rad : ∀ v, G.dist v r ≤ 3) :
    1 + independence G + evenCount G r ≤ maxLeaves G + bipartiteNum G := by
  classical
  obtain ⟨A,ind,size⟩ := exists_max_indep G
  by_cases cl : ∀ x ∉ A, ∀ y ∉ A, x ≠ y → G.Adj x y
  · obtain ⟨w,z,ne⟩ := Fintype.one_lt_card_iff.mp hn
    obtain ⟨u,e⟩ := exists_adj G hc hn w
    have out : ∃ x, x ∉ A := by
      by_cases h : w ∈ A
      · exact ⟨u,fun hu => ind _ h _ hu e.ne e⟩
      · exact ⟨w,h⟩
    obtain ⟨x,hx⟩ := out
    have col := bip_bound G ind (show Indep G {x} by simp [Indep])
      (disjoint_singleton_right.mpr hx)
    have leaf := split_leaf_bound G hc hn A ind cl r
    simp only [card_singleton] at col
    omega
  · push_neg at cl
    obtain ⟨x,hx,y,hy,ne,na⟩ := cl
    have col := bip_bound G ind (pair_ind G na)
      (show Disjoint A {x,y} by simp [disjoint_insert_right,hx,hy])
    have leaf := leaf_bound_of_ecc_le_three G hc r rad
    simp only [card_pair ne] at col
    omega

/-- The full conclusion when a maximum-even root has eccentricity at most three. -/
theorem result180 (hc : G.Connected) (hn : 1 < Fintype.card V)
    (r : V) (maxAt : evenCount G r = maxEven G) (rad : ∀ v, G.dist v r ≤ 3) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  rw [← maxAt]
  exact pointwise_ecc_le_three G hc hn r rad

/-- All connected bipartite graphs, with bipartiteness expressed as a two-coloring. -/
theorem bipartite180 (hc : G.Connected) (hn : 1 < Fintype.card V)
    (hb : TwoColor G univ) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  letI := hc.nonempty
  obtain ⟨r,_,hr⟩ := exists_max_image univ (evenCount G) univ_nonempty
  have mx : maxEven G ≤ evenCount G r := Finset.sup_le hr
  have first := (Graffiti169.parity_bounds G hc hn r).1
  obtain ⟨T,sub,ht⟩ := hc.exists_isTree_le
  obtain ⟨A,ia,sz⟩ := exists_max_indep G
  have it : Short177.Indep T A := fun x hx y hy ne e => ia x hx y hy ne (sub e)
  have second := Graffiti169.tree_budget T ht hn A it
  have hl : (Short177.leaves T).card ≤ Short177.maxLeaves G :=
    le_sup (f := fun K => (Short177.leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,ht⟩)
  have hb' : Fintype.card V ≤ bipartiteNum G := by
    simpa using (le_sup (f := Finset.card) (s := univ.filter (TwoColor G))
      (mem_filter.mpr ⟨mem_univ _,hb⟩) : (univ : Finset V).card ≤ bipartiteNum G)
  change 1 + independence G + maxEven G ≤ Short177.maxLeaves G + bipartiteNum G
  omega

/-- Direct numerical comparison of the right-hand sides of 177 and 180. -/
theorem of_second_degree [DecidableRel G.Adj] (hc : G.Connected) (hn : 1 < Fintype.card V)
    (h : maxEven G + 1 ≤ Short177.independence G + Short177.secondDegree G) :
    1 + Short177.independence G + maxEven G ≤ Short177.maxLeaves G + Short177.bipartiteNum G := by
  have := Short177.conjecture177 G hc hn
  omega

/-- The sharper parity bound from 169 pays the order of an odd-cycle transversal
whenever the maximum even count exceeds independence by at least that order. -/
theorem of_transversal (hc : G.Connected) (hn : 1 < Fintype.card V)
    (cover : Fintype.card V + independence G ≤ maxEven G + bipartiteNum G) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  classical
  letI := hc.nonempty
  obtain ⟨r,_,hr⟩ := exists_max_image univ (evenCount G) univ_nonempty
  have mx : maxEven G ≤ evenCount G r := Finset.sup_le hr
  have parity := (Graffiti169.parity_bounds G hc hn r).1
  change 1 + independence G + maxEven G ≤ Short177.maxLeaves G + bipartiteNum G
  omega

/-- In particular, 180 holds whenever the minimum number of vertices whose
deletion makes the graph bipartite is at most the second-smallest degree. -/
theorem small_transversal [DecidableRel G.Adj] (hc : G.Connected) (hn : 1 < Fintype.card V)
    (cover : Fintype.card V ≤ bipartiteNum G + Short177.secondDegree G) :
    1 + independence G + maxEven G ≤ maxLeaves G + bipartiteNum G := by
  by_cases h : maxEven G + 1 ≤ independence G + Short177.secondDegree G
  · exact of_second_degree G hc hn h
  · apply of_transversal G hc hn
    omega

#print axioms of_transversal
#print axioms small_transversal
#print axioms split_leaf_bound
#print axioms pointwise_ecc_le_three
#print axioms result180
#print axioms bipartite180
#print axioms of_second_degree
end Graffiti180
