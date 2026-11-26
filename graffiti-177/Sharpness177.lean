import Proof177

/-! # Sharpness families for Graffiti.pc 177

The hypotheses describe graphs on an arbitrary finite vertex type. In a
split join, every vertex outside the designated independent set is universal.
In a complete bipartite graph, adjacency is precisely membership in opposite
parts. No particular labeling of the vertices is required. -/

open SimpleGraph Finset
open scoped BigOperators

namespace Graffiti177.Sharpness
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private lemma leaf_mem {T : SimpleGraph V} [DecidableRel T.Adj] (v : V) :
    v ∈ leaves T ↔ T.degree v = 1 := by
  classical simp [leaves, SimpleGraph.degree, SimpleGraph.neighborFinset]

omit [DecidableRel G.Adj] in
private lemma leaf_upper (hn : 3 ≤ Fintype.card V) : maxLeaves G ≤ Fintype.card V - 1 := by
  classical
  apply Finset.sup_le
  intro T hT
  have ht : T.IsTree := (mem_filter.mp hT).2.2
  have hlt : (leaves T).card < Fintype.card V := by
    apply lt_of_le_of_ne (card_le_univ _)
    intro he
    have hall := (leaves T).eq_univ_of_card he
    have hd (v : V) : T.degree v = 1 :=
      (leaf_mem v).mp (by rw [hall]; exact mem_univ _)
    have hs := T.sum_degrees_eq_twice_card_edges
    simp only [hd, sum_const, card_univ, smul_eq_mul, Nat.mul_one] at hs
    have := ht.card_edgeFinset
    omega
  omega

/-- With one possible exception, a lower bound on degrees also bounds the
second entry in the ordered degree sequence. -/
private lemma second_ge (hn : 1 < Fintype.card V) (k : ℕ) (z : V)
    (hdeg : ∀ v ≠ z, k ≤ G.degree v) : k ≤ secondDegree G := by
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨u,v,huv,he⟩ := Nat.sInf_mem
    (show {s | ∃ x y : V, x ≠ y ∧ max (G.degree x) (G.degree y) = s}.Nonempty from
      ⟨_,a,b,hab,rfl⟩)
  change k ≤ sInf _
  rw [← he]
  by_cases hz : u = z
  · exact (hdeg v (by subst z; exact huv.symm)).trans (le_max_right _ _)
  · exact (hdeg u hz).trans (le_max_left _ _)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma connected_of_universal (c : V) (hc : ∀ v ≠ c, G.Adj c v) : G.Connected := by
  haveI : Nonempty V := ⟨c⟩
  have hr (v : V) : G.Reachable c v := by
    by_cases he : v = c
    · subst v; rfl
    · exact (hc v he).reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

private lemma degree_universal (c : V) (hc : ∀ v ≠ c, G.Adj c v) :
    G.degree c = Fintype.card V - 1 := by
  classical
  have he : G.neighborFinset c = univ.erase c := by
    ext v
    simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
    exact ⟨fun h => h.ne.symm, hc v⟩
  rw [← G.card_neighborFinset_eq_degree, he, card_erase_of_mem (mem_univ _), card_univ]

/-- Joining a nonempty clique to an independent set of at least two vertices
attains equality. All vertices outside A are adjacent to every other vertex. -/
theorem split_join {A : Finset V} (hq : 2 ≤ A.card) (hi : Indep G A) (hc : ∃ v, v ∉ A)
    (hu : ∀ x ∉ A, ∀ y ≠ x, G.Adj x y) :
    (maxLeaves G + bipartiteNum G = 2 * independence G + secondDegree G) ∧
      maxLeaves G = Fintype.card V - 1 ∧ bipartiteNum G = A.card + 1 ∧
      independence G = A.card ∧ secondDegree G = Fintype.card V - A.card := by
  classical
  obtain ⟨c,hc⟩ := hc
  have hlt : A.card < Fintype.card V := by
    apply lt_of_le_of_ne (card_le_univ _)
    exact fun h => hc (by rw [A.eq_univ_of_card h]; exact mem_univ _)
  have hn : 3 ≤ Fintype.card V := by omega
  have hdeg (v : V) : Fintype.card V - A.card ≤ G.degree v := by
    by_cases hv : v ∈ A
    · have hs : univ \ A ⊆ G.neighborFinset v := by
        intro x hx
        have hxa := (mem_sdiff.mp hx).2
        exact (G.mem_neighborFinset _ _).mpr (hu x hxa v (fun e => hxa (e ▸ hv))).symm
      simpa [card_univ_diff] using card_le_card hs
    · rw [degree_universal G v (hu v hv)]
      omega
  have hs := second_ge G (by omega) _ c (fun v _ => hdeg v)
  have hα := indep_card_le G hi
  have hL := leaf_upper G hn
  have small {X : Finset V} (hx : Indep G X) (hsub : ¬ X ⊆ A) : X.card ≤ 1 := by
    obtain ⟨u,huX,huA⟩ := not_subset.mp hsub
    have subs : X ⊆ {u} := by
      intro v hv
      apply mem_singleton.mpr
      by_contra hne
      exact hx u huX v hv (Ne.symm hne) (hu u huA v hne)
    simpa using card_le_card subs
  have sized {X : Finset V} (hx : Indep G X) : X.card ≤ A.card := by
    by_cases h : X ⊆ A
    · exact card_le_card h
    · have := small hx h; omega
  have hB : bipartiteNum G ≤ A.card + 1 := by
    apply Finset.sup_le
    intro W hW
    obtain ⟨X,Y,dis,rfl,hx,hy⟩ := (mem_filter.mp hW).2
    by_cases xA : X ⊆ A
    · by_cases yA : Y ⊆ A
      · exact (card_le_card (union_subset xA yA)).trans (by omega)
      · rw [card_union_of_disjoint dis]
        have := small hy yA
        have := sized hx
        omega
    · rw [card_union_of_disjoint dis]
      have := small hx xA
      have := sized hy
      omega
  have h := conjecture177 G (connected_of_universal G c (hu c hc)) (by omega)
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Complete graphs of order at least three attain equality. -/
theorem complete (hn : 3 ≤ Fintype.card V) (hg : ∀ u v : V, u ≠ v → G.Adj u v) :
    (maxLeaves G + bipartiteNum G = 2 * independence G + secondDegree G) ∧
      maxLeaves G = Fintype.card V - 1 ∧ bipartiteNum G = 2 ∧
      independence G = 1 ∧ secondDegree G = Fintype.card V - 1 := by
  classical
  obtain ⟨c,d,hcd⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  have cone (v : V) : ∀ w ≠ v, G.Adj v w := fun w h => hg v w h.symm
  have hL := leaf_upper G hn
  have ha := indep_card_le G (A := {c}) (by simp [Indep])
  have hs := second_ge G (by omega) (Fintype.card V - 1) c
    (fun v _ => (degree_universal G v (cone v)).ge)
  have hB : bipartiteNum G ≤ 2 := by
    have small (X : Finset V) (hx : Indep G X) : X.card ≤ 1 :=
      card_le_one.mpr (fun u hu v hv => by_contra (fun h => hx u hu v hv h (hg u v h)))
    apply Finset.sup_le
    intro W hW
    obtain ⟨X,Y,dis,rfl,hx,hy⟩ := (mem_filter.mp hW).2
    rw [card_union_of_disjoint dis]
    have := small X hx
    have := small Y hy
    omega
  simp only [card_singleton] at ha
  have h := conjecture177 G (connected_of_universal G c (cone c)) (by omega)
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- A clique with a single pendant vertex. Here n = p+2, the pendant is
the unique vertex of minimum degree, and the second degree is n-2. -/
theorem pendant_clique (hn : 4 ≤ Fintype.card V) {l c : V} (hlc : l ≠ c)
    (hpend : ∀ v, G.Adj l v ↔ v = c)
    (hcl : ∀ u ≠ l, ∀ v ≠ l, u ≠ v → G.Adj u v) :
    (maxLeaves G + bipartiteNum G = 2 * independence G + secondDegree G) ∧
      secondDegree G = Fintype.card V - 2 ∧ G.degree l = 1 ∧
      (∀ v ≠ l, G.degree l < G.degree v) ∧
      maxLeaves G = Fintype.card V - 1 ∧ bipartiteNum G = 3 ∧ independence G = 2 := by
  classical
  have deg₁ : G.degree l = 1 := by
    have he : G.neighborFinset l = {c} := by ext v; simp [hpend]
    rw [← G.card_neighborFinset_eq_degree, he, card_singleton]
  have hdeg (v : V) (hv : v ≠ l) : Fintype.card V - 2 ≤ G.degree v := by
    have hsub : univ \ {v,l} ⊆ G.neighborFinset v := by
      intro w hw
      have hw' : w ≠ v ∧ w ≠ l := by simpa using hw
      exact (G.mem_neighborFinset _ _).mpr (hcl _ hv _ hw'.2 hw'.1.symm)
    simpa [card_univ_diff, hv] using card_le_card hsub
  have hall : ∃ w : V, w ∉ ({l,c} : Finset V) := by
    by_contra! he
    have hcard := card_le_card (show univ ⊆ ({l,c} : Finset V) from fun w _ => he w)
    simp [hlc] at hcard
    omega
  obtain ⟨w,hw⟩ := hall
  have hw' : w ≠ l ∧ w ≠ c := by simpa using hw
  have degw : G.degree w = Fintype.card V - 2 := by
    have he : G.neighborFinset w = univ \ {w,l} := by
      ext u
      simp only [mem_neighborFinset, mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and,
        not_or]
      exact ⟨fun h => ⟨h.ne.symm, fun e => hw'.2 ((hpend w).mp (e ▸ h.symm))⟩,
        fun h => hcl _ hw'.1 _ h.2 (Ne.symm h.1)⟩
    rw [← G.card_neighborFinset_eq_degree, he, card_univ_diff, card_pair hw'.1]
  have sig : secondDegree G = Fintype.card V - 2 := by
    apply le_antisymm _ (second_ge G (by omega) _ l hdeg)
    exact Nat.sInf_le ⟨l,w,hw'.1.symm,by rw [deg₁, degw, max_eq_right (by omega)]⟩
  have hi : Indep G {l,w} := by
    intro a ha b hb he hab
    have hnon : ¬G.Adj l w := fun h => hw'.2 ((hpend w).mp h)
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact he rfl
    · exact hnon hab
    · exact hnon hab.symm
    · exact he rfl
  have hα := indep_card_le G hi
  rw [card_pair hw'.1.symm] at hα
  have hL := leaf_upper G (by omega)
  have small {X : Finset V} (hx : Indep G X) : (X.erase l).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    obtain ⟨hul,huX⟩ := mem_erase.mp hu
    obtain ⟨hvl,hvX⟩ := mem_erase.mp hv
    exact Classical.byContradiction (fun (hne : u ≠ v) => hx u huX v hvX hne (hcl u hul v hvl hne))
  have hB : bipartiteNum G ≤ 3 := by
    apply Finset.sup_le
    intro W hW
    obtain ⟨X,Y,_,rfl,hx,hy⟩ := (mem_filter.mp hW).2
    have hsub : X ∪ Y ⊆ insert l (X.erase l ∪ Y.erase l) := by
      intro v hv
      by_cases he : v = l
      · simp [he]
      · simpa [he] using hv
    have h₁ := card_le_card hsub
    have h₂ := card_insert_le l (X.erase l ∪ Y.erase l)
    have h₃ := card_union_le (X.erase l) (Y.erase l)
    have := small hx
    have := small hy
    omega
  have hcone (v : V) (hv : v ≠ c) : G.Adj c v := by
    by_cases hvl : v = l
    · subst v; exact ((hpend c).mpr rfl).symm
    · exact hcl c hlc.symm v hvl hv.symm
  have hh := conjecture177 G (connected_of_universal G c hcone) (by omega)
  exact ⟨by omega, sig, deg₁, (fun v hv => by have := hdeg v hv; omega),
    by omega, by omega, by omega⟩

/-- A tree on at least three vertices with at least n-1 leaves has a
vertex of degree n-1. Such a tree cannot span a graph without a universal
vertex. The proof sums its degrees outside its sole possible nonleaf. -/
private lemma leaves_without_universal (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, G.degree v ≤ Fintype.card V - 2) :
    maxLeaves G ≤ Fintype.card V - 2 := by
  classical
  apply Finset.sup_le
  intro T hT
  obtain ⟨hTG,ht⟩ := (mem_filter.mp hT).2
  by_contra! hmany
  have hC : (univ \ leaves T).card ≤ 1 := by
    rw [card_univ_diff]
    omega
  haveI : Nonempty V := ht.isConnected.nonempty
  obtain ⟨c, hc⟩ := card_le_one_iff_subset_singleton.mp hC
  have hleaves (v : V) (hv : v ≠ c) : T.degree v = 1 := by
    apply (leaf_mem v).mp
    by_contra h
    exact hv (mem_singleton.mp (hc (mem_sdiff.mpr ⟨mem_univ _,h⟩)))
  have hsum : (∑ v ∈ univ.erase c, T.degree v) = Fintype.card V - 1 := by
    calc
      _ = ∑ _v ∈ univ.erase c, 1 := sum_congr rfl (fun v hv => hleaves v (mem_erase.mp hv).1)
      _ = _ := by simp
  have hs := add_sum_erase (univ : Finset V) (fun v => T.degree v) (mem_univ c)
  rw [hsum, T.sum_degrees_eq_twice_card_edges] at hs
  have he := ht.card_edgeFinset
  have hdc := (SimpleGraph.degree_le_of_le hTG (v := c)).trans (hdeg c)
  dsimp only at hs
  omega

/-- For a complete bipartite graph with part sizes p ≤ q and p ≥ 2, the
four invariants are n-2, n, q, p, respectively, yielding slack p-2. -/
theorem complete_bipartite {A : Finset V} (hp : 2 ≤ A.card) (hpq : A.card ≤ (univ \ A).card)
    (hcross : ∀ u v, G.Adj u v ↔ ((u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A))) :
    maxLeaves G = Fintype.card V - 2 ∧ bipartiteNum G = Fintype.card V ∧
    independence G = (univ \ A).card ∧ secondDegree G = A.card ∧
    maxLeaves G + bipartiteNum G - (2 * independence G + secondDegree G) = A.card - 2 := by
  classical
  let B := univ \ A
  have mB (v : V) : v ∈ B ↔ v ∉ A := by simp [B]
  have partCard : A.card + B.card = Fintype.card V := by
    simpa [B, card_univ_diff] using Nat.add_sub_of_le (card_le_univ A)
  change A.card ≤ B.card at hpq
  have hn : 3 ≤ Fintype.card V := by omega
  have degA (v : V) (hv : v ∈ A) : G.degree v = B.card := by
    have he : G.neighborFinset v = B := by ext w; simp [hcross, hv, B]
    rw [← G.card_neighborFinset_eq_degree, he]
  have degB (v : V) (hv : v ∉ A) : G.degree v = A.card := by
    have he : G.neighborFinset v = A := by ext w; simp [hcross, hv]
    rw [← G.card_neighborFinset_eq_degree, he]
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < A.card by omega)
  obtain ⟨b,hb,d,hd,hbd⟩ := one_lt_card.mp (show 1 < B.card by omega)
  have hbA := (mB b).mp hb
  have hdA := (mB d).mp hd
  have hab : a ≠ b := fun h => hbA (h ▸ ha)
  have hL : maxLeaves G = Fintype.card V - 2 := by
    apply le_antisymm (leaves_without_universal G hn ?_)
    · have hc := con_insert G (con_single G b) (mem_singleton_self b)
          ((hcross a b).mpr (Or.inl ⟨ha,hbA⟩))
      have hm := conDom_leaves G {a,b} hc (by
        intro v _
        by_cases hv : v ∈ A
        · exact ⟨b,by simp,(hcross _ _).mpr (Or.inl ⟨hv,hbA⟩)⟩
        · exact ⟨a,by simp,(hcross _ _).mpr (Or.inr ⟨hv,ha⟩)⟩)
      simpa [card_univ_diff, hab] using hm
    · intro v
      by_cases hv : v ∈ A
      · rw [degA v hv]; omega
      · rw [degB v hv]; omega
  have hA : Indep G A := by
    intro u hu v hv _; simp [hcross, hu, hv]
  have hB : Indep G B := by
    intro u hu v hv _; simp [hcross, (mB u).mp hu, (mB v).mp hv]
  have hbi : bipartiteNum G = Fintype.card V := by
    refine le_antisymm (Finset.sup_le (fun X _ => card_le_univ X)) ?_
    rw [← partCard]
    exact bip_bound G hA hB disjoint_sdiff
  have halpha : independence G = B.card := by
    apply le_antisymm _ (indep_card_le G hB)
    obtain ⟨M,hm,hcard⟩ := exists_max_indep G
    rw [← hcard]
    by_cases hs : M ⊆ A
    · exact (card_le_card hs).trans hpq
    · obtain ⟨v,hv,hvA⟩ := not_subset.mp hs
      apply card_le_card
      intro u hu
      apply (mB u).mpr
      intro huA
      exact hm u hu v hv (fun e => hvA (e ▸ huA)) ((hcross u v).mpr (.inl ⟨huA,hvA⟩))
  have hsig : secondDegree G = A.card := by
    refine le_antisymm ?_ ?_
    · exact Nat.sInf_le ⟨b,d,hbd,by simp [degB _ hbA, degB _ hdA]⟩
    apply second_ge G (by omega) _ a
    intro v _
    by_cases hv : v ∈ A
    · rw [degA v hv]; exact hpq
    · rw [degB v hv]
  refine ⟨hL,hbi,halpha,hsig,?_⟩
  rw [hL,hbi,halpha,hsig]
  omega

/-- In a star of order at least three, equality holds and the second
degree is one. Adjacency is to the center and the graph has no loops. -/
theorem star (hn : 3 ≤ Fintype.card V) (c : V)
    (hg : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c)) :
    (maxLeaves G + bipartiteNum G = 2 * independence G + secondDegree G) ∧
      maxLeaves G = Fintype.card V - 1 ∧ bipartiteNum G = Fintype.card V ∧
      independence G = Fintype.card V - 1 ∧ secondDegree G = 1 := by
  classical
  let A := (univ : Finset V).erase c
  have hc (v : V) : v ∈ A ↔ v ≠ c := by simp [A]
  have hcard : A.card = Fintype.card V - 1 := by simp [A]
  have hA : Indep G A := by
    intro u hu v hv _ h
    exact ((hg u v).mp h).2.elim ((hc u).mp hu) ((hc v).mp hv)
  obtain ⟨he, hL, hB, hα, hs⟩ := split_join G (A := A) (by omega) hA
    ⟨c, by simp [A]⟩ (by
      intro x hx y hy
      have he : x = c := by simpa [A] using hx
      exact (hg x y).mpr ⟨hy.symm, Or.inl he⟩)
  exact ⟨he, hL, by omega, by omega, by omega⟩

/-- The connected order-two boundary uses degree-one leaves on both ends. -/
theorem order_two (hn : Fintype.card V = 2) (hconn : G.Connected) :
    maxLeaves G = 2 ∧ bipartiteNum G = 2 ∧ independence G = 1 ∧ secondDegree G = 1 := by
  classical
  have one (T : SimpleGraph V) [DecidableRel T.Adj] (ht : T.Connected) (v : V) : T.degree v = 1 := by
    have pos := (T.degree_pos_iff_exists_adj v).mpr (exists_adj T ht (by omega) v)
    have hi := T.degree_lt_card_verts v
    omega
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  have hL : maxLeaves G = 2 := by
    refine le_antisymm (Finset.sup_le (fun T _ => (card_le_univ _).trans hn.le)) ?_
    obtain ⟨T,hTG,ht⟩ := hconn.exists_isTree_le
    have hall : leaves T = univ := by
      ext v
      exact ⟨fun _ => mem_univ _,fun _ => (leaf_mem v).mpr (one T ht.isConnected v)⟩
    have h := Finset.le_sup (f := fun S => (leaves S).card)
      (mem_filter.mpr ⟨mem_univ T, hTG, ht⟩) (s := univ.filter (fun S => S ≤ G ∧ S.IsTree))
    change (leaves T).card ≤ maxLeaves G at h
    rw [hall,card_univ,hn] at h
    exact h
  have hB : bipartiteNum G = 2 := le_antisymm
    (Finset.sup_le (fun X _ => (card_le_univ X).trans hn.le)) (basic_bipartite G (by omega))
  have hI : independence G = 1 := by
    have hl := indep_card_le G (A := {a}) (by simp [Indep])
    simp only [card_singleton] at hl
    obtain ⟨M,hm,hsize⟩ := exists_max_indep G
    have hmC := card_le_univ M
    apply Classical.byContradiction
    intro h
    have he := M.eq_univ_of_card (show M.card = Fintype.card V by omega)
    obtain ⟨v,hv⟩ := exists_adj G hconn (by omega) a
    exact hm a (by simp [he]) v (by simp [he]) hv.ne hv
  have hsig : secondDegree G = 1 := by
    apply le_antisymm _ (secondDegree_properties G hconn (by omega)).1
    exact Nat.sInf_le ⟨a,b,hab,by simp [one G hconn]⟩
  exact ⟨hL,hB,hI,hsig⟩

#print axioms order_two
#print axioms star
#print axioms complete_bipartite
#print axioms pendant_clique
#print axioms split_join
#print axioms complete
end Graffiti177.Sharpness
