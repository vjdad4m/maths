import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two lengths_take_drop from SmallSeparator189

variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def FarOdd (G : SimpleGraph V) (x : V) : Finset V :=
  Finset.univ.filter (fun z=>3≤G.dist x z ∧ ¬Even (G.dist x z))

/-- All odd layers beyond the first share one charged budget, with
no diameter or vertex-connectivity premise. -/
theorem far_odd_card_le_twelve_at_degree_six
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6) : (FarOdd G x).card ≤ 12 := by
  classical
  let A := Shell G x 1
  let C := Shell G x 3
  let f (a : V) := C ∩ DistanceTwo G a
  let h (a : V) := (FarOdd G x).filter (fun z=>Even (G.dist a z))
  have cA : A.card ≤ 6 := by
    have eq : A = G.neighborFinset x := by
      ext a
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have aDepth {a : V} (am : a ∈ A) : G.dist x a = 1 := mem_shell.mp am
  have cDepth {c : V} (cm : c ∈ C) : G.dist x c = 3 := mem_shell.mp cm
  have d2_of_middle {a b c : V} (da : G.dist x a = 1) (dc : G.dist x c = 3)
      (ab : G.Adj a b) (bc : G.Adj b c) : G.dist a c = 2 := by
    have ne : a ≠ c := by intro e; rw [e] at da; omega
    have na : ¬ G.Adj a c := by
      intro ac
      have e := dist_eq_one_iff_adj.mpr ac
      have t := hc.dist_triangle (u:=x) (v:=a) (w:=c)
      omega
    exact dist_two hc ne na ab bc
  have coverA : C ⊆ A.biUnion f := by
    intro c cm
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x c
    have len : p.length = 3 := hp.trans (cDepth cm)
    let a := p.getVert 1
    let b := p.getVert 2
    have ap : G.dist x a = 1 := distance_on_geodesic hc p hp 1 (by omega)
    have ab : G.Adj a b := p.adj_getVert_succ (i:=1) (by omega)
    have bc : G.Adj b c := by
      have e := p.adj_getVert_succ (i:=2) (by omega)
      have e3 : p.getVert 3 = c := by rw [← len,getVert_length]
      simpa only [e3] using e
    exact mem_biUnion.mpr ⟨a,mem_shell.mpr ap,mem_inter.mpr
      ⟨cm,mem_distanceTwo.mpr (d2_of_middle ap (cDepth cm) ab bc)⟩⟩
  let fam := A.powerset.filter (fun T : Finset V => C ⊆ T.biUnion f)
  have fn : fam.Nonempty := ⟨A,mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl),coverA⟩⟩
  obtain ⟨T, Tfam, minT⟩ := exists_min_image fam (fun S : Finset V => S.card) fn
  have TA : T ⊆ A := mem_powerset.mp (mem_filter.mp Tfam).1
  have cover : C ⊆ T.biUnion f := (mem_filter.mp Tfam).2
  have coverAll : FarOdd G x ⊆ T.biUnion h := by
    intro e em
    obtain ⟨_,de3,deOdd⟩ := mem_filter.mp em
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x e
    let c := p.getVert 3
    have l3 : 3≤p.length := hp.symm ▸ de3
    have c3 : G.dist x c=3 := distance_on_geodesic hc p hp 3 l3
    obtain ⟨a,am,ac⟩ := mem_biUnion.mp (cover (mem_shell.mpr c3))
    have a1 := aDepth (TA am)
    have ac2 := mem_distanceTwo.mp (mem_inter.mp ac).2
    have ⟨_,slen⟩ := lengths_take_drop p 3 l3
    have up := G.dist_le (p.drop 3)
    change G.dist c e ≤ (p.drop 3).length at up
    have ae := hc.dist_triangle (u:=a) (v:=c) (w:=e)
    have xx := hc.dist_triangle (u:=x) (v:=a) (w:=e)
    have aeE : Even (G.dist a e) := by
      simp only [Nat.even_iff] at deOdd ⊢
      omega
    exact mem_biUnion.mpr ⟨a,am,mem_filter.mpr ⟨em,aeE⟩⟩
  have ts : T.card ≤ 6 := (card_le_card TA).trans cA
  have uniqueMiddle (a : V) (ha : a ∈ T) :
      ∃ b : V, G.dist x b = 2 ∧ G.Adj a b ∧ ∀ z ∈ T, z ≠ a → ¬ G.Adj z b := by
    have lost : ¬ C ⊆ (T.erase a).biUnion f := by
      intro hs
      have m : T.erase a ∈ fam := mem_filter.mpr ⟨mem_powerset.mpr
        ((erase_subset a T).trans TA),hs⟩
      have e := minT (T.erase a) m
      have cd := card_erase_add_one ha
      omega
    obtain ⟨c, cm, miss⟩ := not_subset.mp lost
    have ac : c ∈ f a := by
      obtain ⟨z,zm,zc⟩ := mem_biUnion.mp (cover cm)
      by_cases za : z = a
      · exact za ▸ zc
      · exact (miss (mem_biUnion.mpr ⟨z,mem_erase.mpr ⟨za,zm⟩,zc⟩)).elim
    have d2 := mem_distanceTwo.mp (mem_inter.mp ac).2
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a c
    have len : p.length = 2 := hp.trans d2
    let b := p.getVert 1
    have ab : G.Adj a b := by simpa [b] using p.adj_getVert_succ (i:=0) (by omega)
    have bc : G.Adj b c := by
      have e := p.adj_getVert_succ (i:=1) (by omega)
      have e2 : p.getVert 2 = c := by rw [← len,getVert_length]
      simpa only [e2] using e
    have da := aDepth (TA ha)
    have dc := cDepth cm
    have d_ab := dist_eq_one_iff_adj.mpr ab
    have d_bc := dist_eq_one_iff_adj.mpr bc
    have t1 := hc.dist_triangle (u:=x) (v:=a) (w:=b)
    have t2 := hc.dist_triangle (u:=x) (v:=b) (w:=c)
    have db : G.dist x b = 2 := by omega
    refine ⟨b, db, ab, ?_⟩
    intro z zT ne zb
    have zc : c ∈ f z := mem_inter.mpr ⟨cm,mem_distanceTwo.mpr
      (d2_of_middle (aDepth (TA zT)) dc zb bc)⟩
    exact miss (mem_biUnion.mpr ⟨z,mem_erase.mpr ⟨ne,zT⟩,zc⟩)
  let rep (a : V) := if h : a ∈ T then Classical.choose (uniqueMiddle a h) else x
  have prop {a : V} (ha : a ∈ T) :
      G.dist x (rep a) = 2 ∧ G.Adj a (rep a) ∧ ∀ z ∈ T, z ≠ a → ¬ G.Adj z (rep a) := by
    simpa [rep, dif_pos ha] using Classical.choose_spec (uniqueMiddle a ha)
  have fbound (a : V) (ha : a ∈ T) : (h a).card ≤ 7 - T.card := by
    let U := T.erase a
    let ch (b : V) := if G.Adj a b then rep b else b
    have good (b : V) (hb : b ∈ U) : ch b ∈ DistanceTwo G a ∧ G.dist x (ch b) ≤ 2 := by
      obtain ⟨ba,bm⟩ := mem_erase.mp hb
      have pr := prop bm
      have bd := aDepth (TA bm)
      by_cases ab : G.Adj a b
      · have ne : a ≠ rep b := by
          intro h
          have d := aDepth (TA ha)
          rw [h] at d
          have e := pr.1
          omega
        simp only [ch,if_pos ab,mem_distanceTwo]
        exact ⟨dist_two hc ne (pr.2.2 a ha ba.symm) ab pr.2.1,pr.1.le⟩
      · have ax : G.Adj a x := (dist_eq_one_iff_adj.mp (aDepth (TA ha))).symm
        have xb : G.Adj x b := dist_eq_one_iff_adj.mp bd
        simp only [ch,if_neg ab,mem_distanceTwo]
        exact ⟨dist_two hc ba.symm ab ax xb,bd.le.trans (by decide)⟩
    have inj : ∀ b ∈ U, ∀ c ∈ U, ch b = ch c → b = c := by
      intro b hb c hc' eq
      have bm := (mem_erase.mp hb).2
      have cm := (mem_erase.mp hc').2
      have bp := prop bm
      have cp := prop cm
      have b1 := aDepth (TA bm)
      have c1 := aDepth (TA cm)
      by_cases ab : G.Adj a b <;> by_cases ac : G.Adj a c
      · simp only [ch,if_pos ab,if_pos ac] at eq
        apply Classical.byContradiction
        intro ne
        exact cp.2.2 b bm ne (eq ▸ bp.2.1)
      · simp only [ch,if_pos ab,if_neg ac] at eq
        have d := bp.1
        rw [eq] at d
        omega
      · simp only [ch,if_neg ab,if_pos ac] at eq
        have d := cp.1
        rw [← eq] at d
        omega
      · simpa [ch,ab,ac] using eq
    have dis : Disjoint (h a) (U.image ch) := by
      apply disjoint_left.mpr
      intro z zf zi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zi
      have e := (good b hb).2
      have far := (mem_filter.mp (mem_filter.mp zf).1).2.1
      omega
    have here (z : V) (ne : z≠a) (ev : Even (G.dist a z)) :
        z∈(EvenFrom G a).erase a :=
      mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,ev⟩⟩
    have sub : h a ∪ U.image ch ⊆ (EvenFrom G a).erase a := by
      apply union_subset
      · intro z zh
        obtain ⟨zFar,ev⟩ := mem_filter.mp zh
        have far := (mem_filter.mp zFar).2.1
        have near := aDepth (TA ha)
        exact here z (fun e=>by rw [e] at far; omega) ev
      · intro z zz
        obtain ⟨b,hb,rfl⟩ := mem_image.mp zz
        have distance := mem_distanceTwo.mp (good b hb).1
        exact here _ (fun e=>by rw [e,dist_self] at distance; omega) (by rw [distance]; decide)
    have n := card_le_card sub
    rw [card_union_of_disjoint dis,card_image_of_injOn inj] at n
    have sea : a∈EvenFrom G a := by simp [EvenFrom,dist_self]
    have num := card_erase_add_one sea
    have bound := cap a
    have er := card_erase_add_one ha
    dsimp [U] at n
    omega
  have w := (card_le_card coverAll).trans (card_biUnion_le_card_mul T h (7-T.card) fbound)
  have ar (t : ℕ) (h : t ≤ 6) : t*(7-t) ≤ 12 := by
    have e : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact w.trans (ar T.card ts)

/-- Under the degree-six catalogue cap, a connected graph with any
vertex of degree at most six has at most 25 vertices. -/
theorem order_le_twenty_five_at_degree_six
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 25 := by
  classical
  have cov : (Finset.univ : Finset V) ⊆ (EvenFrom G x ∪ G.neighborFinset x) ∪ FarOdd G x := by
    intro y _
    by_cases e : Even (G.dist x y)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_univ _,e⟩))))
    by_cases o : G.dist x y = 1
    · exact mem_union.mpr (.inl (mem_union.mpr
        (.inr ((G.mem_neighborFinset x y).mpr (dist_eq_one_iff_adj.mp o)))))
    have far : 3≤G.dist x y := by simp only [Nat.even_iff] at e; omega
    exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,far,e⟩)
  have c := card_le_card cov
  rw [card_univ] at c
  have u := card_union_le (EvenFrom G x ∪ G.neighborFinset x) (FarOdd G x)
  have v := card_union_le (EvenFrom G x) (G.neighborFinset x)
  rw [G.card_neighborFinset_eq_degree] at v
  have n := cap x
  have f := far_odd_card_le_twelve_at_degree_six hc cap x dx
  omega

#print axioms far_odd_card_le_twelve_at_degree_six
#print axioms order_le_twenty_five_at_degree_six
end Graffiti189LongestPath
