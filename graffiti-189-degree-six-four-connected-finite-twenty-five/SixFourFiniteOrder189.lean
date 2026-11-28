import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189

variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The third distance layer has at most twelve vertices at a degree-six
center under the cap of seven even vertices, with no diameter assumption. -/
theorem third_shell_le_twelve_at_degree_six
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6) : (Shell G x 3).card ≤ 12 := by
  classical
  let A := Shell G x 1
  let C := Shell G x 3
  let f (a : V) := C ∩ DistanceTwo G a
  have cA : A.card ≤ 6 := by
    have eq : A = G.neighborFinset x := by
      ext a
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have bd (u : V) : (DistanceTwo G u).card ≤ 6 :=
    distanceTwo_le_of_even 6 u (cap u)
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
  have fbound (a : V) (ha : a ∈ T) : (f a).card ≤ 7 - T.card := by
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
    have dis : Disjoint (f a) (U.image ch) := by
      apply disjoint_left.mpr
      intro z zf zi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zi
      have d := cDepth (mem_inter.mp zf).1
      have e := (good b hb).2
      omega
    have sub : f a ∪ U.image ch ⊆ DistanceTwo G a := by
      apply union_subset (fun z hz => (mem_inter.mp hz).2)
      intro z zz
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zz
      exact (good b hb).1
    have n := (card_le_card sub).trans (bd a)
    rw [card_union_of_disjoint dis,card_image_of_injOn inj] at n
    have er := card_erase_add_one ha
    dsimp [U] at n
    omega
  have w := (card_le_card cover).trans (card_biUnion_le_card_mul T f (7-T.card) fbound)
  have ar (t : ℕ) (h : t ≤ 6) : t*(7-t) ≤ 12 := by
    have e : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact w.trans (ar T.card ts)

/-- With degree six and connectivity at least four, only orders up to
twenty-five can occur under the odd/even catalogue hypotheses. -/
theorem order_le_twenty_five_at_degree_six_four_connected
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 4 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 25 := by
  classical
  have diam := diameter_bound_from_inner_even_layers hc 6 4 1 cap conn (by decide)
  have cov : (Finset.univ : Finset V) ⊆ (EvenFrom G x ∪ G.neighborFinset x) ∪ Shell G x 3 := by
    intro y _
    have d : G.dist x y ≤ 4 := diam x y
    by_cases e : Even (G.dist x y)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_univ _,e⟩))))
    by_cases o : G.dist x y = 1
    · exact mem_union.mpr (.inl (mem_union.mpr
        (.inr ((G.mem_neighborFinset x y).mpr (dist_eq_one_iff_adj.mp o)))))
    exact mem_union.mpr (.inr (mem_shell.mpr (by simp only [Nat.even_iff] at e; omega)))
  have h := card_le_card cov
  rw [card_univ] at h
  have u := card_union_le (EvenFrom G x ∪ G.neighborFinset x) (Shell G x 3)
  have v := card_union_le (EvenFrom G x) (G.neighborFinset x)
  rw [G.card_neighborFinset_eq_degree] at v
  have c := cap x
  have b := third_shell_le_twelve_at_degree_six hc cap x dx
  omega

#print axioms third_shell_le_twelve_at_degree_six
#print axioms order_le_twenty_five_at_degree_six_four_connected
end Graffiti189LongestPath
