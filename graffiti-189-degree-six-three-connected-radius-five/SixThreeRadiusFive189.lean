import SixFourFiniteOrder189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem fifth_shell_le_five_mul_fourth
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7) (x : V) :
    (Shell G x 5).card ≤ (Shell G x 4).card * 5 := by
  classical
  let D := Shell G x 4
  let F (z : V) := (Shell G x 5).filter (G.Adj z)
  have lim (z : V) (hz : z ∈ D) : (F z).card ≤ 5 := by
    have dz : G.dist x z = 4 := mem_shell.mp hz
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x z
    have len : p.length = 4 := hp.trans dz
    let u := p.getVert 3
    let v := p.getVert 2
    let a := p.getVert 1
    have du : G.dist x u = 3 := distance_on_geodesic hc p hp 3 (by omega)
    have da : G.dist x a = 1 := distance_on_geodesic hc p hp 1 (by omega)
    have av : G.Adj a v := p.adj_getVert_succ (i:=1) (by omega)
    have vu : G.Adj v u := p.adj_getVert_succ (i:=2) (by omega)
    have uz : G.Adj u z := by
      have e := p.adj_getVert_succ (i:=3) (by omega)
      have e4 : p.getVert 4 = z := by rw [← len,getVert_length]
      simpa only [e4] using e
    have two {w : V} (difference : G.dist x w = 1 ∨ G.dist x w = 5) :
        u ≠ w ∧ ¬ G.Adj u w := by
      constructor
      · intro e
        rw [← e] at difference
        omega
      · intro e
        have i := dist_eq_one_iff_adj.mpr e
        have j := hc.dist_triangle (u:=x) (v:=u) (w:=w)
        have k := hc.dist_triangle (u:=x) (v:=w) (w:=u)
        rw [dist_comm (u:=w) (v:=u)] at k
        omega
    have ad2 : a ∈ DistanceTwo G u := mem_distanceTwo.mpr
      (dist_two hc (two (.inl da)).1 (two (.inl da)).2 vu.symm av.symm)
    have sub : insert a (F z) ⊆ DistanceTwo G u := by
      intro w hm
      rcases mem_insert.mp hm with rfl|wm
      · exact ad2
      obtain ⟨wy,zw⟩ := mem_filter.mp wm
      have dw : G.dist x w = 5 := mem_shell.mp wy
      exact mem_distanceTwo.mpr (dist_two hc (two (.inr dw)).1 (two (.inr dw)).2 uz zw)
    have n : a ∉ F z := by
      intro e
      have d : G.dist x a = 5 := mem_shell.mp (mem_filter.mp e).1
      omega
    have c := (card_le_card sub).trans (distanceTwo_le_of_even 6 u (cap u))
    rw [card_insert_of_not_mem n] at c
    omega
  have cov : Shell G x 5 ⊆ D.biUnion F := by
    intro w wm
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x w
    have len : p.length = 5 := hp.trans (mem_shell.mp wm)
    let z := p.getVert 4
    have d : G.dist x z = 4 := distance_on_geodesic hc p hp 4 (by omega)
    have zw : G.Adj z w := by
      have e := p.adj_getVert_succ (i:=4) (by omega)
      have e5 : p.getVert 5 = w := by rw [← len,getVert_length]
      simpa only [e5] using e
    exact mem_biUnion.mpr ⟨z,mem_shell.mpr d,mem_filter.mpr ⟨wm,zw⟩⟩
  exact (card_le_card cov).trans (card_biUnion_le_card_mul D F 5 lim)

private theorem order_sum_odd_shells_of_radius_six
    (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6) (diam : ∀ y, G.dist x y ≤ 6) :
    Fintype.card V ≤ 13 + (Shell G x 3).card + (Shell G x 5).card := by
  classical
  have cov : (Finset.univ : Finset V) ⊆ (EvenFrom G x ∪ G.neighborFinset x) ∪
      (Shell G x 3 ∪ Shell G x 5) := by
    intro y _
    have d := diam y
    by_cases e : Even (G.dist x y)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_univ _,e⟩))))
    by_cases o : G.dist x y = 1
    · exact mem_union.mpr (.inl (mem_union.mpr
        (.inr ((G.mem_neighborFinset x y).mpr (dist_eq_one_iff_adj.mp o)))))
    have h : G.dist x y = 3 ∨ G.dist x y = 5 := by
      simp only [Nat.even_iff] at e
      omega
    exact mem_union.mpr (.inr (mem_union.mpr (h.imp mem_shell.mpr mem_shell.mpr)))
  have h := card_le_card cov
  rw [card_univ] at h
  have u := card_union_le (EvenFrom G x ∪ G.neighborFinset x) (Shell G x 3 ∪ Shell G x 5)
  have v := card_union_le (EvenFrom G x) (G.neighborFinset x)
  rw [G.card_neighborFinset_eq_degree] at v
  have w := card_union_le (Shell G x 3) (Shell G x 5)
  have c := cap x
  omega

/-- A large degree-six, three-connected graph has a unique possible
distance-layer pattern at each degree-at-most-six root. -/
theorem outer_shell_profile_at_degree_six_three_connected
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 3 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x : V) (dx : G.degree x ≤ 6) (n : 25 < Fintype.card V) :
    (∀ y, G.dist x y ≤ 5) ∧ (∃ y, G.dist x y = 5) ∧
      (Shell G x 2).card = 3 ∧ (Shell G x 4).card = 3 := by
  classical
  have rad := diameter_bound_from_inner_even_layers hc 6 3 2 cap conn (by decide)
  have no6 (y : V) : G.dist x y ≤ 5 := by
    have d := rad x y
    by_contra! bad
    have dy : G.dist x y = 6 := by omega
    have n2 := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) (by omega)
    have n4 := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=4) (by decide) (by omega)
    -- The far even vertex itself spends another slot after the two separating layers.
    have y0 : y ≠ x := by intro eq; rw [eq,dist_self] at dy; omega
    have ey : y ∈ (EvenFrom G x).erase x :=
      mem_erase.mpr ⟨y0, mem_filter.mpr ⟨mem_univ _,by rw [dy]; decide⟩⟩
    have not24 : y ∉ Shell G x 2 ∪ Shell G x 4 := by
      intro m
      rcases mem_union.mp m with a|b
      · have e := mem_shell.mp a; omega
      · have e := mem_shell.mp b; omega
    have dis : Disjoint (Shell G x 2) (Shell G x 4) := by
      apply disjoint_left.mpr
      intro w hm hn
      have e := mem_shell.mp hm
      have f := mem_shell.mp hn
      omega
    have sub : insert y (Shell G x 2 ∪ Shell G x 4) ⊆ (EvenFrom G x).erase x := by
      intro v hm
      rcases mem_insert.mp hm with e|s
      · exact e.symm ▸ ey
      have ev : G.dist x v = 2 ∨ G.dist x v = 4 :=
        (mem_union.mp s).imp mem_shell.mp mem_shell.mp
      have n0 : v ≠ x := by intro e; rw [e,dist_self] at ev; omega
      have even : Even (G.dist x v) := by rcases ev with e|e <;> rw [e] <;> decide
      exact mem_erase.mpr ⟨n0,mem_filter.mpr ⟨mem_univ _,even⟩⟩
    have cb := card_le_card sub
    rw [card_insert_of_not_mem not24,card_union_of_disjoint dis] at cb
    have xx : x ∈ EvenFrom G x := by simp [EvenFrom,dist_self]
    have cx := card_erase_add_one xx
    have c := cap x
    omega
  have ex : ∃ y : V, G.dist x y = 5 := by
    by_contra! none
    have q : Shell G x 5 = ∅ := eq_empty_iff_forall_not_mem.mpr fun y hy => none y (mem_shell.mp hy)
    have bs := order_sum_odd_shells_of_radius_six cap x dx (fun y => (no6 y).trans (by decide))
    have bt := third_shell_le_twelve_at_degree_six hc cap x dx
    rw [q,card_empty] at bs
    omega
  obtain ⟨y,dy⟩ := ex
  have n2 := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) (by omega)
  have n4 := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=4) (by decide) (by omega)
  have c := shell_two_four_le_of_even (cap x)
  exact ⟨no6,⟨y,dy⟩,by omega,by omega⟩

theorem order_le_forty_at_degree_six_three_connected
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 3 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 40 := by
  by_cases n : Fintype.card V ≤ 25
  · omega
  obtain ⟨r,_,_,four⟩ := outer_shell_profile_at_degree_six_three_connected hc cap conn x dx (by omega)
  have b := order_sum_odd_shells_of_radius_six cap x dx (fun y => (r y).trans (by decide))
  have t := third_shell_le_twelve_at_degree_six hc cap x dx
  have f := fifth_shell_le_five_mul_fourth hc cap x
  omega

#print axioms outer_shell_profile_at_degree_six_three_connected
#print axioms order_le_forty_at_degree_six_three_connected
end Graffiti189LongestPath
