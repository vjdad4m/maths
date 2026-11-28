import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189

/-- The degree-six case has a finite order frontier. A vertex of degree at
most six serves as the center. Every odd-distance vertex beyond its
neighbors can be charged to an inward even-distance vertex, which controls
at most six successors using a preceding point on a geodesic. -/
theorem order_le_forty_nine_at_degree_six {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 49 := by
  classical
  let E := (EvenFrom G x).erase x
  let f (z : V) := Finset.univ.filter (fun w => G.Adj z w ∧ G.dist x w = G.dist x z + 1)
  have xE : x ∈ EvenFrom G x := by simp [EvenFrom, dist_self]
  have boundE : E.card ≤ 6 := by
    have h := cap x
    have c := Finset.card_erase_add_one xE
    change ((EvenFrom G x).erase x).card ≤ 6
    omega
  have b2 (u : V) : (DistanceTwo G u).card ≤ 6 := distanceTwo_le_of_even 6 u (cap u)
  have next (z : V) (hz : z ∈ E) : (f z).card ≤ 6 := by
    have ne := (Finset.mem_erase.mp hz).1
    have pos : 0 < G.dist x z := by
      by_contra! zero
      exact ne (((dist_eq_zero_iff_eq_or_not_reachable.mp (by omega)).resolve_right
        (not_not.mpr (hc x z))).symm)
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x z
    let j := p.length - 1
    let u := p.getVert j
    have hj : j + 1 = p.length := by dsimp [j]; omega
    have uz : G.Adj u z := by
      have e := p.adj_getVert_succ (i:=j) (by omega)
      rw [hj, getVert_length] at e
      exact e
    have hu : G.dist x u = j := distance_on_geodesic hc p hp j (by omega)
    apply (Finset.card_le_card (t:=DistanceTwo G u) ?_).trans (b2 u)
    intro w hw
    obtain ⟨zw, dw⟩ := (Finset.mem_filter.mp hw).2
    have uwne : u ≠ w := by intro e; rw [← e] at dw; omega
    have uwna : ¬G.Adj u w := by
      intro a
      have hdist := dist_eq_one_iff_adj.mpr a
      have tri := hc.dist_triangle (u:=x) (v:=u) (w:=w)
      omega
    exact mem_distanceTwo.mpr (dist_two hc uwne uwna uz zw)
  have cover : (Finset.univ : Finset V) ⊆
      (EvenFrom G x ∪ G.neighborFinset x) ∪ E.biUnion f := by
    intro w _
    by_cases hw : Even (G.dist x w)
    · exact mem_union.mpr (.inl (mem_union.mpr
          (.inl (mem_filter.mpr ⟨mem_univ _, hw⟩))))
    by_cases one : G.dist x w = 1
    · exact mem_union.mpr (.inl (mem_union.mpr
          (.inr ((G.mem_neighborFinset x w).mpr (dist_eq_one_iff_adj.mp one)))))
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x w
    have long : 3 ≤ p.length := by
      simp only [Nat.even_iff] at hw
      omega
    let j := p.length - 1
    let z := p.getVert j
    have hj : j + 1 = p.length := by dsimp [j]; omega
    have hz : G.dist x z = j := distance_on_geodesic hc p hp j (by omega)
    have zw : G.Adj z w := by
      have e := p.adj_getVert_succ (i:=j) (by omega)
      rw [hj, getVert_length] at e
      exact e
    have zn : z ≠ x := by intro e; rw [e, dist_self] at hz; omega
    have evenZ : Even (G.dist x z) := by
      simp only [Nat.even_iff] at hw ⊢
      omega
    have zE : z ∈ E := mem_erase.mpr ⟨zn,mem_filter.mpr ⟨mem_univ _,evenZ⟩⟩
    exact mem_union.mpr (.inr (mem_biUnion.mpr
      ⟨z,zE,mem_filter.mpr ⟨mem_univ _,zw,by omega⟩⟩))
  have hcard := Finset.card_le_card cover
  rw [Finset.card_univ] at hcard
  have u := Finset.card_union_le (EvenFrom G x ∪ G.neighborFinset x) (E.biUnion f)
  have v := Finset.card_union_le (EvenFrom G x) (G.neighborFinset x)
  rw [G.card_neighborFinset_eq_degree] at v
  have w := Finset.card_biUnion_le_card_mul E f 6 next
  have h := cap x
  omega

#print axioms order_le_forty_nine_at_degree_six
end Graffiti189LongestPath
