import SixFiniteOrder189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189

/-- Refine the degree-six order bound in the presence of three-connectivity. -/
theorem order_le_forty_three_at_degree_six_three_connected {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 3 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 43 := by
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
  have nodeD2 {u z : V} (uz : G.Adj u z)
      (du : G.dist x u + 1 = G.dist x z) : f z ⊆ DistanceTwo G u := by
    intro w hw
    obtain ⟨zw, dw⟩ := (Finset.mem_filter.mp hw).2
    have uwne : u ≠ w := by intro e; rw [← e] at dw; omega
    have uwna : ¬G.Adj u w := by
      intro a
      have hdist := dist_eq_one_iff_adj.mpr a
      have tri := hc.dist_triangle (u:=x) (v:=u) (w:=w)
      omega
    exact mem_distanceTwo.mpr (dist_two hc uwne uwna uz zw)
  have parent (z : V) (pos : 0 < G.dist x z) :
      ∃ u : V, G.Adj u z ∧ G.dist x u + 1 = G.dist x z := by
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x z
    let j := p.length - 1
    let u := p.getVert j
    have hj : j + 1 = p.length := by dsimp [j]; omega
    have uz : G.Adj u z := by
      have e := p.adj_getVert_succ (i:=j) (by omega)
      rw [hj, getVert_length] at e
      exact e
    have hu : G.dist x u = j := distance_on_geodesic hc p hp j (by omega)
    exact ⟨u, uz, by omega⟩
  have next (z : V) (hz : z ∈ E) : (f z).card ≤ 6 := by
    have ne := (Finset.mem_erase.mp hz).1
    have pos : 0 < G.dist x z := by
      by_contra! zero
      exact ne (((dist_eq_zero_iff_eq_or_not_reachable.mp (by omega)).resolve_right
        (not_not.mpr (hc x z))).symm)
    obtain ⟨u,uz,du⟩ := parent z pos
    exact (Finset.card_le_card (nodeD2 uz du)).trans (b2 u)
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
  have hx := cap x
  by_contra! n
  have wide : 30 < (E.biUnion f).card := by omega
  have noShared {u z t : V} (ze : z ∈ E) (te : t ∈ E) (zt : z ≠ t)
      (uz : G.Adj u z) (ut : G.Adj u t)
      (duz : G.dist x u + 1 = G.dist x z) (dut : G.dist x u + 1 = G.dist x t) : False := by
    let R := (E.erase z).erase t
    have cc : R.card ≤ 4 := by
      have tR : t ∈ E.erase z := mem_erase.mpr ⟨zt.symm,te⟩
      have cz := card_erase_add_one ze
      have ct := card_erase_add_one tR
      dsimp [R]
      omega
    have cR : (R.biUnion f).card ≤ 24 := by
      have cr := card_biUnion_le_card_mul R f 6 (fun w hw =>
        next w (mem_erase.mp (mem_erase.mp hw).2).2)
      omega
    have small : (f z ∪ f t).card ≤ 6 :=
      (card_le_card (union_subset (nodeD2 uz duz) (nodeD2 ut dut))).trans (b2 u)
    have sub : E.biUnion f ⊆ (f z ∪ f t) ∪ R.biUnion f := by
      intro w hw
      obtain ⟨i,ie,iw⟩ := mem_biUnion.mp hw
      by_cases iz : i = z
      · exact mem_union.mpr (.inl (mem_union.mpr (.inl (iz ▸ iw))))
      by_cases it : i = t
      · exact mem_union.mpr (.inl (mem_union.mpr (.inr (it ▸ iw))))
      exact mem_union.mpr (.inr (mem_biUnion.mpr
        ⟨i,mem_erase.mpr ⟨it,mem_erase.mpr ⟨iz,ie⟩⟩,iw⟩))
    have csub := card_le_card sub
    have cun := card_union_le (f z ∪ f t) (R.biUnion f)
    omega
  have far : ∃ y : V, 2 < G.dist x y := by
    by_contra! nf
    have z : E.biUnion f = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro w hw
      obtain ⟨i,ie,iw⟩ := mem_biUnion.mp hw
      have hne := (mem_erase.mp ie).1
      have e := (mem_filter.mp (mem_erase.mp ie).2).2
      have dp : G.dist x i ≠ 0 := by
        intro z
        exact hne (((dist_eq_zero_iff_eq_or_not_reachable.mp z).resolve_right
          (not_not.mpr (hc x i))).symm)
      have hh := (mem_filter.mp iw).2.2
      simp only [Nat.even_iff] at e
      have d := nf w
      omega
    rw [z,card_empty] at wide
    omega
  obtain ⟨y,hy⟩ := far
  have Bbig := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) hy
  obtain ⟨B, hB, sizeB⟩ := exists_subset_card_eq Bbig
  have depthB {z : V} (hz : z ∈ B) : G.dist x z = 2 := mem_shell.mp (hB hz)
  have BE : B ⊆ E := by
    intro z hz
    have h := depthB hz
    have ne : z ≠ x := by intro e; rw [e,dist_self] at h; omega
    exact mem_erase.mpr ⟨ne, mem_filter.mpr ⟨mem_univ _,h ▸ (by decide : Even 2)⟩⟩
  have assign (z : V) (hz : z ∈ B) :
      ∃ u : V, G.Adj u z ∧ G.dist x u = 1 := by
    obtain ⟨u,uz,du⟩ := parent z (by rw [depthB hz]; decide)
    exact ⟨u,uz,by have := depthB hz; omega⟩
  let par (z : V) : V := if h : z ∈ B then Classical.choose (assign z h) else x
  have parSpec {z : V} (hz : z ∈ B) : G.Adj (par z) z ∧ G.dist x (par z) = 1 := by
    simpa [par, dif_pos hz] using Classical.choose_spec (assign z hz)
  have oneB (z : V) (hz : z ∈ B) : (f z).card ≤ 4 := by
    let u := par z
    have us := parSpec hz
    have ux : G.Adj u x := (dist_eq_one_iff_adj.mp us.2).symm
    have zu := depthB hz
    let C := B.erase z
    let ch (w : V) := if G.Adj u (par w) then w else par w
    have cert (t : V) (ht : t ∈ C) :
        G.dist x (par t) = 1 ∧ G.dist x t = 2 ∧ u ≠ par t ∧ ¬G.Adj u t := by
      have ⟨ne, tb⟩ := mem_erase.mp ht
      have ps := parSpec tb
      have dt := depthB tb
      have nu : ¬ G.Adj u t := fun adj =>
        noShared (BE hz) (BE tb) ne.symm us.1 adj (by omega) (by omega)
      have nu' : u ≠ par t := fun e => nu (e.symm ▸ ps.1)
      exact ⟨ps.2,dt,nu',nu⟩
    have A (t : V) (th : t ∈ C) : ch t ∈ DistanceTwo G u ∧ G.dist x (ch t) ≤ 2 := by
      obtain ⟨dp,dt,ne,na⟩ := cert t th
      have pt := (parSpec (mem_erase.mp th).2).1
      by_cases a : G.Adj u (par t)
      · have ne' : u ≠ t := by intro e; have e' : G.dist x u = 1 := us.2; rw [e] at e'; omega
        simp only [ch,if_pos a,mem_distanceTwo]
        exact ⟨dist_two hc ne' na a pt,dt.le⟩
      · have xp : G.Adj x (par t) := dist_eq_one_iff_adj.mp dp
        simp only [ch,if_neg a,mem_distanceTwo]
        exact ⟨dist_two hc ne a ux xp,dp.le.trans (by decide)⟩
    have inj : ∀ i ∈ C, ∀ j ∈ C, ch i = ch j → i = j := by
      intro i ih j jh eq
      obtain ⟨pi,di,ui,ni⟩ := cert i ih
      obtain ⟨pj,dj,uj,nj⟩ := cert j jh
      by_cases ai : G.Adj u (par i) <;> by_cases aj : G.Adj u (par j)
      · simpa [ch,ai,aj] using eq
      · simp only [ch,if_pos ai,if_neg aj] at eq
        rw [eq] at di; omega
      · simp only [ch,if_neg ai,if_pos aj] at eq
        rw [← eq] at dj; omega
      · simp only [ch,if_neg ai,if_neg aj] at eq
        apply Classical.byContradiction
        intro hij
        have ib := (mem_erase.mp ih).2
        have jb := (mem_erase.mp jh).2
        exact noShared (BE ib) (BE jb) hij (parSpec ib).1 (eq ▸ (parSpec jb).1)
          (by omega) (by omega)
    have cC : C.card = 2 := by
      have h := card_erase_add_one hz
      dsimp [C]
      omega
    have cIm : (C.image ch).card = 2 := (card_image_of_injOn inj).trans cC
    have dis : Disjoint (f z) (C.image ch) := by
      apply disjoint_left.mpr
      intro w hw hIm
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hIm
      have e := (mem_filter.mp hw).2.2
      have g := (A t ht).2
      omega
    have sub : f z ∪ C.image ch ⊆ DistanceTwo G u := by
      apply union_subset (nodeD2 us.1 (by omega))
      intro w hw
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hw
      exact (A t ht).1
    have bound := (card_le_card sub).trans (b2 u)
    rw [card_union_of_disjoint dis, cIm] at bound
    omega
  let D := E \ B
  have cD : D.card ≤ 3 := by
    have e := card_sdiff_add_card_eq_card BE
    dsimp [D]
    omega
  have cover' : E.biUnion f ⊆ B.biUnion f ∪ D.biUnion f := by
    intro w hw
    obtain ⟨t,te,tw⟩ := mem_biUnion.mp hw
    by_cases h : t ∈ B
    · exact mem_union.mpr (.inl (mem_biUnion.mpr ⟨t,h,tw⟩))
    · exact mem_union.mpr (.inr (mem_biUnion.mpr ⟨t,mem_sdiff.mpr ⟨te,h⟩,tw⟩))
  have ca := card_biUnion_le_card_mul B f 4 oneB
  have cb := card_biUnion_le_card_mul D f 6 (fun z hz => next z (mem_sdiff.mp hz).1)
  have cc := card_le_card cover'
  have cu := card_union_le (B.biUnion f) (D.biUnion f)
  omega

#print axioms order_le_forty_three_at_degree_six_three_connected
end Graffiti189LongestPath
