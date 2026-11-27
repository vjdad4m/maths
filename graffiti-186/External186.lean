import Proof179

/-! The external-neighborhood variant of Written on the Wall II #186. -/

namespace Graffiti186External

open SimpleGraph Finset
open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V]

def eccentricity (G : SimpleGraph V) (v : V) : ℕ := univ.sup (G.dist v)

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl

omit [Fintype V] in
private theorem le_square (G : SimpleGraph V) : G ≤ square G :=
  fun _ _ h => ⟨h.ne, le_trans (G.dist_le h.toWalk) (by simp [Adj.toWalk])⟩

omit [Fintype V] in
private theorem square_connected {G : SimpleGraph V} (hc : G.Connected) :
    (square G).Connected := hc.mono (le_square G)

omit [Fintype V] in
private theorem dist_le_twice_square_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : (square G).Walk v w) : G.dist v w ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h' : G.dist a b ≤ 2 := h.2
    have htri : G.dist a c ≤ G.dist a b + G.dist b c := hc.dist_triangle
    rw [Walk.length_cons]
    omega

omit [Fintype V] in
private theorem square_dist_le_half_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : G.Walk v w) : (square G).dist v w ≤ (p.length + 1) / 2 := by
  match p with
  | .nil => simp
  | .cons h .nil =>
    simpa [Adj.toWalk] using (square G).dist_le ((le_square G h).toWalk)
  | @Walk.cons _ _ a b c h (.cons (v := d) h' q) =>
    have htail := square_dist_le_half_walk hc q
    have hab : G.dist a b ≤ 1 := G.dist_le h.toWalk
    have hbd : G.dist b d ≤ 1 := G.dist_le h'.toWalk
    have had₀ : G.dist a d ≤ G.dist a b + G.dist b d := hc.dist_triangle
    have had : (square G).dist a d ≤ 1 := by
      by_cases heq : a = d
      · simp [heq, dist_self]
      · exact (square G).dist_le (show (square G).Adj a d from ⟨heq, by omega⟩).toWalk
    have htri : (square G).dist a c ≤ (square G).dist a d + (square G).dist d c :=
      (square_connected hc).dist_triangle
    simp only [Walk.length_cons]
    omega
termination_by p.length
decreasing_by simp only [Walk.length_cons]; omega

omit [Fintype V] in
theorem square_dist {G : SimpleGraph V} (hc : G.Connected) (v w : V) :
    (square G).dist v w = (G.dist v w + 1) / 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  obtain ⟨q, hq⟩ := (square_connected hc).exists_walk_length_eq_dist v w
  have hlo := dist_le_twice_square_walk hc q
  have hhi := square_dist_le_half_walk hc p
  omega

private theorem dist_le_ecc (G : SimpleGraph V) (v w : V) :
    G.dist v w ≤ eccentricity G v := le_sup (mem_univ w)

private theorem exists_dist_eq_ecc (G : SimpleGraph V) (v : V) :
    ∃ w, eccentricity G v = G.dist v w := by
  obtain ⟨w, _, hw⟩ := exists_mem_eq_sup univ ⟨v, mem_univ v⟩ (G.dist v)
  exact ⟨w, hw⟩

private theorem square_ecc {G : SimpleGraph V} (hc : G.Connected) (v : V) :
    eccentricity (square G) v = (eccentricity G v + 1) / 2 := by
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨z, hz⟩ := exists_dist_eq_ecc (square G) v
  have hlo := dist_le_ecc (square G) v w
  have hhi := dist_le_ecc G v z
  rw [square_dist hc] at hlo hz
  omega

omit [Fintype V] in
private theorem take_drop_lengths {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) (i : ℕ) :
    (p.take i).length = min i p.length ∧ (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.take, Walk.drop]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.take, Walk.drop]
    | succ i =>
      have h := ih i
      change (p.take i).length + 1 = min (i + 1) (p.length + 1) ∧
        (p.drop i).length = p.length + 1 - (i + 1)
      omega

omit [Fintype V] in
private theorem geodesic_prefix_suffix {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} {p : G.Walk v w} (hp : p.length = G.dist v w) {i : ℕ}
    (hi : i ≤ p.length) :
    G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have hs := take_drop_lengths p i
  have htri : G.dist v w ≤ G.dist v (p.getVert i) + G.dist (p.getVert i) w :=
    hc.dist_triangle
  simp [min_eq_left hi] at hs
  omega

/-- The square centers are exactly the minimizers of eccentricity. -/
def centers (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun v => ∀ w, eccentricity G v ≤ eccentricity G w)

def setNeighbors (H : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ s ∈ S, H.Adj s v)

/-- Distance to a nonempty set. -/
def setDist (H : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (v : V) : ℕ :=
  S.inf' hS (fun s => H.dist s v)

def setEcc (H : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) : ℕ :=
  univ.sup (setDist H S hS)

theorem centers_nonempty {H : SimpleGraph V} (hH : H.Connected) :
    (centers H).Nonempty := by
  classical
  haveI : Nonempty V := hH.nonempty
  obtain ⟨v, hv, hm⟩ := exists_min_image (univ : Finset V) (eccentricity H) univ_nonempty
  exact ⟨v, mem_filter.mpr ⟨hv, fun w => hm w (mem_univ w)⟩⟩

omit [Fintype V] in
theorem square_setDist {G : SimpleGraph V} (hc : G.Connected) {S : Finset V}
    (hS : S.Nonempty) (v : V) :
    setDist (square G) S hS v = (setDist G S hS v + 1) / 2 := by
  obtain ⟨x, hx, hxv⟩ := exists_mem_eq_inf' hS (fun s => G.dist s v)
  obtain ⟨y, hy, hyv⟩ := exists_mem_eq_inf' hS (fun s => (square G).dist s v)
  have hlo : setDist G S hS v ≤ G.dist y v := inf'_le (fun s => G.dist s v) hy
  have hhi : setDist (square G) S hS v ≤ (square G).dist x v :=
    inf'_le (fun s => (square G).dist s v) hx
  rw [square_dist hc] at hyv hhi
  change setDist G S hS v = G.dist x v at hxv
  change setDist (square G) S hS v = (G.dist y v + 1) / 2 at hyv
  omega

theorem square_setEcc {G : SimpleGraph V} (hc : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    setEcc (square G) S hS = (setEcc G S hS + 1) / 2 := by
  haveI : Nonempty V := hc.nonempty
  obtain ⟨v, hv, he⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty (setDist G S hS)
  change setEcc G S hS = setDist G S hS v at he
  apply le_antisymm
  · unfold setEcc
    apply Finset.sup_le_iff.mpr
    intro u _
    rw [square_setDist hc]
    have hu : setDist G S hS u ≤ setEcc G S hS := le_sup (mem_univ u)
    change setDist G S hS u ≤ univ.sup (setDist G S hS) at hu
    omega
  · rw [he, ← square_setDist hc]
    exact le_sup (mem_univ v)

variable [DecidableEq V]

theorem metric_external_layers {G : SimpleGraph V} (hc : G.Connected)
    {S : Finset V} (hS : S.Nonempty) (v : V)
    :
    (S ∪ setNeighbors (square G) S).card + (setDist G S hS v - 2) ≤ Fintype.card V := by
  classical
  let D := setDist G S hS v
  obtain ⟨s, hs, hsd⟩ := exists_mem_eq_inf' hS (fun z => G.dist z v)
  change D = G.dist s v at hsd
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist s v
  have hlen : p.length = D := hp.trans hsd.symm
  let I := Finset.Icc 3 D
  let N := S ∪ setNeighbors (square G) S
  have hinj (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) :
      p.getVert i = p.getVert j → i = j := by
    intro hij
    obtain ⟨hi₀, hi₁⟩ := mem_Icc.mp hi
    obtain ⟨hj₀, hj₁⟩ := mem_Icc.mp hj
    have hpi := (geodesic_prefix_suffix hc hp (i := i) (by omega)).1
    have hpj := (geodesic_prefix_suffix hc hp (i := j) (by omega)).1
    rw [hij, hpj] at hpi
    exact hpi.symm
  have hdis : Disjoint N (I.image p.getVert) := by
    apply disjoint_left.mpr
    intro x hxN hxI
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hxI
    obtain ⟨hi₀, hi₁⟩ := mem_Icc.mp hi
    have htail := (geodesic_prefix_suffix hc hp (i := i) (by omega)).2
    have near : ∃ a ∈ S, G.dist a (p.getVert i) ≤ 2 := by
      rcases mem_union.mp hxN with hs | hn
      · exact ⟨_,hs,by rw [SimpleGraph.dist_self]; decide⟩
      · obtain ⟨a,ha,hadj⟩ := (mem_filter.mp hn).2
        exact ⟨a,ha,hadj.2⟩
    obtain ⟨a,ha,hnear⟩ := near
    have htri : G.dist a v ≤ G.dist a (p.getVert i) + G.dist (p.getVert i) v :=
      hc.dist_triangle
    have hmin : D ≤ G.dist a v := inf'_le (fun z => G.dist z v) ha
    omega
  have hsum := card_union_of_disjoint hdis
  have hcard := card_le_univ (N ∪ I.image p.getVert)
  rw [hsum, card_image_of_injOn (fun i hi j hj => hinj i hi j hj)] at hcard
  change N.card + (Finset.Icc 3 D).card ≤ _ at hcard
  rw [Nat.card_Icc] at hcard
  change N.card + (D - 2) ≤ _
  omega

def externalNeighbors (H : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact setNeighbors H S \ S

theorem metric_external_deficit {G : SimpleGraph V} (hc : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    (externalNeighbors (square G) S).card + S.card + (setEcc G S hS - 2) ≤ Fintype.card V := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨v, _, he⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty (setDist G S hS)
  have hu : externalNeighbors (square G) S ∪ S = S ∪ setNeighbors (square G) S := by
    ext x
    simp only [externalNeighbors,mem_union,mem_sdiff]
    tauto
  have dis : Disjoint (externalNeighbors (square G) S) S := disjoint_left.mpr fun _ h hx => (mem_sdiff.mp h).2 hx
  unfold setEcc
  rw [he, ← card_union_of_disjoint dis, hu]
  exact metric_external_layers hc hS v

omit [DecidableEq V] in
theorem singleton_center_even {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected)
    (c : V) (hC : centers (square G) = {c}) : eccentricity G c % 2 = 0 := by
  classical
  by_contra ho
  have hmem : c ∈ centers (square G) := by simp [hC]
  have hmin : ∀ w, eccentricity (square G) c ≤ eccentricity (square G) w :=
    (mem_filter.mp hmem).2
  obtain ⟨x,hx⟩ := exists_ne c
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist c x
  have hpos : 0 < p.length := hp ▸ hc.pos_dist_of_ne hx.symm
  let w := p.getVert 1
  have hcw : G.Adj c w := by simpa [w] using p.adj_getVert_succ (i:=0) hpos
  obtain ⟨z,hz⟩ := exists_dist_eq_ecc G w
  have ht : G.dist w z ≤ G.dist w c + G.dist c z := hc.dist_triangle
  have hwc : G.dist w c = 1 := dist_eq_one_iff_adj.mpr hcw.symm
  have hcZ := dist_le_ecc G c z
  have hwc' : eccentricity (square G) w ≤ eccentricity (square G) c := by
    rw [square_ecc hc, square_ecc hc]
    omega
  have hw : w ∈ centers (square G) :=
    mem_filter.mpr ⟨mem_univ _, fun u => hwc'.trans (hmin u)⟩
  rw [hC,mem_singleton] at hw
  exact hcw.ne hw.symm

theorem external_rhs_le_order_add_one {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) :
    (externalNeighbors (square G) (centers (square G))).card +
      2 * setEcc (square G) (centers (square G))
        (centers_nonempty (square_connected hc)) ≤ Fintype.card V + 1 := by
  classical
  let S := centers (square G)
  have hS : S.Nonempty := centers_nonempty (square_connected hc)
  have hex := metric_external_deficit hc S hS
  have hpos : 0 < S.card := card_pos.mpr hS
  rw [square_setEcc hc]
  by_cases hs : S.card = 1
  · obtain ⟨c,hc'⟩ := card_eq_one.mp hs
    have he := singleton_center_even hc c hc'
    have hh : setEcc G S hS = eccentricity G c := by
      unfold setEcc eccentricity
      congr 1
      funext v
      obtain ⟨s,hm,hval⟩ := exists_mem_eq_inf' hS (fun s => G.dist s v)
      have eq : s = c := by rwa [hc',mem_singleton] at hm
      exact hval.trans (congrArg (fun s => G.dist s v) eq)
    change (externalNeighbors (square G) S).card +
      2 * ((setEcc G S hS + 1) / 2) ≤ Fintype.card V + 1
    rw [hh] at hex ⊢
    omega
  · change (externalNeighbors (square G) S).card +
      2 * ((setEcc G S hS + 1) / 2) ≤ Fintype.card V + 1
    omega

/-- The variant excludes the center set itself from its square neighborhood.
This is not the literal catalogue inequality with the unrestricted union. -/
theorem conjecture186_external {G : SimpleGraph V} [Nontrivial V]
    [DecidableRel G.Adj] (hc : G.Connected) :
    (externalNeighbors (square G) (centers (square G))).card +
      2 * setEcc (square G) (centers (square G))
        (centers_nonempty (square_connected hc)) ≤
      Short177.maxLeaves G + Short177.bipartiteNum G :=
  (external_rhs_le_order_add_one hc).trans
    (Graffiti179.order_add_one G hc Fintype.one_lt_card)

#print axioms conjecture186_external
end
end Graffiti186External
