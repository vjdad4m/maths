import CrossSaturation189


namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem d2 {x y z : V} (hc : G.Connected) (xz : x≠z)
    (na : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z ∈ DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz na
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo, show G.dist x z=2 by omega]

private theorem cross_walk_length {a b y : V} (L : Finset V) (yo : y∉L)
    (boundary : ∀ u∈L, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈L)
    {x : V} (p : G.Walk x y) (xl : x∈L) :
    1 + min (G.dist a y) (G.dist b y) ≤ p.length := by
  induction p with
  | nil => exact (yo xl).elim
  | @cons u v w e p ih =>
    rcases boundary u xl v e with va|vb|vl
    · subst v
      have h := G.dist_le p
      have h' := Nat.min_le_left (G.dist a w) (G.dist b w)
      simp only [Walk.length_cons]
      omega
    · subst v
      have h := G.dist_le p
      have h' := Nat.min_le_right (G.dist a w) (G.dist b w)
      simp only [Walk.length_cons]
      omega
    · have h := ih yo vl
      simp only [Walk.length_cons]
      omega

private theorem cross_dist_of_equal {a b x y : V} (L : Finset V)
    (hc : G.Connected) (xl : x∈L) (yo : y∉L)
    (boundary : ∀ u∈L, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈L)
    (hit : G.Adj a x ∨ G.Adj b x) (same : G.dist a y = G.dist b y) :
    G.dist x y = G.dist a y + 1 := by
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x y
  have lower := cross_walk_length L yo boundary p xl
  rw [same, min_self, ← same] at lower
  rcases hit with ax|bx
  · have upper := hc.dist_triangle (u:=x) (v:=a) (w:=y)
    have d1 := dist_eq_one_iff_adj.mpr ax.symm
    omega
  · have upper := hc.dist_triangle (u:=x) (v:=b) (w:=y)
    have d1 := dist_eq_one_iff_adj.mpr bx.symm
    omega

/-- Positive even-distance vertices (the origin is not counted). -/
noncomputable def PositiveEven (G : SimpleGraph V) [Fintype V] (x : V) : Finset V := by
  classical
  exact (EvenFrom G x).erase x

private theorem mem_positive {x y : V} :
    y∈PositiveEven G x ↔ y≠x ∧ Even (G.dist x y) := by
  classical simp [PositiveEven,EvenFrom]

private theorem positive_card {x : V} (h : (EvenFrom G x).card ≤ 6) :
    (PositiveEven G x).card ≤ 5 := by
  classical
  have hx : x∈EvenFrom G x := by simp [EvenFrom,SimpleGraph.dist_self]
  have h1 := card_erase_of_mem hx
  change ((EvenFrom G x).erase x).card ≤ 5
  omega

private theorem odd_dist_to_even_next {m n : ℕ} (nm : n=m+1) (odd : ¬ Even m) :
    Even n := by
  rw [nm]
  simp only [Nat.even_iff] at odd ⊢
  omega

private theorem twins_dist_le (hc : G.Connected) {a b z : V} (az : a≠z)
    (same : ∀ v, v≠b → G.Adj a v → G.Adj b v) :
    G.dist b z ≤ G.dist a z := by
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist a z
  cases q with
  | nil => exact (az rfl).elim
  | @cons u v w e q =>
    simp only [Walk.length_cons] at ql
    by_cases eq : v=b
    · subst v
      have h := G.dist_le q
      omega
    · have h := G.dist_le (Walk.cons (same _ eq e) q)
      simp only [Walk.length_cons] at h
      omega

namespace Split
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)

private theorem left_boundary :
    ∀ u∈S.L, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈S.L := by
  intro u ul v uv
  rcases S.cover v with aa|bb|vl|vr
  · exact Or.inl aa
  · exact Or.inr (Or.inl bb)
  · exact Or.inr (Or.inr vl)
  · exact (S.cross _ ul _ vr uv).elim

private theorem right_boundary :
    ∀ u∈S.R, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈S.R := by
  intro u ur v uv
  rcases S.cover v with aa|bb|vl|vr
  · exact Or.inl aa
  · exact Or.inr (Or.inl bb)
  · exact (S.cross _ vl _ ur uv.symm).elim
  · exact Or.inr (Or.inr vr)

private theorem odd_equal (hc : G.Connected) (ab : G.Adj a b) {z : V}
    (oa : ¬Even (G.dist a z)) (ob : ¬Even (G.dist b z)) :
    G.dist a z = G.dist b z := by
  have a1 := dist_eq_one_iff_adj.mpr ab
  have b1 := dist_eq_one_iff_adj.mpr ab.symm
  have u := hc.dist_triangle (u:=a) (v:=b) (w:=z)
  have v := hc.dist_triangle (u:=b) (v:=a) (w:=z)
  simp only [Nat.even_iff] at oa ob
  omega

private theorem covered_even (hc : G.Connected) (ab : G.Adj a b)
    {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (xh : G.Adj a x ∨ G.Adj b x) (yh : G.Adj a y ∨ G.Adj b y)
    {z : V} (za : z≠a) (zb : z≠b) :
    z∈PositiveEven G a ∨ z∈PositiveEven G b ∨
      z∈PositiveEven G x ∨ z∈PositiveEven G y := by
  classical
  by_cases za' : Even (G.dist a z)
  · exact Or.inl (mem_positive.mpr ⟨za,za'⟩)
  by_cases zb' : Even (G.dist b z)
  · exact Or.inr (Or.inl (mem_positive.mpr ⟨zb,zb'⟩))
  have eq := odd_equal hc ab za' zb'
  rcases S.cover z with zz|zz|zl|zr
  · exact (za zz).elim
  · exact (zb zz).elim
  · have zo : z∉S.R := fun h=>disjoint_left.mp S.dis zl h
    have dk := cross_dist_of_equal S.R hc yr zo (right_boundary S) yh eq
    exact Or.inr (Or.inr (Or.inr (mem_positive.mpr
      ⟨fun e=>zo (e.symm ▸ yr),odd_dist_to_even_next dk za'⟩)))
  · have zo : z∉S.L := fun h=>disjoint_left.mp S.dis h zr
    have dk := cross_dist_of_equal S.L hc xl zo (left_boundary S) xh eq
    exact Or.inr (Or.inr (Or.inl (mem_positive.mpr
      ⟨fun e=>zo (e.symm ▸ xl),odd_dist_to_even_next dk za'⟩)))

private theorem order_le_twenty_one_of_overlap (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6) (ab : G.Adj a b)
    {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (xh : G.Adj a x ∨ G.Adj b x) (yh : G.Adj a y ∨ G.Adj b y)
    (overlap : ∃ z, (z∈PositiveEven G a ∨ z∈PositiveEven G b) ∧
      (z∈PositiveEven G x ∨ z∈PositiveEven G y)) :
    Fintype.card V≤21 := by
  classical
  let A := PositiveEven G a ∪ PositiveEven G b
  let B := PositiveEven G x ∪ PositiveEven G y
  obtain ⟨z,za,zb⟩ := overlap
  have za' : z∈A := mem_union.mpr za
  have zb' : z∈B := mem_union.mpr zb
  have h : A∪B = A∪B.erase z := by
    ext u
    simp only [mem_union,mem_erase]
    constructor
    · rintro (ua|ub)
      · exact Or.inl ua
      by_cases uz : u=z
      · exact Or.inl (uz.symm ▸ za')
      · exact Or.inr ⟨uz,ub⟩
    · exact fun e => e.imp id And.right
  have cA := card_union_le (PositiveEven G a) (PositiveEven G b)
  have cB := card_union_le (PositiveEven G x) (PositiveEven G y)
  have cB' := card_erase_of_mem zb'
  have ae := positive_card (even a)
  have be := positive_card (even b)
  have xe := positive_card (even x)
  have ye := positive_card (even y)
  have cc : (A∪B).card ≤ 19 := by
    rw [h]
    have k := card_union_le A (B.erase z)
    dsimp only [A,B] at k cB' ⊢
    omega
  have cov : (univ : Finset V) ⊆ insert a (insert b (A∪B)) := by
    intro u _
    by_cases ua : u=a
    · simp [ua]
    by_cases ub : u=b
    · simp [ub]
    rcases covered_even S hc ab xl yr xh yh ua ub with k|k|k|k <;>
      simp [A,B,k]
  have cv := card_le_card cov
  rw [card_univ] at cv
  have c1 := card_insert_le a (insert b (A∪B))
  have c2 := card_insert_le b (A∪B)
  omega

theorem order_le_seventeen_of_twins (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6) (ab : G.Adj a b)
    {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (xh : G.Adj a x ∨ G.Adj b x) (yh : G.Adj a y ∨ G.Adj b y)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z)) :
    Fintype.card V≤17 := by
  classical
  let A := PositiveEven G a
  let B := PositiveEven G x ∪ PositiveEven G y
  have ae := positive_card (even a)
  have xe := positive_card (even x)
  have ye := positive_card (even y)
  have cB := card_union_le (PositiveEven G x) (PositiveEven G y)
  have cc := card_union_le A B
  have cov : (univ : Finset V) ⊆ insert a (insert b (A∪B)) := by
    intro u _
    by_cases ua : u=a
    · simp [ua]
    by_cases ub : u=b
    · simp [ub]
    have e1 := twins_dist_le hc (Ne.symm ua)
      (fun v vb av=> (twin v av.ne.symm vb).mp av)
    have e2 := twins_dist_le hc (Ne.symm ub)
      (fun v va bv=> (twin v va bv.ne.symm).mpr bv)
    have eq : G.dist a u = G.dist b u := by omega
    rcases covered_even S hc ab xl yr xh yh ua ub with k|k|k|k
    · simp [A,k]
    · have ka := mem_positive.mpr ⟨ua,eq.symm ▸ (mem_positive.mp k).2⟩
      simp [A,ka]
    · simp [B,k]
    · simp [B,k]
  have cv := card_le_card cov
  rw [card_univ] at cv
  have c1 := card_insert_le a (insert b (A∪B))
  have c2 := card_insert_le b (A∪B)
  dsimp only [A,B] at cc cv c1 c2
  omega

theorem order_le_twenty_one_of_adjacent_cut (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6) (ab : G.Adj a b)
    (rightA : ∃ x∈S.R, G.Adj a x) (rightB : ∃ x∈S.R, G.Adj b x) :
    Fintype.card V≤21 := by
  classical
  obtain ⟨la,lah,ala⟩ := S.leftA
  obtain ⟨lb,lbh,blb⟩ := S.leftB
  obtain ⟨ra,rah,ara⟩ := rightA
  obtain ⟨rb,rbh,brb⟩ := rightB
  by_cases twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z)
  · exact (order_le_seventeen_of_twins S hc even ab lah rah (.inl ala) (.inl ara) twin).trans (by decide)
  push_neg at twin
  obtain ⟨z,za,zb,ex⟩ := twin
  have loc : z∈S.L ∨ z∈S.R := by
    rcases S.cover z with h|h|h|h
    · exact (za h).elim
    · exact (zb h).elim
    · exact .inl h
    · exact .inr h
  have ol (v : V) (vl : v∈S.L) (vr : z∈S.R)
      (d : ∃ c, G.Adj v c ∧ G.Adj c z) : z∈PositiveEven G v := by
    obtain ⟨c,vc,cz⟩ := d
    have eq := d2 (x:=v) (z:=z) hc (fun h=>disjoint_left.mp S.dis vl (h ▸ vr))
      (S.cross v vl z vr) vc cz
    exact mem_positive.mpr ⟨fun h=>disjoint_left.mp S.dis (h ▸ vl) vr,by simp [(mem_filter.mp eq).2]⟩
  have or' (v : V) (vr : v∈S.R) (vl : z∈S.L)
      (d : ∃ c, G.Adj v c ∧ G.Adj c z) : z∈PositiveEven G v := by
    obtain ⟨c,vc,cz⟩ := d
    have eq := d2 (x:=v) (z:=z) hc (fun h=>disjoint_left.mp S.dis (h.symm ▸ vl) vr)
      (fun h=>S.cross z vl v vr h.symm) vc cz
    exact mem_positive.mpr ⟨fun h=>disjoint_left.mp S.dis vl (h ▸ vr),by simp [(mem_filter.mp eq).2]⟩
  by_cases az : G.Adj a z
  · have bz : ¬G.Adj b z := (ex.resolve_right (fun h=>h.1 az)).2
    have db := d2 hc (Ne.symm zb) bz ab.symm az
    have pe : z∈PositiveEven G b := mem_positive.mpr ⟨zb,by simp [(mem_filter.mp db).2]⟩
    rcases loc with zl|zr
    · exact order_le_twenty_one_of_overlap S hc even ab lah rah (.inl ala) (.inl ara)
        ⟨z,.inr pe,.inr (or' ra rah zl ⟨a,ara.symm,az⟩)⟩
    · exact order_le_twenty_one_of_overlap S hc even ab lah rah (.inl ala) (.inl ara)
        ⟨z,.inr pe,.inl (ol la lah zr ⟨a,ala.symm,az⟩)⟩
  have bz : G.Adj b z := (ex.resolve_left (fun h=>az h.1)).2
  have da := d2 hc (Ne.symm za) az ab bz
  have pe : z∈PositiveEven G a := mem_positive.mpr ⟨za,by simp [(mem_filter.mp da).2]⟩
  rcases loc with zl|zr
  · exact order_le_twenty_one_of_overlap S hc even ab lbh rbh (.inr blb) (.inr brb)
      ⟨z,.inl pe,.inr (or' rb rbh zl ⟨b,brb.symm,bz⟩)⟩
  · exact order_le_twenty_one_of_overlap S hc even ab lbh rbh (.inr blb) (.inr brb)
      ⟨z,.inl pe,.inl (ol lb lbh zr ⟨b,blb.symm,bz⟩)⟩

#print axioms order_le_twenty_one_of_adjacent_cut
end Split
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
