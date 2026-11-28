import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SixCentreParity189

namespace Graffiti189Adam
set_option linter.unusedSectionVars false
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {a b : V}

/-- A two-side separator. No degree hypothesis is included. -/
structure Separator (G : SimpleGraph V) (a b : V) where
  conn : G.Connected
  sides : Bool → Finset V
  disj : Disjoint (sides false) (sides true)
  not_a : ∀ i, a ∉ sides i
  not_b : ∀ i, b ∉ sides i
  covers : ∀ x, x = a ∨ x = b ∨ x ∈ sides false ∨ x ∈ sides true
  closed : ∀ i x, x ∈ sides i → ∀ y, G.Adj x y → y = a ∨ y = b ∨ y ∈ sides i

variable (S : Separator G a b)

theorem cross_distance {i j : Bool} (hij : i ≠ j) {x y : V}
    (hx : x ∈ S.sides i) (hy : y ∈ S.sides j) :
    G.dist x y = min (G.dist x a + G.dist a y) (G.dist x b + G.dist b y) := by
  have hDj : Disjoint (S.sides i) (S.sides j) := by
    cases i <;> cases j
    · contradiction
    · exact S.disj
    · exact S.disj.symm
    · contradiction
  have crossing {u v : V} (w : G.Walk u v) (hu : u ∈ S.sides i) (hv : v ∉ S.sides i) :
      a ∈ w.support ∨ b ∈ w.support := by
    induction w with
    | nil => exact (hv hu).elim
    | @cons u z v uz w ih =>
      rcases S.closed i u hu z uz with rfl|rfl|hz
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih hz hv).imp (fun h => by simp [h]) (fun h => by simp [h])
  apply Nat.le_antisymm
  · exact le_min (S.conn.dist_triangle (v:=a)) (S.conn.dist_triangle (v:=b))
  obtain ⟨w,wl⟩ := S.conn.exists_walk_length_eq_dist x y
  rcases crossing w hx (fun hi => disjoint_left.mp hDj hi hy) with ha|hb
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp ha
    have hh : w.length=p.length+q.length := by rw [eq,length_append]
    exact (min_le_left _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp hb
    have hh : w.length=p.length+q.length := by rw [eq,length_append]
    exact (min_le_right _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)

noncomputable def ev (G : SimpleGraph V) (c x : V) : ℕ :=
  if G.dist c x % 2 = 0 then 1 else 0

noncomputable def evAmount (G : SimpleGraph V) (c : V) (A : Finset V) : ℕ :=
  ∑ x ∈ A, ev G c x

noncomputable def cov (G : SimpleGraph V) (a b p q x : V) : ℕ :=
  ev G a x + ev G b x + ev G p x + ev G q x

def EvenBudget (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ x, evAmount G x univ ≤ d+1

private theorem ev_dist_zero (x : V) : ev G x x = 1 := by simp [ev,SimpleGraph.dist_self]

private theorem ev_of_dist_two {x y : V} (h : G.dist x y = 2) : ev G x y = 1 := by
  simp [ev,h]

private theorem port_extra {i : Bool} {y : V} (hy : y ∈ S.sides i)
    (hya : G.Adj y a) (hab : G.dist a b = 3) :
    ∃ t, t ≠ y ∧ (t = b ∨ t ∈ S.sides i) ∧ ev G y t = 1 := by
  have hya' : G.dist y a = 1 := dist_eq_one_iff_adj.2 hya
  have h₂ := S.conn.dist_triangle (u:=a) (v:=y) (w:=b)
  rw [dist_comm (G:=G) (u:=a) (v:=y),hya',hab] at h₂
  have h₄ := S.conn.dist_triangle (u:=y) (v:=a) (w:=b)
  rw [hya',hab] at h₄
  have hRange : G.dist y b = 2 ∨ G.dist y b = 3 ∨ G.dist y b = 4 := by omega
  rcases hRange with h|h|h
  · refine ⟨b,?_,Or.inl rfl,by simp [ev,h]⟩
    intro he; subst b; simp [SimpleGraph.dist_self] at h
  · obtain ⟨w,hw⟩ := S.conn.exists_walk_length_eq_dist y b
    have hw' : w.length = 3 := hw.trans h
    cases w with
    | nil => simp at hw'
    | @cons _ u _ h₁ w =>
      cases w with
      | nil => simp at hw'
      | @cons _ t _ h₂' w =>
        cases w with
        | nil => simp at hw'
        | @cons _ z _ h₃ w =>
          cases w with
          | @cons => simp at hw'
          | nil =>
            have hut : G.dist u b ≤ 2 := G.dist_le (.cons h₂' (.cons h₃ .nil))
            have htb : G.dist t b = 1 := dist_eq_one_iff_adj.2 h₃
            have huu : u ≠ a := by intro he; subst u; omega
            have hub : u ≠ b := by
              intro he; subst u
              have := dist_eq_one_iff_adj.2 h₁
              omega
            have hta : t ≠ a := by intro he; subst t; omega
            have htb' : t ≠ b := h₃.ne
            have hus : u ∈ S.sides i := ((S.closed i y hy u h₁).resolve_left huu).resolve_left hub
            have hts : t ∈ S.sides i := ((S.closed i u hus t h₂').resolve_left hta).resolve_left htb'
            have hYt : G.dist y t = 2 := by
              have hUpper : G.dist y t ≤ 2 := G.dist_le (.cons h₁ (.cons h₂' .nil))
              have hLower := S.conn.dist_triangle (u:=y) (v:=t) (w:=b)
              omega
            refine ⟨t,?_,Or.inr hts,ev_of_dist_two hYt⟩
            intro he; subst t; simp [SimpleGraph.dist_self] at hYt
  · refine ⟨b,?_,Or.inl rfl,by simp [ev,h]⟩
    intro he; subst b; simp [SimpleGraph.dist_self] at h

private def swap (S : Separator G a b) : Separator G b a where
  conn := S.conn
  sides := S.sides
  disj := S.disj
  not_a := S.not_b
  not_b := S.not_a
  covers x := by
    rcases S.covers x with h|h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  closed i x hx y had := by
    rcases S.closed i x hx y had with h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

private theorem amount_mono {c : V} {X Y : Finset V} (h : X ⊆ Y) :
    evAmount G c X ≤ evAmount G c Y := Finset.sum_le_sum_of_subset h

private theorem amount_insert {c x : V} {A : Finset V} (hx : x ∉ A) :
    evAmount G c (insert x A) = ev G c x + evAmount G c A :=
  Finset.sum_insert hx

private theorem amount_union {c : V} {A B : Finset V} (h : Disjoint A B) :
    evAmount G c (A ∪ B) = evAmount G c A + evAmount G c B :=
  Finset.sum_union h

private theorem terminal_amount (d : ℕ) (hb : EvenBudget G d)
    {t : V} (ht0 : t ∉ S.sides false) (ht1 : t ∉ S.sides true) :
    evAmount G t (S.sides false) + evAmount G t (S.sides true) ≤ d := by
  have ht : t ∉ S.sides false ∪ S.sides true := by simp [ht0,ht1]
  have hh : evAmount G t (insert t (S.sides false ∪ S.sides true)) ≤ evAmount G t univ :=
    amount_mono (Finset.subset_univ _)
  rw [amount_insert ht,amount_union S.disj,ev_dist_zero] at hh
  exact Nat.le_of_succ_le_succ (by have := hb t; omega)

private theorem port_amount (d : ℕ) (hBudget : EvenBudget G d)
    {i j : Bool} (hij : i ≠ j) {y : V} (hy : y ∈ S.sides i)
    (ht : ∃ t, t ≠ y ∧ (t = a ∨ t = b ∨ t ∈ S.sides i) ∧ ev G y t = 1) :
    evAmount G y (S.sides j) + 2 ≤ d+1 := by
  have hD : Disjoint (S.sides i) (S.sides j) := by
    cases i <;> cases j
    · contradiction
    · exact S.disj
    · exact S.disj.symm
    · contradiction
  obtain ⟨t,hty,hts,hte⟩ := ht
  have hn : y ∉ S.sides j := disjoint_left.1 hD hy
  have hh : t ∉ S.sides j := by
    rcases hts with rfl|rfl|h
    · exact S.not_a j
    · exact S.not_b j
    · exact disjoint_left.1 hD h
  have hyn : y ∉ insert t (S.sides j) := by simp [hty.symm,hn]
  have hh' : evAmount G y (insert y (insert t (S.sides j))) ≤ evAmount G y univ :=
    amount_mono (Finset.subset_univ _)
  rw [amount_insert hyn, amount_insert hh,ev_dist_zero,hte] at hh'
  have := hBudget y
  omega

private theorem port_amount_a (d : ℕ) (hBudget : EvenBudget G d)
    {i j : Bool} (hij : i ≠ j) {y : V} (hy : y ∈ S.sides i)
    (hya : G.Adj y a) (hab : G.dist a b = 3) :
    evAmount G y (S.sides j) + 2 ≤ d+1 := by
  obtain ⟨t,ht,hs,he⟩ := port_extra S hy hya hab
  exact port_amount S d hBudget hij hy ⟨t,ht,Or.inr hs,he⟩

private theorem port_amount_b (d : ℕ) (hBudget : EvenBudget G d)
    {i j : Bool} (hij : i ≠ j) {y : V} (hy : y ∈ S.sides i)
    (hyb : G.Adj y b) (hab : G.dist a b = 3) :
    evAmount G y (S.sides j) + 2 ≤ d+1 := by
  obtain ⟨t,ht,hs,he⟩ := port_extra (swap S) hy hyb
    ((dist_comm (G:=G) (u:=b) (v:=a)).trans hab)
  exact port_amount S d hBudget hij hy
    ⟨t,ht,hs.elim Or.inl (fun h => Or.inr (Or.inr h)),he⟩

private theorem partition_card (hab : G.dist a b = 3) :
    Fintype.card V = (S.sides false).card + (S.sides true).card + 2 := by
  have hne : a ≠ b := by intro h; subst b; simp [SimpleGraph.dist_self] at hab
  have hay : a ∉ insert b (S.sides false ∪ S.sides true) := by
    simp [hne, S.not_a]
  have hby : b ∉ S.sides false ∪ S.sides true := by simp [S.not_b]
  have he : (univ : Finset V) = insert a (insert b (S.sides false ∪ S.sides true)) := by
    ext x
    simp only [mem_univ, mem_insert, mem_union, true_iff]
    exact S.covers x
  calc
    Fintype.card V = (univ : Finset V).card := card_univ.symm
    _ = _ := by rw [he,card_insert_of_not_mem hay,card_insert_of_not_mem hby,
                     card_union_of_disjoint S.disj]

private theorem sum_cov (p q : V) (A : Finset V) :
    ∑ x ∈ A, cov G a b p q x =
      evAmount G a A + evAmount G b A + evAmount G p A + evAmount G q A := by
  simp only [cov, evAmount, Finset.sum_add_distrib]

/-- Each terminal pays one extra incidence (itself); each port pays two.
    No degree or connectivity-after-deleting-the-cut hypothesis is needed. -/
theorem six_centre_sum (d : ℕ) (hBudget : EvenBudget G d) (hab : G.dist a b = 3)
    {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hra : G.Adj r a) (hsb : G.Adj s b) :
    (∑ x ∈ S.sides false, cov G a b r s x) +
      (∑ x ∈ S.sides true, cov G a b p q x) + 10 ≤ 6*(d+1) := by
  have ha := terminal_amount S d hBudget (S.not_a false) (S.not_a true)
  have hb := terminal_amount S d hBudget (S.not_b false) (S.not_b true)
  have h₁ := port_amount_a S d hBudget (by decide : false ≠ true) hp hpa hab
  have h₂ := port_amount_b S d hBudget (by decide : false ≠ true) hq hqb hab
  have h₃ := port_amount_a S d hBudget (by decide : true ≠ false) hr hra hab
  have h₄ := port_amount_b S d hBudget (by decide : true ≠ false) hs hsb hab
  rw [sum_cov,sum_cov]
  omega

noncomputable def failures (A : Finset V) (f : V → ℕ) : ℕ :=
  (A.filter (fun x => f x = 1)).card

noncomputable def gains (A : Finset V) (f : V → ℕ) : ℕ :=
  (A.filter (fun x => 3 ≤ f x)).card

private theorem sum_cov_lower (A : Finset V) (f : V → ℕ) (h : ∀ x ∈ A, 0 < f x) :
    2*A.card + gains A f ≤ (∑ x ∈ A, f x) + failures A f := by
  have hs : (∑ x ∈ A, (2 + (if 3 ≤ f x then 1 else 0))) ≤
      (∑ x ∈ A, (f x + (if f x = 1 then 1 else 0))) := by
    apply Finset.sum_le_sum
    intro x hx
    have := h x hx
    split <;> split <;> omega
  have indicator (P : V → Prop) [DecidablePred P] :
      (∑ x ∈ A, if P x then (1 : ℕ) else 0) = (A.filter P).card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,indicator,indicator] at hs
  simpa [failures,gains,Finset.sum_const,Nat.mul_comm] using hs

/-- The exact integral form of n ≤ 3d + (f−g)/2. -/
theorem six_centre_bound_of_positive (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hra : G.Adj r a) (hsb : G.Adj s b)
    (hX : ∀ x ∈ S.sides false, 0 < cov G a b r s x)
    (hY : ∀ x ∈ S.sides true, 0 < cov G a b p q x) :
    2*Fintype.card V + gains (S.sides false) (cov G a b r s) +
        gains (S.sides true) (cov G a b p q) ≤
      6*d + failures (S.sides false) (cov G a b r s) +
        failures (S.sides true) (cov G a b p q) := by
  have h₁ := six_centre_sum S d hBudget hab hp hq hr hs hpa hqb hra hsb
  have h₂ := partition_card S hab
  have h₃ := sum_cov_lower (S.sides false) (cov G a b r s) hX
  have h₄ := sum_cov_lower (S.sides true) (cov G a b p q) hY
  omega

theorem coverage_distances {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : G.Adj p a) (hqb : G.Adj q b) :
    cov G a b p q x =
    Graffiti189SixCentre.coverage (G.dist x a) (G.dist x b) (G.dist p b) (G.dist q a) := by
  have ep := cross_distance S hij hp hx
  have eq := cross_distance S hij hq hx
  rw [dist_eq_one_iff_adj.2 hpa] at ep
  rw [dist_eq_one_iff_adj.2 hqb] at eq
  unfold cov ev Graffiti189SixCentre.coverage Graffiti189SixCentre.evenBit
  rw [ep, eq, dist_comm (G:=G) (u:=a) (v:=x), dist_comm (G:=G) (u:=b) (v:=x)]
  rw [Nat.add_comm 1 (G.dist x a), Nat.add_comm (G.dist p b) (G.dist x b),
      Nat.add_comm (G.dist q a) (G.dist x a), Nat.add_comm 1 (G.dist x b)]

include S in
private theorem dist_diff (hab : G.dist a b = 3) (x : V) :
    G.dist x a ≤ G.dist x b + 3 ∧ G.dist x b ≤ G.dist x a + 3 := by
  have ha := S.conn.dist_triangle (u:=x) (v:=b) (w:=a)
  have hb := S.conn.dist_triangle (u:=x) (v:=a) (w:=b)
  rw [dist_comm (G:=G) (u:=b) (v:=a),hab] at ha
  rw [hab] at hb
  exact ⟨ha,hb⟩

include S in
private theorem opposite_range (hab : G.dist a b = 3) {p q : V}
    (hpa : G.Adj p a) (hqb : G.Adj q b) :
    2 ≤ G.dist p b ∧ G.dist p b ≤ 4 ∧ 2 ≤ G.dist q a ∧ G.dist q a ≤ 4 := by
  have hp := dist_diff S hab p
  have hq := dist_diff S hab q
  have hpa' := dist_eq_one_iff_adj.2 hpa
  have hqb' := dist_eq_one_iff_adj.2 hqb
  have hlp := S.conn.dist_triangle (u:=a) (v:=p) (w:=b)
  rw [dist_comm (G:=G) (u:=a) (v:=p),hpa',hab] at hlp
  have hlq := S.conn.dist_triangle (u:=a) (v:=q) (w:=b)
  rw [dist_comm (G:=G) (u:=a) (v:=q),hqb',hab] at hlq
  omega

theorem coverage_positive_graph (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : G.Adj p a) (hqb : G.Adj q b) :
    0 < cov G a b p q x := by
  rw [coverage_distances S hij hp hq hx hpa hqb]
  obtain ⟨hα,hβ⟩ := dist_diff S hab x
  obtain ⟨h₁,h₂,h₃,h₄⟩ := opposite_range S hab hpa hqb
  exact Graffiti189SixCentre.coverage_positive _ _ _ _ hα hβ h₁ h₂ h₃ h₄

/-- The graph-level six-centre bound; no minimum-degree premise. -/
theorem six_centre_bound (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hra : G.Adj r a) (hsb : G.Adj s b) :
    2*Fintype.card V + gains (S.sides false) (cov G a b r s) +
        gains (S.sides true) (cov G a b p q) ≤
      6*d + failures (S.sides false) (cov G a b r s) +
        failures (S.sides true) (cov G a b p q) :=
  six_centre_bound_of_positive S d hBudget hab hp hq hr hs hpa hqb hra hsb
    (fun _ hx => coverage_positive_graph S hab (by decide) hr hs hx hra hsb)
    (fun _ hy => coverage_positive_graph S hab (by decide) hp hq hy hpa hqb)

private theorem fail_zero (A : Finset V) (f : V → ℕ) (h : ∀ x ∈ A, 2 ≤ f x) :
    failures A f = 0 := by
  unfold failures
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_not_mem.2
  intro x hx
  obtain ⟨ha,hf⟩ := Finset.mem_filter.1 hx
  have := h x ha
  omega

theorem coverage_far_graph (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hpb : G.dist p b = 4) (hqa : G.dist q a = 4) :
    2 ≤ cov G a b p q x := by
  rw [coverage_distances S hij hp hq hx hpa hqb,hpb,hqa]
  obtain ⟨hα,hβ⟩ := dist_diff S hab x
  exact Graffiti189SixCentre.coverage_far_at_least_two _ _ hα hβ

/-- Four far ports force the desired n ≤ 3d order bound. -/
theorem six_centre_far (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hra : G.Adj r a) (hsb : G.Adj s b)
    (hpb : G.dist p b = 4) (hqa : G.dist q a = 4)
    (hrb : G.dist r b = 4) (hsa : G.dist s a = 4) :
    Fintype.card V ≤ 3*d := by
  have h := six_centre_bound S d hBudget hab hp hq hr hs hpa hqb hra hsb
  rw [fail_zero _ _ (fun _ hx => coverage_far_graph S hab (by decide) hr hs hx hra hsb hrb hsa),
      fail_zero _ _ (fun _ hx => coverage_far_graph S hab (by decide) hp hq hx hpa hqb hpb hqa)] at h
  omega

/-- The arithmetic coverage table is the exact number of incidences in the graph. -/
theorem coverage_table_graph (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : G.Adj p a) (hqb : G.Adj q b) :
    cov G a b p q x =
      if G.dist x b ≤ G.dist x a then
        Graffiti189SixCentre.entry (G.dist x a - G.dist x b) (G.dist x b) (G.dist p b)
      else
        Graffiti189SixCentre.entry (G.dist x b - G.dist x a) (G.dist x a) (G.dist q a) := by
  rw [coverage_distances S hij hp hq hx hpa hqb]
  obtain ⟨hα,hβ⟩ := dist_diff S hab x
  obtain ⟨h₁,h₂,h₃,h₄⟩ := opposite_range S hab hpa hqb
  exact Graffiti189SixCentre.coverage_table _ _ _ _ hα hβ h₁ h₂ h₃ h₄

/-- The notation really counts vertices at even shortest-path distance,
including the centre itself when the finset contains it. -/
theorem evAmount_eq_card (c : V) (A : Finset V) :
    evAmount G c A = (A.filter (fun x => G.dist c x % 2 = 0)).card := by
  unfold evAmount ev
  rw [← Finset.sum_filter]
  simp

/-- Defect and gain need not both vanish; the count also closes when the
ports can be chosen so that the gains make up for the failures. -/
theorem six_centre_nonpositive_defect (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hra : G.Adj r a) (hsb : G.Adj s b)
    (hDefect :
      failures (S.sides false) (cov G a b r s) + failures (S.sides true) (cov G a b p q) ≤
      gains (S.sides false) (cov G a b r s) + gains (S.sides true) (cov G a b p q)) :
    Fintype.card V ≤ 3*d := by
  have h := six_centre_bound S d hBudget hab hp hq hr hs hpa hqb hra hsb
  omega

#print axioms cross_distance
#print axioms coverage_distances
#print axioms coverage_table_graph
#print axioms six_centre_sum
#print axioms evAmount_eq_card
#print axioms six_centre_bound
#print axioms six_centre_nonpositive_defect
#print axioms six_centre_far

end Graffiti189Adam
