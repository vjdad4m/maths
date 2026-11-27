import PentagonRead133
import SixCycle133

namespace Graffiti133Pentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def Outside (c : Fin 5 → V) (x : V) : Prop := ∀ i, x ≠ c i
def One (G : SimpleGraph V) (c : Fin 5 → V) (x : V) (i : Fin 5) : Prop :=
  Outside c x ∧ ∀ j, G.Adj x (c j) ↔ j = i
def Two (G : SimpleGraph V) (c : Fin 5 → V) (x : V) (i : Fin 5) : Prop :=
  Outside c x ∧ ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i+1

structure PentagonFrame (G : SimpleGraph V) where
  c : Fin 5 → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ pent i j
  h4 : FourCycleFree G
  noP6 : ¬ ∃ f : Fin 6 → V, InducedPath G f
  dom : ∀ x, Outside c x → ∃ i, G.Adj x (c i)

theorem make_frame (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : ¬NoSimpleFive133 G) (no : ¬ ∃ f : Fin 6 → V, InducedPath G f) :
    Nonempty (PentagonFrame G) := by
  classical
  unfold NoSimpleFive133 at h5
  push_neg at h5
  obtain ⟨a,b,c,d,e,hn,hAB,hBC,hCD,hDE,hEA⟩ := h5
  let f : Fin 5 → V := ![a,b,c,d,e]
  have inj : Function.Injective f := by
    apply List.nodup_ofFn.mp
    simpa [f,List.ofFn_succ] using hn
  have hside (i : Fin 5) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    all_goals first | exact hAB | exact hBC | exact hCD | exact hDE | exact hEA.1
  have hrel := cycle_pentagon h4 inj hside
  have step (u v : V) (e : G.Adj u v)
      (hu : Outside f u → ∃ i, G.Adj u (f i)) :
      Outside f v → ∃ i, G.Adj v (f i) := by
    intro hv
    by_cases uu : Outside f u
    · apply Classical.byContradiction
      intro none
      obtain ⟨p,hp,h0,htail⟩ := extend_pentagon h4 inj hrel u uu (hu uu)
      have hn : ∀ i, v ≠ p i := by
        intro i he
        by_cases hh : i.val = 0
        · have eq : i = 0 := Fin.ext hh
          rw [eq,h0] at he
          exact e.ne he.symm
        · obtain ⟨j,hj⟩ := htail i (Nat.pos_of_ne_zero hh)
          exact hv j (he.trans hj)
      have ha : G.Adj v (p 0) := h0.symm ▸ e.symm
      have hn' (i : Fin 5) (hi : 0 < i.val) : ¬ G.Adj v (p i) := by
        intro er
        obtain ⟨j,hj⟩ := htail i hi
        exact none ⟨j,hj ▸ er⟩
      obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp v hn ha hn'
      exact no ⟨q,hq⟩
    · have h : ∃ i, u = f i := by
        apply Classical.byContradiction
        intro bad
        exact uu (fun i eq => bad ⟨i,eq⟩)
      obtain ⟨i,hi⟩ := h
      exact ⟨i,hi ▸ e.symm⟩
  refine ⟨⟨f,inj,hrel,h4,no,?_⟩⟩
  intro x
  obtain ⟨p⟩ := hc (f 0) x
  have seed : Outside f (f 0) → ∃ i, G.Adj (f 0) (f i) :=
    fun h => (h 0 rfl).elim
  have walkprop {a b : V} (p : G.Walk a b)
      (ha : Outside f a → ∃ i, G.Adj a (f i)) :
      Outside f b → ∃ i, G.Adj b (f i) := by
    induction p with
    | nil => exact ha
    | cons e q ih => exact ih (step _ _ e ha)
  exact walkprop p seed

namespace PentagonFrame
variable (F : PentagonFrame G)

private lemma finite_contact : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j = true ↔ j = i) ∨ (∃ i, ∀ j, b j = true ↔ j = i ∨ j = i+1) := by
  decide

lemma contact_sep2 {x : V} (hx : Outside F.c x) (i : Fin 5)
    (h : G.Adj x (F.c i)) : ¬G.Adj x (F.c (i+2)) := by
  intro e
  have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
    (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (F.inj w)) h.symm e.symm
    ((F.adj _ _).mpr (Or.inl rfl))
    ((F.adj _ _).mpr (Or.inr (by fin_cases i <;> decide)))
  exact hx _ eq

theorem classify_contact (x : V) (hx : Outside F.c x) :
    (∃ i, One G F.c x i) ∨ (∃ i, Two G F.c x i) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (F.c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases he : b (i+2)
    · rfl
    · exact (F.contact_sep2 hx i ((btrue _).mp h) ((btrue _).mp he)).elim
  obtain ⟨i,hi⟩ := F.dom x hx
  rcases finite_contact b sep ⟨i,(btrue _).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx,fun w => (btrue _).symm.trans (hj w)⟩
  · exact Or.inr ⟨j,hx,fun w => (btrue _).symm.trans (hj w)⟩

private lemma forbidden_site {x y : V} (hx : Outside F.c x) (hy : Outside F.c y)
    (e : G.Adj x y) {i j : Fin 5} (hi : G.Adj x (F.c i)) (hj : G.Adj y (F.c j)) :
    ¬pent i j := by
  intro h
  have eq := F.h4 x (F.c j) y (F.c i) (hx j) e hj.symm hi ((F.adj _ _).mpr h).symm
  exact hy i eq

private lemma one_slots : ∀ i j : Fin 5, ¬pent i j → j = i ∨ j = i+2 ∨ j = i+3 := by decide
private lemma two_slots : ∀ i j : Fin 5, ¬pent i j → ¬pent (i+1) j → j = i+3 := by decide

theorem outside_to_one {x y : V} {i : Fin 5} (hx : One G F.c x i) (hy : Outside F.c y)
    (e : G.Adj x y) {j : Fin 5} (hj : G.Adj y (F.c j)) :
    j = i ∨ j = i+2 ∨ j = i+3 :=
  one_slots i j (F.forbidden_site hx.1 hy e ((hx.2 _).mpr rfl) hj)

theorem outside_to_two {x y : V} {i : Fin 5} (hx : Two G F.c x i) (hy : Outside F.c y)
    (e : G.Adj x y) {j : Fin 5} (hj : G.Adj y (F.c j)) : j = i+3 :=
  two_slots i j (F.forbidden_site hx.1 hy e ((hx.2 _).mpr (Or.inl rfl)) hj)
    (F.forbidden_site hx.1 hy e ((hx.2 _).mpr (Or.inr rfl)) hj)

theorem same_site_neighbors {x y z : V} (hx : Outside F.c x)
    (e1 : G.Adj x y) (e2 : G.Adj x z) {j : Fin 5}
    (hy : G.Adj y (F.c j)) (hz : G.Adj z (F.c j)) : y = z :=
  F.h4 x (F.c j) y z (hx j) e1 hy.symm e2 hz.symm

theorem memLocalSet {v : V} {A : Finset V} :
    A ∈ localIndependentSets G v ↔ (∀ x ∈ A, G.Adj v x) ∧
      (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) := by
  classical
  simp only [localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_univ, true_and]

theorem maxLocalSet (v : V) :
    ∃ A ∈ localIndependentSets G v, A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, memLocalSet.mpr (by simp)⟩
  exact ⟨A,hA,le_antisymm (Finset.le_sup (f := Finset.card) hA)
    (Finset.sup_le_iff.mpr hM)⟩

private def Stamp (y : V) (j : Fin 5) : Prop :=
  y = F.c j ∨ (Outside F.c y ∧ G.Adj y (F.c j))

private theorem stamp_exists (y : V) : ∃ j, F.Stamp y j := by
  by_cases hi : Outside F.c y
  · obtain ⟨j,h⟩ := F.dom y hi
    exact ⟨j,Or.inr ⟨hi,h⟩⟩
  · apply Classical.byContradiction
    intro bad
    exact hi (fun j e => bad ⟨j,Or.inl e⟩)

private theorem stamp_inj {x y z : V} {j : Fin 5} (hx : Outside F.c x)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬ G.Adj y z)
    (sy : F.Stamp y j) (sz : F.Stamp z j) : y = z := by
  rcases sy with sy | ⟨hy,e1⟩ <;> rcases sz with sz | ⟨hz,e2⟩
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ e2.symm)).elim
  · exact (no (sz.symm ▸ e1)).elim
  · exact F.same_site_neighbors hx ey ez e1 e2

noncomputable def label (y : V) : Fin 5 := Classical.choose (F.stamp_exists y)
private theorem label_stamp (y : V) : F.Stamp y (F.label y) :=
  Classical.choose_spec (F.stamp_exists y)

private theorem label_inj {x : V} (hx : Outside F.c x)
    (A : Finset V) (hA : A ∈ localIndependentSets G x) :
    Set.InjOn F.label (↑A : Set V) := by
  obtain ⟨hN,hI⟩ := memLocalSet.mp hA
  intro y hy z hz he
  exact F.stamp_inj hx (hN _ hy) (hN _ hz) (hI _ hy _ hz)
    (F.label_stamp y) (he.symm ▸ F.label_stamp z)

private theorem label_one_range {x y : V} {i : Fin 5} (hx : One G F.c x i)
    (e : G.Adj x y) : F.label y = i ∨ F.label y = i+2 ∨ F.label y = i+3 := by
  rcases F.label_stamp y with h | ⟨hy,e2⟩
  · exact Or.inl ((hx.2 _).mp (h ▸ e))
  · exact F.outside_to_one hx hy e e2

private theorem label_two_range {x y : V} {i : Fin 5} (hx : Two G F.c x i)
    (e : G.Adj x y) : F.label y = i ∨ F.label y = i+1 ∨ F.label y = i+3 := by
  rcases F.label_stamp y with h | ⟨hy,e2⟩
  · rcases (hx.2 _).mp (h ▸ e) with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (F.outside_to_two hx hy e e2))

theorem local_one_le_three {x : V} {i : Fin 5} (hx : One G F.c x i) :
    localIndependence G x ≤ 3 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  let seats : Finset (Fin 5) := {i,i+2,i+3}
  have hbase : A.card ≤ seats.card := Finset.card_le_card_of_injOn F.label
    (fun y hy => by simpa [seats] using F.label_one_range hx ((memLocalSet.mp hA).1 y hy))
    (F.label_inj hx.1 A hA)
  exact hbase.trans ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (by simp))))

theorem local_two_le_two {x : V} {i : Fin 5} (hx : Two G F.c x i) :
    localIndependence G x ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  let rho (y : V) := if F.label y = i+1 then i else F.label y
  let seats : Finset (Fin 5) := {i,i+3}
  have neq : ∀ i : Fin 5, i ≠ i+1 ∧ i+3 ≠ i+1 := by decide
  have disj (j : Fin 5) (h : j = i ∨ j = i+1)
      {y : V} (e : G.Adj x y) (h' : F.Stamp y j) : y = F.c j := by
    rcases h' with e | ⟨hy,he⟩
    · exact e
    · have eq := F.outside_to_two hx hy e he
      rcases h with h | h
      · exact ((show i ≠ i+3 by fin_cases i <;> decide) (h.symm.trans eq)).elim
      · exact ((show i+1 ≠ i+3 by fin_cases i <;> decide) (h.symm.trans eq)).elim
  have hmap (y : V) (hy : y ∈ A) : rho y ∈ seats := by
    rcases F.label_two_range hx ((memLocalSet.mp hA).1 y hy) with e | e | e
    · simp [rho,seats,e,(neq i).1]
    · simp [rho,seats,e]
    · simp [rho,seats,e,(neq i).2]
  have hInj : Set.InjOn rho (↑A : Set V) := by
    intro y hy z hz he
    obtain ⟨hh,hI⟩ := memLocalSet.mp hA
    have hY := F.label_two_range hx (hh y hy)
    have hZ := F.label_two_range hx (hh z hz)
    by_cases e1 : F.label y = i+1 <;> by_cases e2 : F.label z = i+1
    · exact F.label_inj hx.1 A hA hy hz (e1.trans e2.symm)
    · have he' : F.label z = i := by simpa only [rho,if_pos e1,if_neg e2] using he.symm
      have ey := disj (i+1) (Or.inr rfl) (hh y hy) (e1 ▸ F.label_stamp y)
      have ez := disj i (Or.inl rfl) (hh z hz) (he' ▸ F.label_stamp z)
      exact (hI _ hy _ hz (ey.symm ▸ ez.symm ▸ ((F.adj _ _).mpr (Or.inr rfl)))).elim
    · have he' : F.label y = i := by simpa [rho,e1,e2] using he
      have ey := disj i (Or.inl rfl) (hh y hy) (he' ▸ F.label_stamp y)
      have ez := disj (i+1) (Or.inr rfl) (hh z hz) (e2 ▸ F.label_stamp z)
      exact (hI _ hy _ hz (ey.symm ▸ ez.symm ▸ ((F.adj _ _).mpr (Or.inl rfl)))).elim
    · exact F.label_inj hx.1 A hA hy hz (by simpa [rho,e1,e2] using he)
  exact (Finset.card_le_card_of_injOn rho hmap hInj).trans ((Finset.card_insert_le _ _).trans (by simp))

private lemma offset_seats : ∀ i : Fin 5,
    i+2 ≠ i ∧ i+3 ≠ i ∧ i+2 ≠ i+3 ∧ (i+3)+2=i ∧
      pent (i+2) (i+3) ∧ ¬pent i (i+2) ∧ ¬pent i (i+3) := by decide

/-- If an outside vertex with a single cycle contact has local independence
at least three, it sees single-contact vertices at both opposite sites. -/
theorem high_opposite {x : V} {i : Fin 5} (hx : One G F.c x i)
    (hd : 3 ≤ localIndependence G x) :
    ∃ y z, One G F.c y (i+2) ∧ One G F.c z (i+3) ∧ G.Adj x y ∧ G.Adj x z := by
  classical
  obtain ⟨A,hA,hc⟩ := maxLocalSet x
  obtain ⟨ha,hi⟩ := memLocalSet.mp hA
  let seats : Finset (Fin 5) := {i,i+2,i+3}
  have hs : seats.card = 3 := (by decide : ∀ i : Fin 5, ({i,i+2,i+3} : Finset (Fin 5)).card = 3) i
  have hsize : (A.image F.label).card = A.card := Finset.card_image_of_injOn (F.label_inj hx.1 A hA)
  have sub : A.image F.label ⊆ seats := by
    intro j hj
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
    simpa [seats] using F.label_one_range hx (ha y hy)
  have eq : A.image F.label = seats := Finset.eq_of_subset_of_card_le sub (by omega)
  obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp (show i+2 ∈ A.image F.label by simp [eq,seats])
  obtain ⟨z,hz,ez⟩ := Finset.mem_image.mp (show i+3 ∈ A.image F.label by simp [eq,seats])
  have yh : F.Stamp y (i+2) := ey ▸ F.label_stamp y
  have zh : F.Stamp z (i+3) := ez ▸ F.label_stamp z
  have yne : y ≠ z := fun e => (offset_seats i).2.2.1 (ey.symm.trans (e ▸ ez))
  have outY : Outside F.c y ∧ G.Adj y (F.c (i+2)) := by
    rcases yh with e | hy'
    · exact ((offset_seats i).1 ((hx.2 _).mp (e ▸ ha y hy))).elim
    · exact hy'
  have outZ : Outside F.c z ∧ G.Adj z (F.c (i+3)) := by
    rcases zh with e | hz'
    · exact ((offset_seats i).2.1 ((hx.2 _).mp (e ▸ ha z hz))).elim
    · exact hz'
  refine ⟨y,z,⟨outY.1,?_⟩,⟨outZ.1,?_⟩,ha y hy,ha z hz⟩
  · intro j
    refine ⟨?_,fun e => e.symm ▸ outY.2⟩
    intro h
    rcases F.outside_to_one hx outY.1 (ha y hy) h with ea | e | eb
    · exact (F.contact_sep2 outY.1 i (ea ▸ h) outY.2).elim
    · exact e
    · exact (yne (F.same_site_neighbors hx.1 (ha y hy) (ha z hz) (eb ▸ h) outZ.2)).elim
  · intro j
    refine ⟨?_,fun e => e.symm ▸ outZ.2⟩
    intro h
    rcases F.outside_to_one hx outZ.1 (ha z hz) h with ea | eb | e
    · exact (F.contact_sep2 outZ.1 (i+3) outZ.2 ((offset_seats i).2.2.2.1.symm ▸ (ea ▸ h))).elim
    · exact (yne (F.same_site_neighbors hx.1 (ha y hy) (ha z hz) outY.2 (eb ▸ h))).elim
    · exact e

private theorem single_disjoint {x : V} {i j : Fin 5}
    (hi : One G F.c x i) (hj : One G F.c x j) : i = j :=
  (hj.2 i).mp ((hi.2 i).mpr rfl)

private def arrangement {V : Type*} (a b c d e f : V) : Fin 6 → V := ![a,b,c,d,e,f]

private theorem has_P6_ms (a b c d e f : V)
    (nd : [a,b,c,d,e,f].Nodup)
    (hAB : G.Adj a b) (hBC : G.Adj b c) (hCD : G.Adj c d)
    (hDE : G.Adj d e) (hEF : G.Adj e f)
    (hAC : ¬G.Adj a c) (hAD : ¬G.Adj a d) (hAE : ¬G.Adj a e) (hAF : ¬G.Adj a f)
    (hBD : ¬G.Adj b d) (hBE : ¬G.Adj b e) (hBF : ¬G.Adj b f)
    (hCE : ¬G.Adj c e) (hCF : ¬G.Adj c f) (hDF : ¬G.Adj d f) :
    ∃ p : Fin 6 → V, InducedPath G p := by
  let p := arrangement a b c d e f
  refine ⟨p, ?_,?_⟩
  · apply List.nodup_ofFn.mp
    simpa [p,arrangement,List.ofFn_succ] using nd
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | contradiction | exact iff_of_true hAB rfl | exact iff_of_true hBC rfl |
      exact iff_of_true hCD rfl | exact iff_of_true hDE rfl | exact iff_of_true hEF rfl |
      exact iff_of_false hAC (by decide) | exact iff_of_false hAD (by decide) |
      exact iff_of_false hAE (by decide) | exact iff_of_false hAF (by decide) |
      exact iff_of_false hBD (by decide) | exact iff_of_false hBE (by decide) |
      exact iff_of_false hBF (by decide) | exact iff_of_false hCE (by decide) |
      exact iff_of_false hCF (by decide) | exact iff_of_false hDF (by decide)

private theorem opposite_seat_unique {x y z : V} {i j k : Fin 5}
    (hx : One G F.c x i) (hy : One G F.c y j) (hz : One G F.c z k)
    (e1 : G.Adj x y) (e2 : G.Adj x z)
    (nij : i ≠ j) (nik : i ≠ k) (njk : j ≠ k)
    (cij : ¬pent i j) (cik : ¬pent i k) (cjk : pent j k) :
    ∀ w, One G F.c w k → w = z := by
  intro w hw
  apply Classical.byContradiction
  intro hne
  have hAB := ((hx.2 i).mpr rfl).symm
  have hCD := (hy.2 j).mpr rfl
  have hDE := (F.adj j k).mpr cjk
  have hEF := ((hw.2 k).mpr rfl).symm
  have hAC : ¬G.Adj (F.c i) y := fun e => nij ((hy.2 i).mp e.symm)
  have hAD : ¬G.Adj (F.c i) (F.c j) := fun e => cij ((F.adj _ _).mp e)
  have hAE : ¬G.Adj (F.c i) (F.c k) := fun e => cik ((F.adj _ _).mp e)
  have hAF : ¬G.Adj (F.c i) w := fun e => nik ((hw.2 i).mp e.symm)
  have hBD : ¬G.Adj x (F.c j) := fun e => nij ((hx.2 j).mp e).symm
  have hBE : ¬G.Adj x (F.c k) := fun e => nik ((hx.2 k).mp e).symm
  have hBF : ¬G.Adj x w := fun e => hne (F.same_site_neighbors hx.1 e e2 ((hw.2 k).mpr rfl)
    ((hz.2 k).mpr rfl))
  have hCE : ¬G.Adj y (F.c k) := fun e => njk ((hy.2 k).mp e).symm
  have hCF : ¬G.Adj y w := fun e => F.forbidden_site hy.1 hw.1 e hCD hEF.symm cjk
  have hDF : ¬G.Adj (F.c j) w := fun e => njk ((hw.2 j).mp e.symm)
  have cw₁ : F.c i ≠ w := (hw.1 i).symm
  have cw₂ : F.c j ≠ w := (hw.1 j).symm
  have cw₃ : F.c k ≠ w := (hw.1 k).symm
  have common : x ≠ w := fun e => nik (F.single_disjoint hx (e.symm ▸ hw))
  have other : y ≠ w := fun e => njk (F.single_disjoint hy (e.symm ▸ hw))
  have nod : [F.c i,x,y,F.c j,F.c k,w].Nodup := by
    simp [hAB.ne,e1.ne,hCD.ne,hDE.ne,hEF.ne,cw₁,cw₂,cw₃,common,other,
      (hy.1 i).symm,(hx.1 j),(hx.1 k),(hy.1 k),
      show F.c i ≠ F.c j from fun e => nij (F.inj e),
      show F.c i ≠ F.c k from fun e => nik (F.inj e)]
  exact F.noP6 (has_P6_ms _ _ _ _ _ _ nod hAB e1 hCD hDE hEF hAC hAD hAE hAF
    hBD hBE hBF hCE hCF hDF)

/-- A high singleton forces its two opposite sites to be singleton fibers. -/
theorem high_unique_opposite {x : V} {i : Fin 5} (hx : One G F.c x i)
    (h : 3 ≤ localIndependence G x) :
    (∃ y, One G F.c y (i+2) ∧ G.Adj x y ∧ ∀ w, One G F.c w (i+2) → w = y) ∧
    (∃ z, One G F.c z (i+3) ∧ G.Adj x z ∧ ∀ w, One G F.c w (i+3) → w = z) := by
  obtain ⟨y,z,hy,hz,ey,ez⟩ := F.high_opposite hx h
  obtain ⟨ha,hb,hc,he,hf,hg,hh⟩ := offset_seats i
  exact ⟨⟨y,hy,ey,F.opposite_seat_unique hx hz hy ez ey hb.symm ha.symm hc.symm hh hg
      (or_comm.mp hf)⟩,
    ⟨z,hz,ez,F.opposite_seat_unique hx hy hz ey ez ha.symm hb.symm hc hg hh hf⟩⟩

end PentagonFrame
#print axioms make_frame
#print axioms PentagonFrame.local_one_le_three
#print axioms PentagonFrame.local_two_le_two
#print axioms PentagonFrame.high_unique_opposite
end Graffiti133Pentagon
