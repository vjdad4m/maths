import NoFiveHoles133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private def Front {n : ℕ} (H : Hole G n) (x : V) : Prop :=
  Outside H.c x → ∃ i, G.Adj x (H.c i)

/-- In the P7-free C4/C5-free class, an induced hexagon dominates. -/
theorem hex_dominates (H : Hole G 6) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : ∀ x, Front H x := by
  classical
  have step (u v : V) (e : G.Adj u v) (hu : Front H u) : Front H v := by
    intro hv
    by_cases uu : Outside H.c u
    · apply Classical.byContradiction
      intro none
      obtain ⟨p,hp,h0,htail⟩ := extend_hole_no_five (Or.inl rfl) H h4 h5 u uu (hu uu)
      change p (0 : Fin 6) = u at h0
      have hn : ∀ i, v ≠ p i := by
        intro i he
        by_cases hh : i.val = 0
        · have eq : i = 0 := Fin.ext hh
          rw [eq,h0] at he
          exact e.ne he.symm
        · obtain ⟨j,hj⟩ := htail i (Nat.pos_of_ne_zero hh)
          exact hv j (he.trans hj)
      have ha : G.Adj v (p 0) := h0.symm ▸ e.symm
      have hn' (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj v (p i) := by
        intro er
        obtain ⟨j,hj⟩ := htail i hi
        exact none ⟨j,hj ▸ er⟩
      obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp v hn ha hn'
      exact no7 ⟨q,hq⟩
    · have h : ∃ i, u = H.c i := by
        apply Classical.byContradiction
        intro bad
        exact uu (fun i eq => bad ⟨i,eq⟩)
      obtain ⟨i,hi⟩ := h
      exact ⟨i,hi ▸ e.symm⟩
  intro x
  obtain ⟨p⟩ := hc (H.c 0) x
  have walkprop {a b : V} (p : G.Walk a b) (ha : Front H a) : Front H b := by
    induction p with
    | nil => exact ha
    | cons e q ih => exact ih (step _ _ e ha)
  exact walkprop p (fun h => (h 0 rfl).elim)

/-- Under the same hypotheses, an induced heptagon fills the whole
connected graph. -/
theorem heptagon_spans (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : Function.Surjective H.c := by
  classical
  have next (u v : V) (e : G.Adj u v) (hu : ∃ i, H.c i = u) : ∃ i, H.c i = v := by
    obtain ⟨i,rfl⟩ := hu
    apply Classical.byContradiction
    intro bad
    obtain ⟨p,hp,_,_⟩ := extend_hole_no_five (Or.inr rfl) H h4 h5 v
      (fun j eq => bad ⟨j,eq.symm⟩) ⟨i,e.symm⟩
    exact no7 ⟨p,hp⟩
  intro x
  obtain ⟨p⟩ := hc (H.c 0) x
  have walkprop {a b : V} (p : G.Walk a b) (ha : ∃ i, H.c i = a) : ∃ i, H.c i = b := by
    induction p with
    | nil => exact ha
    | cons e q ih => exact ih (next _ _ e ha)
  exact walkprop p ⟨0,rfl⟩

private lemma cyc6_sites : ∀ i j : Fin 6, Cyclic i j ↔ j=i+1 ∨ j=i+5 := by decide
private lemma cyc7_sites : ∀ i j : Fin 7, Cyclic i j ↔ j=i+1 ∨ j=i+6 := by decide
private lemma cyc6_ne : ∀ i j : Fin 6, Cyclic i j → i≠j := by decide

private def One (H : Hole G 6) (x : V) (i : Fin 6) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ j = i
private def Two (H : Hole G 6) (x : V) (i : Fin 6) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ j = i ∨ j=i+1

private lemma classifyMask : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2)=false ∧ b (i+3)=false) → (∃ i,b i=true) →
    (∃ i, ∀ j, b j=true ↔ j=i) ∨ (∃ i, ∀ j, b j=true ↔ j=i ∨ j=i+1) := by decide

private theorem classify_hex (H : Hole G 6) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (dom : ∀ x, Front H x) (x : V) (hx : Outside H.c x) :
    (∃ i, One H x i) ∨ (∃ i, Two H x i) := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (H.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (H.c i) := by simp [b]
  have sep (i : Fin 6) (h : b i=true) : b (i+2)=false ∧ b (i+3)=false := by
    have hN := no_spoke_offset (Or.inl rfl) H h4 h5 x hx i ((bt i).mp h)
    constructor
    · cases eq : b (i+2)
      · rfl
      · exact (hN.1 ((bt _).mp eq)).elim
    · cases eq : b (i+3)
      · rfl
      · exact (hN.2 ((bt _).mp eq)).elim
  obtain ⟨i,hi⟩ := dom x hx
  rcases classifyMask b sep ⟨i,(bt i).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx,fun k => (bt k).symm.trans (hj k)⟩
  · exact Or.inr ⟨j,hx,fun k => (bt k).symm.trans (hj k)⟩

private def cycNear2 (i j : Fin 6) : Prop := j = i+2 ∨ i = j+2
private instance : DecidableRel cycNear2 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
private lemma mid6 : ∀ i j : Fin 6, cycNear2 i j →
    ∃ k, k≠i ∧ k≠j ∧ i≠j ∧ Cyclic i k ∧ Cyclic k j := by decide

private theorem forbidAdjacentSite (H : Hole G 6) (h4 : FourCycleFree G) {x y : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (e : G.Adj x y)
    {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    ¬Cyclic i j := by
  intro h
  exact hy i (h4 x (H.c j) y (H.c i) (hx j) e yj.symm xi ((H.adj _ _).mpr h).symm)

private theorem forbidNear2Site (H : Hole G 6) (h5 : NoSimpleFive133 G) {x y : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (e : G.Adj x y)
    {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    ¬cycNear2 i j := by
  intro h
  obtain ⟨k,ki,kj,ij,e1,e2⟩ := mid6 i j h
  have hN : [x,y,H.c j,H.c k,H.c i].Nodup := by
    simp [e.ne,hx j,hx k,hx i,hy j,hy k,hy i,H.inj.ne kj.symm,H.inj.ne ij.symm,H.inj.ne ki]
  exact h5 _ _ _ _ _ hN e yj ((H.adj _ _).mpr e2).symm ((H.adj _ _).mpr e1).symm xi.symm

private lemma remainingContact : ∀ i j : Fin 6, ¬Cyclic i j → ¬cycNear2 i j →
    j=i ∨ j=i+3 := by decide
private lemma impossibleDouble : ∀ i j : Fin 6,
    (j=i ∨ j=i+3) → (j=i+1 ∨ j=(i+1)+3) → False := by decide

private theorem seat_available (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {x y : V} (hx : Outside H.c x) (hy : Outside H.c y)
    (e : G.Adj x y) {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    j=i ∨ j=i+3 :=
  remainingContact i j (forbidAdjacentSite H h4 hx hy e xi yj)
    (forbidNear2Site H h5 hx hy e xi yj)

private def Stamp (H : Hole G 6) (y : V) (j : Fin 6) : Prop :=
  y = H.c j ∨ (Outside H.c y ∧ G.Adj y (H.c j))

private theorem stamp_exists (H : Hole G 6) (dom : ∀ x, Front H x) (y : V) :
    ∃ j, Stamp H y j := by
  by_cases h : Outside H.c y
  · obtain ⟨j,hj⟩ := dom y h
    exact ⟨j,Or.inr ⟨h,hj⟩⟩
  · apply Classical.byContradiction
    intro no
    exact h (fun j eq => no ⟨j,Or.inl eq⟩)

private theorem stamp_single (H : Hole G 6) (h4 : FourCycleFree G)
    {x y z : V} {j : Fin 6} (hne : x ≠ H.c j)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (sy : Stamp H y j) (sz : Stamp H z j) : y = z := by
  rcases sy with sy | ⟨hy,e1⟩ <;> rcases sz with sz | ⟨hz,e2⟩
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ e2.symm)).elim
  · exact (no (sz.symm ▸ e1)).elim
  · exact h4 x (H.c j) y z hne ey e1.symm ez e2.symm

private theorem local_single_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) {x : V} {i : Fin 6}
    (hx : One H x i) : localIndependence G x ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let f (w : V) := Classical.choose (stamp_exists H dom w)
  have spec (w : V) : Stamp H w (f w) := Classical.choose_spec (stamp_exists H dom w)
  let seats : Finset (Fin 6) := {i,i+3}
  have hf (w : V) (hw : w ∈ A) : f w ∈ seats := by
    rcases spec w with eq | ⟨hw',hW⟩
    · have : f w = i := (hx.2 _).mp (eq ▸ hN w hw)
      simp [seats,this]
    · have := seat_available H h4 h5 hx.1 hw' (hN w hw) ((hx.2 i).mpr rfl) hW
      simpa [seats] using this
  have inj : Set.InjOn f (↑A : Set V) := by
    intro a ha b hb he
    exact stamp_single H h4 (hx.1 (f a)) (hN _ ha) (hN _ hb) (hI _ ha _ hb)
      (spec a) (he.symm ▸ spec b)
  exact (Finset.card_le_card_of_injOn f hf inj).trans ((Finset.card_insert_le _ _).trans (by simp))

private theorem local_double_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) {x : V} {i : Fin 6}
    (hx : Two H x i) : localIndependence G x ≤ 1 := by
  classical
  have hh (y : V) (e : G.Adj x y) : y = H.c i ∨ y = H.c (i+1) := by
    by_cases out : Outside H.c y
    · obtain ⟨j,hj⟩ := dom y out
      have e1 := seat_available H h4 h5 hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj
      have e2 := seat_available H h4 h5 hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj
      exact (impossibleDouble i j e1 e2).elim
    · obtain ⟨j,hj⟩ : ∃ j, y = H.c j := by
        apply Classical.byContradiction
        intro no
        exact out fun j eq => no ⟨j,eq⟩
      rcases (hx.2 _).mp (hj ▸ e) with a | b
      · exact Or.inl (hj.trans (congrArg H.c a))
      · exact Or.inr (hj.trans (congrArg H.c b))
  have adj : G.Adj (H.c i) (H.c (i+1)) :=
    (H.adj _ _).mpr ((cyc6_sites _ _).mpr (Or.inl rfl))
  apply Finset.sup_le_iff.mpr
  intro A hA
  apply Finset.card_le_one.mpr
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  intro y hy z hz
  rcases hh y (hN _ hy) with e | e <;> rcases hh z (hN _ hz) with f | f
  · exact e.trans f.symm
  · exact (hI _ hy _ hz (e.symm ▸ f.symm ▸ adj)).elim
  · exact (hI _ hy _ hz (e.symm ▸ f.symm ▸ adj.symm)).elim
  · exact e.trans f.symm

private noncomputable def singleSite (H : Hole G 6) (i : Fin 6) : Finset V := by
  classical exact Finset.univ.filter (fun x => One H x i)

private lemma site_mem (H : Hole G 6) {i : Fin 6} {x : V} :
    x ∈ singleSite H i ↔ One H x i := by
  classical simp [singleSite]

private theorem local_cycle_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) (i : Fin 6) :
    localIndependence G (H.c i) ≤ 2 + (singleSite H i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A \ singleSite H i
  let seats : Finset (Fin 6) := {i+1,i+5}
  have label (w : V) (hw : w ∈ B) : ∃ j, Cyclic i j ∧ Stamp H w j := by
    have e := hN w (Finset.mem_sdiff.mp hw).1
    by_cases out : Outside H.c w
    · rcases classify_hex H h4 h5 dom w out with ⟨j,hj⟩ | ⟨j,hj⟩
      · have he := (hj.2 i).mp e.symm
        exact ((Finset.mem_sdiff.mp hw).2 ((site_mem H).mpr (he.symm ▸ hj))).elim
      · rcases (hj.2 i).mp e.symm with he | he
        · have m : Cyclic i (j+1) := (cyc6_sites _ _).mpr (Or.inl (by rw [he]))
          exact ⟨j+1,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inr rfl)⟩⟩
        · have m : Cyclic i j := (cyclic_symm _ _).mpr ((cyc6_sites _ _).mpr (Or.inl he))
          exact ⟨j,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inl rfl)⟩⟩
    · obtain ⟨j,hj⟩ : ∃ j, w = H.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j eq => no ⟨j,eq⟩)
      exact ⟨j,(H.adj _ _).mp (hj ▸ e),Or.inl hj⟩
  let f (w : V) := if hw : w ∈ B then Classical.choose (label w hw) else i
  have fs (w : V) (hw : w ∈ B) : Cyclic i (f w) ∧ Stamp H w (f w) := by
    simpa only [f,dif_pos hw] using Classical.choose_spec (label w hw)
  have hf (w : V) (hw : w ∈ B) : f w ∈ seats := by
    simpa [seats] using (cyc6_sites _ _).mp (fs w hw).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz e
    have hyA := (Finset.mem_sdiff.mp hy).1
    have hzA := (Finset.mem_sdiff.mp hz).1
    have ne : H.c i ≠ H.c (f y) := H.inj.ne (cyc6_ne _ _ (fs y hy).1)
    exact stamp_single H h4 ne (hN _ hyA) (hN _ hzA) (hI _ hyA _ hzA)
      (fs y hy).2 (e.symm ▸ (fs z hz).2)
  have cb : B.card ≤ 2 := (Finset.card_le_card_of_injOn f hf inj).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  have hInt := Finset.card_le_card (show A ∩ singleSite H i ⊆ singleSite H i from Finset.inter_subset_right)
  have hC : B.card + (A ∩ singleSite H i).card = A.card := Finset.card_sdiff_add_card_inter A _
  omega


private noncomputable def singles (H : Hole G 6) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, One H x i)

private lemma singles_iff (H : Hole G 6) (x : V) :
    x ∈ singles H ↔ ∃ i, One H x i := by classical simp [singles]

private noncomputable def core (H : Hole G 6) : Finset V := by
  classical
  exact (Finset.univ : Finset (Fin 6)).image H.c

private noncomputable def fSite (H : Hole G 6) (x : V) : Fin 6 := by
  classical exact if h : ∃ i, One H x i then Classical.choose h else 0

private theorem sum_sites (H : Hole G 6) : (∑ i, (singleSite H i).card) = (singles H).card := by
  classical
  have fiber (i : Fin 6) : singleSite H i = (singles H).filter (fun x => fSite H x = i) := by
    ext x
    rw [site_mem,Finset.mem_filter]
    have fvalid (h : x ∈ singles H) : One H x (fSite H x) := by
      have q := (singles_iff H x).mp h
      unfold fSite
      rw [dif_pos q]
      exact Classical.choose_spec q
    refine ⟨?_,fun ⟨h,he⟩ => he ▸ fvalid h⟩
    intro h
    have hS := (singles_iff H x).mpr ⟨i,h⟩
    exact ⟨hS,(h.2 _).mp (((fvalid hS).2 _).mpr rfl)⟩
  simpa only [fiber] using
    (Finset.card_eq_sum_card_fiberwise (s:=singles H) (t:=Finset.univ)
      (f:=fSite H) (fun _ _ => Finset.mem_univ _)).symm

private noncomputable def charge (H : Hole G 6) (x : V) : ℕ := by
  classical exact ∑ i : Fin 6, if x = H.c i then (singleSite H i).card else 0

private noncomputable def fee (H : Hole G 6) (x : V) : ℕ := by
  classical exact if x ∈ core H ∪ singles H then 1 else 0

/-- A dominating induced hexagon imposes a strict density bound in the
ordinary-C4/C5-free class: sum of local independence plus six is at
most three times the order. -/
theorem hex_budget (H : Hole G 6) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (dom : ∀ x, Front H x) :
    (∑ x, localIndependence G x) + 6 ≤ 3 * Fintype.card V := by
  classical
  have pointwise (x : V) : localIndependence G x + fee H x ≤ 3 + charge H x := by
    by_cases out : Outside H.c x
    · have b : fee H x ≤ 1 := by
        unfold fee
        split <;> omega
      rcases classify_hex H h4 h5 dom x out with ⟨i,h⟩ | ⟨i,h⟩
      · have l := local_single_bound H h4 h5 dom h
        omega
      · have l := local_double_bound H h4 h5 dom h
        omega
    · obtain ⟨i,e⟩ : ∃ i, x = H.c i := by
        apply Classical.byContradiction
        intro no
        exact out fun j e => no ⟨j,e⟩
      have hL := local_cycle_bound H h4 h5 dom i
      rw [← e] at hL
      have hl : (singleSite H i).card ≤ charge H x := by
        have hh := Finset.single_le_sum (f := fun j : Fin 6 =>
          if x = H.c j then (singleSite H j).card else 0) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        simpa [charge,e] using hh
      have b : fee H x ≤ 1 := by
        unfold fee
        split <;> omega
      omega
  have disj : Disjoint (core H) (singles H) := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,_,e⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi⟩ := (singles_iff H x).mp hs
    exact hi.1 a e.symm
  have hc : (core H).card = 6 := by
    unfold core
    rw [Finset.card_image_of_injective _ H.inj]
    simp
  have hfee : (∑ x, fee H x) = 6+(singles H).card := by
    have hF : (Finset.univ : Finset V).filter (fun x => x ∈ core H ∪ singles H) = core H ∪ singles H := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [fee,Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,
      Nat.cast_id,mul_one,mul_zero,add_zero,hF,Finset.card_union_of_disjoint disj,hc]
  have hcharge : (∑ x, charge H x) = (singles H).card := by
    unfold charge
    rw [Finset.sum_comm]
    simp [sum_sites H]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => pointwise x)
  have hu : (∑ x, localIndependence G x) + (6+(singles H).card) ≤
      3*Fintype.card V + (singles H).card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hfee,hcharge,
      Nat.mul_comm] using h
  omega

theorem heptagon_budget (H : Hole G 7) (sur : Function.Surjective H.c) :
    (∑ x, localIndependence G x) ≤ 2 * Fintype.card V := by
  classical
  have atmost (x : V) : localIndependence G x ≤ 2 := by
    obtain ⟨i,rfl⟩ := sur x
    apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
    have hsub : A ⊆ ({H.c (i+1),H.c (i+6)} : Finset V) := by
      intro y hy
      obtain ⟨j,rfl⟩ := sur y
      have hh := (cyc7_sites i j).mp ((H.adj _ _).mp (hN _ hy))
      rcases hh with rfl | rfl <;> simp
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => atmost x)
  simpa [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_comm] using h

#print axioms hex_dominates
#print axioms heptagon_spans
#print axioms hex_budget
#print axioms heptagon_budget

end Graffiti133NoFive
