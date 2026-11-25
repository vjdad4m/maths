import Std
set_option warningAsError true
namespace Graffiti426
abbrev Set (V : Type) := V → Prop
abbrev Graph (V : Type) := V → V → Prop

def Neighborhood {V} (G : Graph V) (M : Set V) : Set V :=
  fun v => ∃ m, M m ∧ G v m

def Independent {V} (G : Graph V) (I : Set V) : Prop :=
  ∀ v w, I v → I w → ¬ G v w

def Dominates {V} (G : Graph V) (U I : Set V) : Prop :=
  ∀ v, U v → I v ∨ ∃ w, I w ∧ G v w

noncomputable def card {n} (U : Set (Fin n)) : Nat := by
  classical
  exact ((List.ofFn id : List (Fin n)).filter fun v => decide (U v)).length

theorem cover_extend {V} (G : Graph V)
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (xs : List V) (S : Set V) (hS : Independent G S) :
    ∃ I : Set V, Independent G I ∧ (∀ v, S v → I v)
      ∧ Dominates G (fun v => v ∈ xs) I := by
  classical
  induction xs generalizing S with
  | nil =>
    exact ⟨S, hS, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons a xs ih =>
    by_cases hh : S a ∨ ∃ w, S w ∧ G a w
    · obtain ⟨I, hI, hSI, hDom⟩ := ih S hS
      refine ⟨I, hI, hSI, ?_⟩
      intro v h
      rcases List.mem_cons.mp h with h | h
      · subst v
        rcases hh with ha | ⟨w, hw, haw⟩
        · exact Or.inl (hSI _ ha)
        · exact Or.inr ⟨w, hSI _ hw, haw⟩
      · exact hDom _ h
    · let S' : Set V := fun v => S v ∨ v = a
      have hS' : Independent G S' := by
        intro v w hv hw h
        rcases hv with hv | rfl <;> rcases hw with hw | rfl
        · exact hS _ _ hv hw h
        · exact hh (Or.inr ⟨v, hv, symm h⟩)
        · exact hh (Or.inr ⟨w, hw, h⟩)
        · exact loopless _ h
      obtain ⟨I, hI, hSI, hDom⟩ := ih S' hS'
      refine ⟨I, hI, (fun v hv => hSI v (Or.inl hv)), ?_⟩
      intro v h
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl (hSI _ (Or.inr h))
      · exact hDom _ h

private theorem filter_split {V} (U I : Set V) (xs : List V) : by
    classical
    exact (xs.filter (fun v => decide (I v))).length +
      (xs.filter (fun v => decide (U v ∧ ¬ I v))).length ≤ xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons a l ih =>
    by_cases hi : I a <;> by_cases hu : U a <;>
      simp [List.filter_cons, hi, hu] at * <;> omega

theorem card_split {n} (U I : Set (Fin n)) :
    card I + card (fun v => U v ∧ ¬ I v) ≤ n := by
  classical
  have h := filter_split U I (List.ofFn id)
  simpa [card] using h

/-- Construct simultaneous independent and ordinary dominating sets with the
required sum of cardinalities. This works for arbitrary M. -/
theorem simultaneous {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (M : Set (Fin n)) :
    ∃ I D : Set (Fin n), Independent G I ∧ Dominates G (fun _ => True) I ∧
      (∀ v, D v → Neighborhood G M v) ∧ Dominates G (Neighborhood G M) D ∧
      card I + card D ≤ n := by
  classical
  let U := Neighborhood G M
  let W : Set (Fin n) := fun v => M v ∧ ¬ U v
  have hW : Independent G W := by
    intro v w hv hw hj
    exact hv.2 ⟨w, hw.1, hj⟩
  obtain ⟨I, hi, hwi, hdi⟩ := cover_extend G @symm loopless (List.ofFn id) W hW
  let D : Set (Fin n) := fun v => U v ∧ ¬ I v
  refine ⟨I, D, hi, (fun v _ => hdi v (List.mem_ofFn.mpr ⟨v,rfl⟩)), (fun _ h => h.1), ?_, card_split U I⟩
  intro v hv
  by_cases iv : I v
  · have hn : ∃ w, U w ∧ G v w := by
      apply Classical.byContradiction
      intro hn
      obtain ⟨m, hm, hvₘ⟩ := hv
      have hwm : W m := ⟨hm, fun hum => hn ⟨m, hum, hvₘ⟩⟩
      exact hi v m iv (hwi _ hwm) (hvₘ)
    obtain ⟨w, hw, hvw⟩ := hn
    exact Or.inr ⟨w, ⟨hw, fun h => hi _ _ iv h hvw⟩, hvw⟩
  · exact Or.inl ⟨hv, iv⟩
end Graffiti426
namespace Graffiti426

theorem min_exists (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases he : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hp⟩ := he
      exact ih j hj hp
    · refine ⟨k, hk, ?_⟩
      intro j hj
      by_cases hlt : j < k
      · exact False.elim (he ⟨j,hlt,hj⟩)
      · omega

def independentDomCard {n} (G : Graph (Fin n)) (k : Nat) : Prop :=
  ∃ I, Independent G I ∧ Dominates G (fun _ => True) I ∧ card I = k

def inducedDomCard {n} (G : Graph (Fin n)) (U : Set (Fin n)) (k : Nat) : Prop :=
  ∃ D, (∀ v, D v → U v) ∧ Dominates G U D ∧ card D = k

theorem indep_exists {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x) :
    ∃ k, independentDomCard G k := by
  obtain ⟨I, _, hi, hd, _, _, _⟩ := simultaneous G @symm loopless (fun _ => False)
  exact ⟨card I, I, hi, hd, rfl⟩

theorem dom_exists {n} (G : Graph (Fin n)) (U : Set (Fin n)) :
    ∃ k, inducedDomCard G U k :=
  ⟨card U, U, (fun _ h => h), (fun _ h => Or.inl h), rfl⟩

noncomputable def independentDomination {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x) : Nat :=
  Classical.choose (min_exists _ (indep_exists G @symm loopless))

noncomputable def inducedDomination {n} (G : Graph (Fin n)) (U : Set (Fin n)) : Nat :=
  Classical.choose (min_exists _ (dom_exists G U))

/-- Exact conjecture in the stronger version allowing arbitrary M and no
connectivity or order lower bound. -/
theorem conjecture426 {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (M : Set (Fin n)) :
    independentDomination G @symm loopless ≤ n - inducedDomination G (Neighborhood G M) := by
  obtain ⟨I, D, hI, hdI, hD, hdD, hcard⟩ := simultaneous G @symm loopless M
  have h1 : independentDomination G @symm loopless ≤ card I :=
    (Classical.choose_spec (min_exists _ (indep_exists G @symm loopless))).2 _
      ⟨I,hI,hdI,rfl⟩
  have h2 : inducedDomination G (Neighborhood G M) ≤ card D :=
    (Classical.choose_spec (min_exists _ (dom_exists G (Neighborhood G M)))).2 _
      ⟨D,hD,hdD,rfl⟩
  omega

#print axioms conjecture426
end Graffiti426

set_option warningAsError true
namespace Graffiti416
open Graffiti426

theorem card_congr {n} {U W : Set (Fin n)} (h : ∀ v, U v ↔ W v) : card U = card W := by
  have he : U = W := funext fun v => propext (h v)
  rw [he]

private theorem filt_mono {V} (U W : Set V) (h : ∀ v, U v → W v) (xs : List V) : by
    classical
    exact (xs.filter (fun v => decide (U v))).length ≤ (xs.filter (fun v => decide (W v))).length := by
  classical
  induction xs with
  | nil => simp
  | cons a as ih =>
    by_cases ha : U a
    · have hb := h a ha
      simp [List.filter_cons, ha, hb, ih]
    · by_cases hb : W a <;> simp [List.filter_cons, ha, hb] <;> omega

theorem card_mono {n} {U W : Set (Fin n)} (h : ∀ v, U v → W v) : card U ≤ card W := by
  classical
  exact filt_mono U W h (List.ofFn id)

theorem card_le {n} (U : Set (Fin n)) : card U ≤ n := by
  classical
  unfold card
  have h := List.length_filter_le (fun v : Fin n => decide (U v)) (List.ofFn id)
  simpa using h

private theorem filt_union {V} (U W : Set V) (h : ∀ v, U v → ¬ W v) (xs : List V) : by
    classical
    exact (xs.filter (fun v => decide (U v ∨ W v))).length =
      (xs.filter (fun v => decide (U v))).length + (xs.filter (fun v => decide (W v))).length := by
  classical
  induction xs with
  | nil => simp
  | cons a as ih =>
    by_cases ha : U a
    · have hb := h a ha
      simp [List.filter_cons, ha, hb] at ih ⊢
      omega
    · by_cases hb : W a <;> simp [List.filter_cons, ha, hb] at ih ⊢ <;> omega

theorem card_union {n} (U W : Set (Fin n)) (h : ∀ v, U v → ¬ W v) :
    card (fun v => U v ∨ W v) = card U + card W := by
  classical
  simpa [card] using filt_union U W h (List.ofFn id)

theorem card_true (n : Nat) : card (fun _ : Fin n => True) = n := by
  unfold card
  rw [List.filter_eq_self.mpr (by simp)]
  simp

theorem card_empty (n : Nat) : card (fun _ : Fin n => False) = 0 := by
  simp [card]

theorem card_compl {n} (U : Set (Fin n)) : card U + card (fun v => ¬ U v) = n := by
  rw [← card_union U _ (fun _ h hh => hh h)]
  rw [card_congr (W := fun _ => True) (fun v => iff_true_intro (Classical.em (U v))), card_true]

private theorem filt_single {n} (a : Fin n) :
    ((List.finRange n).filter (fun v => decide (v = a))).length = 1 := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    refine Fin.cases ?_ (fun b => ?_) a
    · rw [List.finRange_succ]
      have hx : ((List.finRange n).map Fin.succ).filter (fun v => decide (v = 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x h
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        simpa using Fin.succ_ne_zero i
      simp [hx]
    · rw [List.finRange_succ, List.filter_cons]
      have hz : (0 : Fin (n+1)) ≠ b.succ := Ne.symm (Fin.succ_ne_zero b)
      have he : ((fun v : Fin (n+1) => decide (v=b.succ)) ∘ Fin.succ) =
          (fun v : Fin n => decide (v=b)) := by funext v; simp
      simpa [hz, List.filter_map, he] using ih b

theorem card_single {n} (a : Fin n) : card (fun v => v = a) = 1 := by
  unfold card
  rw [List.filter_congr (q := fun v => @decide (v=a) (instDecidableEqFin _ _ _))
      (fun _ _ => by simp)]
  exact filt_single a

theorem card_add {n} (I : Set (Fin n)) (p : Fin n) (hp : ¬ I p) :
    card (fun v => I v ∨ v = p) = card I + 1 := by
  rw [card_union I (fun v => v = p) (fun v h hv => hp (hv ▸ h)), card_single]

def Pendant {n} (G : Graph (Fin n)) (p : Fin n) : Prop :=
  ∃ u, G p u ∧ ∀ w, G p w → w = u

def DiameterAtMostTwo {n} (G : Graph (Fin n)) : Prop :=
  ∀ a b, a = b ∨ G a b ∨ ∃ c, G a c ∧ G c b

def Isolates {n} (G : Graph (Fin n)) (U : Set (Fin n)) : Set (Fin n) :=
  fun v => U v ∧ ∀ w, U w → ¬ G v w

def IsoTwoStep {n} (G : Graph (Fin n)) : Set (Fin n) :=
  Isolates G (Neighborhood G (Neighborhood G (Pendant G)))

/-- Adding n avoids signed integers but does not change the optimization order. -/
noncomputable def score {n} (G : Graph (Fin n)) (I : Set (Fin n)) : Nat :=
  card I + n - card (Neighborhood G I)

theorem score_order_exact {n} (G : Graph (Fin n)) (I J : Set (Fin n)) :
    score G I ≤ score G J ↔
      (card I : Int) - (card (Neighborhood G I) : Int) ≤
      (card J : Int) - (card (Neighborhood G J) : Int) := by
  have hI := card_le (Neighborhood G I)
  have hJ := card_le (Neighborhood G J)
  unfold score
  omega

def Critical {n} (G : Graph (Fin n)) (I : Set (Fin n)) : Prop :=
  Independent G I ∧ ∀ J, Independent G J → score G J ≤ score G I

def MaximumCritical {n} (G : Graph (Fin n)) (I : Set (Fin n)) : Prop :=
  Critical G I ∧ ∀ J, Critical G J → card J ≤ card I

def CriticalUnion {n} (G : Graph (Fin n)) : Set (Fin n) :=
  fun p => ∃ I, MaximumCritical G I ∧ I p

theorem max_exists (P : Nat → Prop) (B : Nat) (h : ∃ k, P k) (hb : ∀ k, P k → k ≤ B) :
    ∃ k, P k ∧ ∀ j, P j → j ≤ k := by
  obtain ⟨m, ⟨k,hk,hm⟩, hmin⟩ :=
    Graffiti426.min_exists (fun z => ∃ k, P k ∧ B-k=z)
      (by obtain ⟨k,hk⟩ := h; exact ⟨B-k, k, hk, rfl⟩)
  exact ⟨k, hk, fun j hj => by
    have h := hmin (B-j) ⟨j,hj,rfl⟩
    have hjb := hb j hj
    have hkb := hb k hk
    omega⟩

theorem critical_exists {n} (G : Graph (Fin n)) : ∃ I, Critical G I := by
  have h₀ : Independent G (fun _ => False) := fun _ _ hx => False.elim hx
  obtain ⟨s, ⟨I,hI,hs⟩, hmax⟩ :=
    max_exists (fun s => ∃ I, Independent G I ∧ score G I = s) (n+n)
    ⟨_, _, h₀, rfl⟩ (fun s ⟨I,_,hs⟩ => by
      have h := card_le I
      simp only [score] at hs
      omega)
  exact ⟨I, hI, fun J hJ => hs ▸ hmax (score G J) ⟨J,hJ,rfl⟩⟩

theorem maxcritical_exists {n} (G : Graph (Fin n)) : ∃ I, MaximumCritical G I := by
  obtain ⟨I₀,hI₀⟩ := critical_exists G
  obtain ⟨s, ⟨I,hI,hs⟩, hmax⟩ :=
    max_exists (fun s => ∃ I, Critical G I ∧ card I = s) n
    ⟨_, I₀, hI₀, rfl⟩ (fun s ⟨I,_,hs⟩ => hs ▸ card_le I)
  exact ⟨I, hI, fun J hJ => hs ▸ hmax (card J) ⟨J,hJ,rfl⟩⟩
end Graffiti416
namespace Graffiti416
open Graffiti426

theorem cover_unique {n} {G : Graph (Fin n)}
    (symm : ∀ {x y}, G x y → G y x)
    (hd : DiameterAtMostTwo G) {p u : Fin n}
    (hp : G p u) (hu : ∀ w, G p w → w = u) :
    ∀ a, a ≠ u → G a u := by
  intro a ha
  rcases hd p a with rfl | h | ⟨w, hpw, hwa⟩
  · exact hp
  · exact False.elim (ha (hu _ h))
  · have hw := hu _ hpw
    subst w
    exact symm hwa

theorem two_others {n} (hn : 2 < n) (u p : Fin n) (hup : u ≠ p) :
    ∃ a, a ≠ u ∧ a ≠ p := by
  classical
  by_cases h : ∃ a, a ≠ u ∧ a ≠ p
  · exact h
  · have ht : ∀ a : Fin n, a = u ∨ a = p := by
      intro a
      by_cases hu : a = u
      · exact Or.inl hu
      · by_cases hp : a = p
        · exact Or.inr hp
        · exact False.elim (h ⟨a,hu,hp⟩)
    have h₁ : card (fun a => a = u ∨ a = p) = 2 := by
      rw [card_add (fun a => a = u) p (Ne.symm hup), card_single]
    have h₂ : card (fun a => a = u ∨ a = p) = n := by
      rw [card_congr (W := fun _ => True) (fun a => iff_true_intro (ht a)), card_true]
    omega

theorem card_union_one_le {n} (S : Set (Fin n)) (a : Fin n) :
    card (fun v => S v ∨ v = a) ≤ card S + 1 := by
  classical
  by_cases ha : S a
  · have h : card (fun v => S v ∨ v = a) = card S := by
      apply card_congr
      intro v
      constructor
      · intro h
        rcases h with h | rfl
        · exact h
        · exact ha
      · exact Or.inl
    omega
  · exact Nat.le_of_eq (card_add _ _ ha)

theorem critical_avoids_universal {n} {G : Graph (Fin n)}
    (hn : 2 < n)
    (loopless : ∀ x, ¬ G x x) {u : Fin n} (hall : ∀ a, a ≠ u → G a u)
    {I : Set (Fin n)} (hI : Critical G I) : ¬ I u := by
  intro hu
  have hi : ∀ a, I a ↔ a = u := by
    intro a
    constructor
    · intro ha
      by_cases hau : a = u
      · exact hau
      · exact False.elim (hI.1 _ _ ha hu (hall _ hau))
    · intro h
      simpa [h] using hu
  have hcard := card_congr hi
  rw [card_single] at hcard
  have hneigh : ∀ a, Neighborhood G I a ↔ a ≠ u := by
    intro a
    constructor
    · rintro ⟨v,hv,ha⟩ rfl
      have hv' := (hi v).mp hv
      subst v
      exact loopless _ ha
    · intro h
      exact ⟨u,hu,hall _ h⟩
  have hnc := card_congr hneigh
  have hn' := card_compl (fun a => a = u)
  rw [card_single] at hn'
  have hfinal : 1 + card (Neighborhood G I) = n := by
    rw [hnc]
    exact hn'
  have he : score G (fun _ => False) = n := by
    unfold score
    have hne : card (Neighborhood G (fun _ => False)) = 0 := by
      rw [card_congr (W := fun _ => False)]
      · exact card_empty n
      · intro a; constructor
        · rintro ⟨_,h,_⟩; exact h
        · exact False.elim
    rw [hne, card_empty]; omega
  have hopt : n ≤ score G I := by
    simpa only [he] using hI.2 (fun _ => False) (fun _ _ h => False.elim h)
  unfold score at hopt
  omega

theorem strengthened416 {n} (G : Graph (Fin n)) (hn : 2 < n)
    (symm : ∀ {x y}, G x y → G y x)
    (loopless : ∀ x, ¬ G x x) (hd : DiameterAtMostTwo G) :
    card (IsoTwoStep G) ≤ card (CriticalUnion G) := by
  classical
  by_cases hP : ∃ p, Pendant G p
  · obtain ⟨p,u,hpu,huniq⟩ := hP
    have hall := cover_unique (G := G) @symm hd hpu huniq
    have hpu' : p ≠ u := fun h => loopless u (h ▸ hpu)
    obtain ⟨v,hvu,hvp⟩ := two_others hn u p (Ne.symm hpu')
    have hnu : ¬ Pendant G u := by
      rintro ⟨w,_,hw⟩
      have hpw := hw p (symm hpu)
      have hvw := hw v (symm (hall v hvu))
      exact hvp (hvw.trans hpw.symm)
    have hnp : ∀ a, Neighborhood G (Pendant G) a ↔ a = u := by
      intro a
      constructor
      · rintro ⟨q,hq,haq⟩
        have hqu : q ≠ u := fun h => hnu (h ▸ hq)
        obtain ⟨w,_,hw⟩ := hq
        exact (hw a (symm haq)).trans (hw u (hall q hqu)).symm
      · intro h
        subst a
        exact ⟨p, ⟨u,hpu,huniq⟩, symm hpu⟩
    have hnn : ∀ a, Neighborhood G (Neighborhood G (Pendant G)) a ↔ a ≠ u := by
      intro a
      constructor
      · rintro ⟨q,hq,haq⟩ h
        have hq' := (hnp q).mp hq
        subst q
        exact loopless u (h ▸ haq)
      · intro h
        exact ⟨u,(hnp u).mpr rfl,hall _ h⟩
    have hiso : ∀ a, IsoTwoStep G a ↔ Pendant G a := by
      intro a
      constructor
      · rintro ⟨ha,hi⟩
        have hau := (hnn a).mp ha
        refine ⟨u,hall _ hau,fun w hw => ?_⟩
        by_cases hwu : w=u
        · exact hwu
        · exact False.elim (hi _ ((hnn w).mpr hwu) hw)
      · intro hp
        have hau : a ≠ u := fun h => hnu (h ▸ hp)
        refine ⟨(hnn a).mpr hau,fun w hw haw => ?_⟩
        obtain ⟨q,_,hq⟩ := hp
        have : w = u := (hq w haw).trans (hq u (hall _ hau)).symm
        exact (hnn w).mp hw this
    obtain ⟨I,hI⟩ := maxcritical_exists G
    have hno : ¬ I u := critical_avoids_universal hn loopless hall hI.1
    have hcontain : ∀ p', Pendant G p' → I p' := by
      intro p' hp'
      by_cases hi : I p'
      · exact hi
      · exfalso
        have hpu'' : p' ≠ u := fun h => hnu (h ▸ hp')
        obtain ⟨q,_,hq⟩ := hp'
        have hsole : ∀ w, G p' w → w=u :=
          fun w hw => (hq w hw).trans (hq u (hall p' hpu'')).symm
        let J : Set (Fin n) := fun v => I v ∨ v=p'
        have hJ : Independent G J := by
          intro v w hv hw ha
          rcases hv with hv | rfl <;> rcases hw with hw | rfl
          · exact hI.1.1 _ _ hv hw ha
          · exact hno ((hsole _ (symm ha)) ▸ hv)
          · exact hno ((hsole _ ha) ▸ hw)
          · exact loopless _ ha
        have hnc : card (Neighborhood G J) ≤ card (Neighborhood G I) + 1 := by
          apply Nat.le_trans (card_mono (W := fun v => Neighborhood G I v ∨ v=u) ?_)
            (card_union_one_le _ _)
          rintro v ⟨w,hw,hvw⟩
          rcases hw with hw | rfl
          · exact Or.inl ⟨w,hw,hvw⟩
          · exact Or.inr (hsole _ (symm hvw))
        have hc : card J = card I + 1 := card_add _ _ hi
        have hs : score G I ≤ score G J := by
          simp only [score]
          omega
        have hcrit : Critical G J := ⟨hJ, fun X hX => Nat.le_trans (hI.1.2 X hX) hs⟩
        have : card J ≤ card I := hI.2 J hcrit
        omega
    have hcard : card (IsoTwoStep G) ≤ card (CriticalUnion G) :=
      card_mono (fun a ha => ⟨I,hI,hcontain a ((hiso a).mp ha)⟩)
    omega
  · have hh : card (IsoTwoStep G) = 0 := by
      rw [card_congr (W := fun _ => False)]
      · exact card_empty n
      · intro a
        constructor
        · rintro ⟨⟨v,⟨p,hp,_⟩,_⟩,_⟩
          exact hP ⟨p,hp⟩
        · exact False.elim
    omega

theorem conjecture416 {n} (G : Graph (Fin n)) (hn : 2 < n)
    (symm : ∀ {x y}, G x y → G y x)
    (loopless : ∀ x, ¬ G x x) (hd : DiameterAtMostTwo G) :
    card (IsoTwoStep G) - 2 ≤ card (CriticalUnion G) := by
  have h := strengthened416 G hn @symm loopless hd
  omega

#print axioms score_order_exact
#print axioms conjecture416
#print axioms strengthened416
end Graffiti416
