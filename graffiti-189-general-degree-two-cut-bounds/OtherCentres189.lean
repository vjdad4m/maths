import SixCentreGraph189
import SixCentreCount189

namespace Graffiti189Adam
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {a b : V}
variable (S : Separator G a b)

/-- Original ports and their parity-equivalent replacements. -/
def EffectiveA (G : SimpleGraph V) (a b c : V) : Prop :=
  G.dist c a % 2 = 1 ∧ 1 ≤ G.dist c b - G.dist c a ∧
    G.dist c b - G.dist c a ≤ 3

noncomputable def effectiveOpp (G : SimpleGraph V) (a b c : V) : ℕ :=
  G.dist c b - G.dist c a + 1

theorem effective_a_coverage {i j : Bool} (hij : i ≠ j) {c x : V}
    (hc : c ∈ S.sides i) (hx : x ∈ S.sides j) (h : EffectiveA G a b c) :
    ev G c x = Graffiti189SixCentre.evenBit (min (G.dist x a + 1)
      (G.dist x b + effectiveOpp G a b c)) := by
  have e := cross_distance S hij hc hx
  rw [dist_comm (G:=G) (u:=a) (v:=x), dist_comm (G:=G) (u:=b) (v:=x)] at e
  obtain ⟨ho,hl,hu⟩ := h
  let k := G.dist c a - 1
  have hK : k % 2 = 0 := by dsimp [k]; omega
  have he₁ : G.dist c a + G.dist x a = k + (G.dist x a + 1) := by dsimp [k]; omega
  have he₂ : G.dist c b + G.dist x b = k + (G.dist x b + effectiveOpp G a b c) := by
    dsimp [k,effectiveOpp]
    omega
  rw [he₁,he₂,Nat.add_min_add_left] at e
  unfold ev Graffiti189SixCentre.evenBit
  rw [e]
  have hM (m : ℕ) : (k+m)%2 = m%2 := by omega
  rw [hM]

private def swapOther (S : Separator G a b) : Separator G b a where
  conn := S.conn
  sides := S.sides
  disj := S.disj
  not_a := S.not_b
  not_b := S.not_a
  covers x := by rcases S.covers x with h|h|h|h <;> tauto
  closed i x hx y h := by have := S.closed i x hx y h; tauto

theorem effective_b_coverage {i j : Bool} (hij : i ≠ j) {c x : V}
    (hc : c ∈ S.sides i) (hx : x ∈ S.sides j) (h : EffectiveA G b a c) :
    ev G c x = Graffiti189SixCentre.evenBit (min (G.dist x a + effectiveOpp G b a c)
       (G.dist x b + 1)) := by
  rw [min_comm]
  exact effective_a_coverage (swapOther S) hij hc hx h

private theorem effective_a_extra_long {i : Bool} {c : V}
    (hc : c ∈ S.sides i) (h : EffectiveA G a b c) (hLong : 3 ≤ G.dist c a) :
    ∃ t, t ≠ c ∧ t ∈ S.sides i ∧ G.dist c t = 2 := by
  obtain ⟨w,hw⟩ := S.conn.exists_walk_length_eq_dist c a
  obtain ⟨ho,hl,hu⟩ := h
  cases w with
  | nil => simp at hw; omega
  | @cons _ u _ h₁ w =>
    cases w with
    | nil => simp at hw; omega
    | @cons _ t _ h₂ w =>
      have hCt : G.dist c t ≤ 2 := G.dist_le (.cons h₁ (.cons h₂ .nil))
      have hCu : G.dist c u = 1 := dist_eq_one_iff_adj.2 h₁
      have hTa := G.dist_le w
      have hTriangle := S.conn.dist_triangle (u:=c) (v:=t) (w:=a)
      simp only [length_cons] at hw
      have hExact : G.dist c t = 2 := by omega
      have huA : u ≠ a := by intro he; subst u; omega
      have huB : u ≠ b := by intro he; subst u; omega
      have htA : t ≠ a := by intro he; subst t; omega
      have htB : t ≠ b := by intro he; subst t; omega
      have huS := ((S.closed i c hc u h₁).resolve_left huA).resolve_left huB
      have htS := ((S.closed i u huS t h₂).resolve_left htA).resolve_left htB
      refine ⟨t,?_,htS,hExact⟩
      intro he; subst t
      simp [SimpleGraph.dist_self] at hExact

private theorem effective_a_extra_short {i : Bool} {c : V}
    (hc : c ∈ S.sides i) (hab : G.dist a b = 3)
    (h : EffectiveA G a b c) (hs : G.dist c a = 1) :
    ∃ t, t ≠ c ∧ (t = b ∨ t ∈ S.sides i) ∧ ev G c t = 1 := by
  obtain ⟨ho,hl,hu⟩ := h
  have hh : G.dist c b = 2 ∨ G.dist c b = 3 ∨ G.dist c b = 4 := by omega
  rcases hh with h|h|h
  · exact ⟨b,fun he => S.not_b i (he.symm ▸ hc),Or.inl rfl,by simp [ev,h]⟩
  · obtain ⟨w,hw⟩ := S.conn.exists_walk_length_eq_dist c b
    have hw' : w.length = 3 := hw.trans h
    cases w with
    | nil => simp at hw'
    | @cons _ u _ h₁ w =>
      cases w with
      | nil => simp at hw'
      | @cons _ t _ h₂ w =>
        cases w with
        | nil => simp at hw'
        | @cons _ z _ h₃ w =>
          cases w with
          | @cons => simp at hw'
          | nil =>
            have hut : G.dist u b ≤ 2 := G.dist_le (.cons h₂ (.cons h₃ .nil))
            have htb : G.dist t b = 1 := dist_eq_one_iff_adj.2 h₃
            have huu : u ≠ a := by intro he; subst u; omega
            have hub : u ≠ b := by
              intro he; subst u
              have := dist_eq_one_iff_adj.2 h₁
              omega
            have hta : t ≠ a := by intro he; subst t; omega
            have htb' : t ≠ b := h₃.ne
            have hus : u ∈ S.sides i := ((S.closed i c hc u h₁).resolve_left huu).resolve_left hub
            have hts : t ∈ S.sides i := ((S.closed i u hus t h₂).resolve_left hta).resolve_left htb'
            have hYt : G.dist c t = 2 := by
              have hUpper : G.dist c t ≤ 2 := G.dist_le (.cons h₁ (.cons h₂ .nil))
              have hLower := S.conn.dist_triangle (u:=c) (v:=t) (w:=b)
              omega
            refine ⟨t,?_,Or.inr hts,by simp [ev,hYt]⟩
            intro he; subst t; simp [SimpleGraph.dist_self] at hYt
  · exact ⟨b,fun he => S.not_b i (he.symm ▸ hc),Or.inl rfl,by simp [ev,h]⟩

theorem effective_a_extra {i : Bool} {c : V} (hc : c ∈ S.sides i)
    (hab : G.dist a b = 3) (h : EffectiveA G a b c) :
    ∃ t, t ≠ c ∧ (t = b ∨ t ∈ S.sides i) ∧ ev G c t = 1 := by
  by_cases hLong : 3 ≤ G.dist c a
  · obtain ⟨t,ht,hts,he⟩ := effective_a_extra_long S hc h hLong
    exact ⟨t,ht,Or.inr hts,by simp [ev,he]⟩
  · have hshort : G.dist c a = 1 := by have := h.1; omega
    exact effective_a_extra_short S hc hab h hshort

theorem effective_b_extra {i : Bool} {c : V} (hc : c ∈ S.sides i)
    (hab : G.dist a b = 3) (h : EffectiveA G b a c) :
    ∃ t, t ≠ c ∧ (t = a ∨ t ∈ S.sides i) ∧ ev G c t = 1 :=
  effective_a_extra (swapOther S) hc ((dist_comm (G:=G) (u:=b) (v:=a)).trans hab) h

theorem effective_coverage {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q) :
    cov G a b p q x = Graffiti189SixCentre.coverage (G.dist x a) (G.dist x b)
      (effectiveOpp G a b p) (effectiveOpp G b a q) := by
  unfold cov Graffiti189SixCentre.coverage
  rw [effective_a_coverage S hij hp hx hpa,effective_b_coverage S hij hq hx hqb]
  unfold ev Graffiti189SixCentre.evenBit
  rw [dist_comm (G:=G) (u:=a) (v:=x),dist_comm (G:=G) (u:=b) (v:=x)]

private theorem rangeEff {x : V} (h : EffectiveA G a b x) :
    2 ≤ effectiveOpp G a b x ∧ effectiveOpp G a b x ≤ 4 := by
  obtain ⟨_,hl,hu⟩ := h
  unfold effectiveOpp
  omega

include S in
private theorem terminalEffDiff (hab : G.dist a b = 3) (x : V) :
    G.dist x a ≤ G.dist x b + 3 ∧ G.dist x b ≤ G.dist x a + 3 := by
  have h₁ := S.conn.dist_triangle (u:=x) (v:=b) (w:=a)
  have h₂ := S.conn.dist_triangle (u:=x) (v:=a) (w:=b)
  rw [dist_comm (G:=G) (u:=b) (v:=a),hab] at h₁
  rw [hab] at h₂
  exact ⟨h₁,h₂⟩

theorem effective_coverage_interval (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q) :
    1 ≤ cov G a b p q x ∧ cov G a b p q x ≤ 3 := by
  rw [effective_coverage S hij hp hq hx hpa hqb]
  obtain ⟨h₁,h₂⟩ := terminalEffDiff S hab x
  obtain ⟨h₃,h₄⟩ := rangeEff hpa
  obtain ⟨h₅,h₆⟩ := rangeEff hqb
  exact ⟨Graffiti189SixCentre.coverage_positive _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆,
    Graffiti189SixCentre.coverage_at_most_three _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆⟩

private theorem terminalEffSpend (d : ℕ) (hBudget : EvenBudget G d)
    {t : V} (ht0 : t ∉ S.sides false) (ht1 : t ∉ S.sides true) :
    evAmount G t (S.sides false) + evAmount G t (S.sides true) ≤ d := by
  have ht : t ∉ S.sides false ∪ S.sides true := by simp [ht0,ht1]
  have hh := Finset.sum_le_sum_of_subset (f := ev G t)
    (Finset.subset_univ (insert t (S.sides false ∪ S.sides true)))
  rw [Finset.sum_insert ht,Finset.sum_union S.disj] at hh
  have he : ev G t t = 1 := by simp [ev,SimpleGraph.dist_self]
  rw [he] at hh
  have hp := hBudget t
  unfold evAmount at hp ⊢
  omega

private theorem effectiveSpend (d : ℕ) (hBudget : EvenBudget G d)
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
  have hY : y ∉ S.sides j := disjoint_left.1 hD hy
  have hT : t ∉ S.sides j := by
    rcases hts with rfl|rfl|ht'
    · exact S.not_a j
    · exact S.not_b j
    · exact disjoint_left.1 hD ht'
  have hYt : y ∉ insert t (S.sides j) := by simp [hty.symm,hY]
  have hh := Finset.sum_le_sum_of_subset (f := ev G y)
    (Finset.subset_univ (insert y (insert t (S.sides j))))
  have he : ev G y y = 1 := by simp [ev,SimpleGraph.dist_self]
  rw [Finset.sum_insert hYt,Finset.sum_insert hT,he,hte] at hh
  have hp := hBudget y
  unfold evAmount at hp ⊢
  omega

private theorem spend_a (d : ℕ) (hBudget : EvenBudget G d) (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {c : V} (hc : c ∈ S.sides i) (he : EffectiveA G a b c) :
    evAmount G c (S.sides j) + 2 ≤ d+1 := by
  obtain ⟨t,ht,hcase,hev⟩ := effective_a_extra S hc hab he
  exact effectiveSpend S d hBudget hij hc ⟨t,ht,Or.inr hcase,hev⟩

private theorem spend_b (d : ℕ) (hBudget : EvenBudget G d) (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {c : V} (hc : c ∈ S.sides i) (he : EffectiveA G b a c) :
    evAmount G c (S.sides j) + 2 ≤ d+1 := by
  obtain ⟨t,ht,hcase,hev⟩ := effective_b_extra S hc hab he
  exact effectiveSpend S d hBudget hij hc
    ⟨t,ht,hcase.elim Or.inl (fun h => Or.inr (Or.inr h)),hev⟩

private theorem effective_side_card (hab : G.dist a b = 3) :
    Fintype.card V = (S.sides false).card + (S.sides true).card + 2 := by
  have hne : a ≠ b := by intro he; subst b; simp [SimpleGraph.dist_self] at hab
  have hay : a ∉ insert b (S.sides false ∪ S.sides true) := by simp [hne,S.not_a]
  have hby : b ∉ S.sides false ∪ S.sides true := by simp [S.not_b]
  have he : (univ : Finset V) = insert a (insert b (S.sides false ∪ S.sides true)) := by
    ext x
    simp only [mem_univ, mem_insert, mem_union, true_iff]
    exact S.covers x
  calc
    Fintype.card V = (univ : Finset V).card := card_univ.symm
    _ = _ := by rw [he,card_insert_of_not_mem hay,card_insert_of_not_mem hby,
                     card_union_of_disjoint S.disj]

theorem six_effective_centres_bound (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q)
    (hra : EffectiveA G a b r) (hsb : EffectiveA G b a s) :
    2*Fintype.card V + gains (S.sides false) (cov G a b r s) +
        gains (S.sides true) (cov G a b p q) ≤
      6*d + failures (S.sides false) (cov G a b r s) +
        failures (S.sides true) (cov G a b p q) := by
  have ha := terminalEffSpend S d hBudget (S.not_a false) (S.not_a true)
  have hb := terminalEffSpend S d hBudget (S.not_b false) (S.not_b true)
  have h₁ := spend_a S d hBudget hab (by decide : false ≠ true) hp hpa
  have h₂ := spend_b S d hBudget hab (by decide : false ≠ true) hq hqb
  have h₃ := spend_a S d hBudget hab (by decide : true ≠ false) hr hra
  have h₄ := spend_b S d hBudget hab (by decide : true ≠ false) hs hsb
  have charge (p q : V) (A : Finset V) :
      ∑ x ∈ A, cov G a b p q x =
        evAmount G a A + evAmount G b A + evAmount G p A + evAmount G q A := by
    simp only [cov,evAmount,Finset.sum_add_distrib]
  have hsum : (∑ x ∈ S.sides false, cov G a b r s x) +
      (∑ x ∈ S.sides true, cov G a b p q x) + 10 ≤ 6*(d+1) := by
    rw [charge,charge]
    omega
  have hX (x : V) (hx : x ∈ S.sides false) :=
    effective_coverage_interval S hab (by decide) hr hs hx hra hsb
  have hY (x : V) (hx : x ∈ S.sides true) :=
    effective_coverage_interval S hab (by decide) hp hq hx hpa hqb
  have hF := Graffiti189SixCentre.sum_coverage_accounting (S.sides false) (cov G a b r s)
    (fun x hx => (hX x hx).1) (fun x hx => (hX x hx).2)
  have hT := Graffiti189SixCentre.sum_coverage_accounting (S.sides true) (cov G a b p q)
    (fun x hx => (hY x hx).1) (fun x hx => (hY x hx).2)
  have hC := effective_side_card S hab
  unfold failures gains
  omega

include S in
theorem port_is_effective_a (hab : G.dist a b = 3) {c : V} (h : G.Adj c a) :
    EffectiveA G a b c := by
  have ha := dist_eq_one_iff_adj.2 h
  have h₁ := S.conn.dist_triangle (u:=a) (v:=c) (w:=b)
  have h₂ := S.conn.dist_triangle (u:=c) (v:=a) (w:=b)
  rw [dist_comm (G:=G) (u:=a) (v:=c),ha,hab] at h₁
  rw [ha,hab] at h₂
  unfold EffectiveA
  omega

include S in
theorem port_is_effective_b (hab : G.dist a b = 3) {c : V} (h : G.Adj c b) :
    EffectiveA G b a c :=
  port_is_effective_a (swapOther S) ((dist_comm (G:=G) (u:=b) (v:=a)).trans hab) h

theorem six_effective_centres_nonpositive_defect (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q)
    (hra : EffectiveA G a b r) (hsb : EffectiveA G b a s)
    (hDefect :
      failures (S.sides false) (cov G a b r s) + failures (S.sides true) (cov G a b p q) ≤
      gains (S.sides false) (cov G a b r s) + gains (S.sides true) (cov G a b p q)) :
    Fintype.card V ≤ 3*d := by
  have h := six_effective_centres_bound S d hBudget hab hp hq hr hs hpa hqb hra hsb
  omega

private theorem failureEffZero {A : Finset V} {f : V → ℕ} (h : ∀ x ∈ A, 2 ≤ f x) :
    failures A f = 0 := by
  unfold failures
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_not_mem.2
  intro x hx
  obtain ⟨h₁,h₂⟩ := Finset.mem_filter.1 hx
  have := h x h₁
  omega

theorem six_effective_centres_far (d : ℕ) (hBudget : EvenBudget G d)
    (hab : G.dist a b = 3) {p q r s : V}
    (hp : p ∈ S.sides false) (hq : q ∈ S.sides false)
    (hr : r ∈ S.sides true) (hs : s ∈ S.sides true)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q)
    (hra : EffectiveA G a b r) (hsb : EffectiveA G b a s)
    (hpb : effectiveOpp G a b p = 4) (hqa : effectiveOpp G b a q = 4)
    (hrb : effectiveOpp G a b r = 4) (hsa : effectiveOpp G b a s = 4) :
    Fintype.card V ≤ 3*d := by
  apply six_effective_centres_nonpositive_defect S d hBudget hab hp hq hr hs hpa hqb hra hsb
  have hX (x : V) (hx : x ∈ S.sides false) : 2 ≤ cov G a b r s x := by
    rw [effective_coverage S (by decide) hr hs hx hra hsb,hrb,hsa]
    obtain ⟨h₁,h₂⟩ := terminalEffDiff S hab x
    exact Graffiti189SixCentre.coverage_far_at_least_two _ _ h₁ h₂
  have hY (x : V) (hx : x ∈ S.sides true) : 2 ≤ cov G a b p q x := by
    rw [effective_coverage S (by decide) hp hq hx hpa hqb,hpb,hqa]
    obtain ⟨h₁,h₂⟩ := terminalEffDiff S hab x
    exact Graffiti189SixCentre.coverage_far_at_least_two _ _ h₁ h₂
  rw [failureEffZero hX,failureEffZero hY]
  simp

private theorem effectiveRareFailure (x y u v : ℕ)
    (hxy : x ≤ y+3) (hyx : y ≤ x+3)
    (hu : 3 ≤ u ∧ u ≤ 4) (hv : 3 ≤ v ∧ v ≤ 4) :
    Graffiti189SixCentre.coverage x y u v = 1 ↔
      (x = y+3 ∧ y%2=0 ∧ u=3) ∨ (y = x+3 ∧ x%2=0 ∧ v=3) := by
  rw [Graffiti189SixCentre.coverage_table _ _ _ _ hxy hyx
    (by omega) hu.2 (by omega) hv.2]
  unfold Graffiti189SixCentre.entry Graffiti189SixCentre.evenBit
  repeat' first | omega | split

/-- If the two selected centres have gaps at least two, the only
remaining uncovered incidence is the gap-three, even-nearer profile,
and only if that orientation uses effective opposite distance three. -/
theorem effective_coverage_rare_failure (hab : G.dist a b = 3)
    {i j : Bool} (hij : i ≠ j) {p q x : V}
    (hp : p ∈ S.sides i) (hq : q ∈ S.sides i) (hx : x ∈ S.sides j)
    (hpa : EffectiveA G a b p) (hqb : EffectiveA G b a q)
    (hpl : 3 ≤ effectiveOpp G a b p) (hql : 3 ≤ effectiveOpp G b a q) :
    cov G a b p q x = 1 ↔
      (G.dist x a = G.dist x b + 3 ∧ G.dist x b % 2 = 0 ∧ effectiveOpp G a b p = 3) ∨
      (G.dist x b = G.dist x a + 3 ∧ G.dist x a % 2 = 0 ∧ effectiveOpp G b a q = 3) := by
  rw [effective_coverage S hij hp hq hx hpa hqb]
  obtain ⟨h₁,h₂⟩ := terminalEffDiff S hab x
  exact effectiveRareFailure _ _ _ _ h₁ h₂ ⟨hpl,(rangeEff hpa).2⟩ ⟨hql,(rangeEff hqb).2⟩

#print axioms effective_a_coverage
#print axioms effective_b_coverage
#print axioms effective_a_extra
#print axioms effective_b_extra
#print axioms six_effective_centres_bound
#print axioms six_effective_centres_nonpositive_defect
#print axioms six_effective_centres_far
#print axioms effective_coverage_rare_failure

end Graffiti189Adam
