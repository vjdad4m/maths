import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Written on the Wall II #321. -/

namespace Graffiti321

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def eccentricity (G : SimpleGraph V) (v : V) : ℕ := univ.sup (G.dist v)

noncomputable def transmission (G : SimpleGraph V) (v : V) : ℕ := ∑ w, G.dist v w

noncomputable def maxTransmission (G : SimpleGraph V) : ℕ := univ.sup (transmission G)

noncomputable def sumEccentricities (G : SimpleGraph V) : ℕ := ∑ v, eccentricity G v

noncomputable def averageEccentricity (G : SimpleGraph V) : ℚ :=
  (sumEccentricities G : ℚ) / Fintype.card V

def MetricPremise (G : SimpleGraph V) : Prop :=
  (maxTransmission G : ℚ) / 3 ≤ averageEccentricity G

def IntegralPremise (G : SimpleGraph V) : Prop :=
  Fintype.card V * maxTransmission G ≤ 3 * sumEccentricities G

omit [Fintype V] in
def TotalDominates (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, ∃ u ∈ S, G.Adj v u

omit [Fintype V] in
def MinimalTotalDominates (G : SimpleGraph V) (S : Finset V) : Prop :=
  TotalDominates G S ∧ ∀ T : Finset V, T ⊂ S → ¬TotalDominates G T

omit [Fintype V] in
def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ S, MinimalTotalDominates G S → ∀ T, TotalDominates G T → S.card ≤ T.card

theorem premise_iff_integral (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    MetricPremise G ↔ IntegralPremise G := by
  have hnq : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  unfold MetricPremise averageEccentricity IntegralPremise
  rw [le_div_iff₀ hnq, div_mul_eq_mul_div, div_le_iff₀ (by decide : (0 : ℚ) < 3)]
  rw [mul_comm (maxTransmission G : ℚ) (Fintype.card V : ℚ),
    mul_comm (sumEccentricities G : ℚ) (3 : ℚ)]
  norm_cast

private noncomputable def diameter (G : SimpleGraph V) : ℕ := univ.sup (eccentricity G)

private theorem dist_le_ecc (G : SimpleGraph V) (u v : V) :
    G.dist u v ≤ eccentricity G u :=
  le_sup (f := G.dist u) (mem_univ v)

private theorem ecc_le_diam (G : SimpleGraph V) (v : V) : eccentricity G v ≤ diameter G :=
  le_sup (f := eccentricity G) (mem_univ v)

private theorem sum_ecc_le (G : SimpleGraph V) :
    sumEccentricities G ≤ Fintype.card V * diameter G := by
  simpa [sumEccentricities, Nat.mul_comm] using
    (sum_le_sum (s := univ) (fun v _ => ecc_le_diam G v))

private theorem diam_attained (G : SimpleGraph V) [Nonempty V] :
    ∃ a b, G.dist a b = diameter G := by
  obtain ⟨a, _, ha⟩ := exists_mem_eq_sup _ univ_nonempty (eccentricity G)
  obtain ⟨b, _, hb⟩ := exists_mem_eq_sup _ univ_nonempty (G.dist a)
  exact ⟨a, b, hb.symm.trans ha.symm⟩

private theorem transmissions_bound (G : SimpleGraph V) (h : G.Connected) (a b : V) :
    Fintype.card V * G.dist a b ≤ transmission G a + transmission G b := by
  have hterm (v : V) : G.dist a b ≤ G.dist a v + G.dist b v := by
    rw [G.dist_comm (u := b) (v := v)]
    exact h.dist_triangle
  simpa [transmission, sum_add_distrib, Nat.mul_comm] using
    (sum_le_sum (s := univ) (fun v _ => hterm v))

private theorem transmission_le_max (G : SimpleGraph V) (v : V) :
    transmission G v ≤ maxTransmission G :=
  le_sup (f := transmission G) (mem_univ v)

private theorem diam_mul_order_le (G : SimpleGraph V) (h : G.Connected) :
    Fintype.card V * diameter G ≤ 2 * maxTransmission G := by
  haveI := h.nonempty
  obtain ⟨a,b,hab⟩ := diam_attained G
  rw [← hab, two_mul]
  exact (transmissions_bound G h a b).trans
    (Nat.add_le_add (transmission_le_max G a) (transmission_le_max G b))

private theorem diameter_positive (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) : 0 < diameter G := by
  obtain ⟨u⟩ := hc.nonempty
  obtain ⟨v,hv⟩ := Fintype.exists_ne_of_one_lt_card hn u
  exact (hc.pos_dist_of_ne hv.symm).trans_le ((dist_le_ecc G u v).trans (ecc_le_diam G u))

theorem order_le_six (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) (h : IntegralPremise G) : Fintype.card V ≤ 6 := by
  have h₁ := diam_mul_order_le G hc
  have h₂ := sum_ecc_le G
  have hp := diameter_positive G hc hn
  have hb : Fintype.card V * (Fintype.card V * diameter G) ≤
      Fintype.card V * (6 * diameter G) := by
    calc
      _ ≤ Fintype.card V * (2 * maxTransmission G) := Nat.mul_le_mul_left _ h₁
      _ = 2 * (Fintype.card V * maxTransmission G) := by ring
      _ ≤ 2 * (3 * sumEccentricities G) := Nat.mul_le_mul_left _ h
      _ ≤ Fintype.card V * (6 * diameter G) := by nlinarith
  exact Nat.le_of_mul_le_mul_right
    (Nat.le_of_mul_le_mul_left hb (by omega)) hp

private theorem equalities_at_six (G : SimpleGraph V) (hc : G.Connected)
    (hn : Fintype.card V = 6) (h : IntegralPremise G) :
    sumEccentricities G = 6 * diameter G ∧ maxTransmission G = 3 * diameter G := by
  have h₁ := diam_mul_order_le G hc
  have h₂ := sum_ecc_le G
  unfold IntegralPremise at h
  rw [hn] at h h₁ h₂
  omega

private theorem ecc_eq_diameter_at_six (G : SimpleGraph V) (hc : G.Connected)
    (hn : Fintype.card V = 6) (h : IntegralPremise G) (v : V) :
    eccentricity G v = diameter G := by
  apply (ecc_le_diam G v).antisymm
  by_contra! hv
  have hs := Finset.sum_lt_sum (s := (univ : Finset V))
    (fun w _ => ecc_le_diam G w) ⟨v, mem_univ v, hv⟩
  have hs' : sumEccentricities G < Fintype.card V * diameter G := by
    simpa [sumEccentricities, Nat.mul_comm] using hs
  rw [hn, (equalities_at_six G hc hn h).1] at hs'
  exact (lt_irrefl _ hs')

private theorem antipode_sum (G : SimpleGraph V) (hc : G.Connected)
    (hn : Fintype.card V = 6) (h : IntegralPremise G) {a b : V}
    (hab : G.dist a b = diameter G) (v : V) :
    G.dist a v + G.dist b v = diameter G := by
  have lower (w : V) : diameter G ≤ G.dist a w + G.dist b w := by
    rw [← hab, G.dist_comm (u := b) (v := w)]
    exact hc.dist_triangle
  apply le_antisymm _ (lower v)
  by_contra! hv
  have hs := Finset.sum_lt_sum (s := (univ : Finset V))
    (fun w _ => lower w) ⟨v, mem_univ v, hv⟩
  have hs' : Fintype.card V * diameter G < transmission G a + transmission G b := by
    simpa [transmission, sum_add_distrib, Nat.mul_comm] using hs
  rw [hn] at hs'
  have ha := transmission_le_max G a
  have hb := transmission_le_max G b
  rw [(equalities_at_six G hc hn h).2] at ha hb
  omega

private theorem antipode_exists (G : SimpleGraph V) (hc : G.Connected)
    (hn : Fintype.card V = 6) (h : IntegralPremise G) (v : V) :
    ∃ w, G.dist v w = diameter G := by
  haveI := hc.nonempty
  obtain ⟨w,_,hw⟩ := exists_mem_eq_sup _ univ_nonempty (G.dist v)
  exact ⟨w, hw.symm.trans (ecc_eq_diameter_at_six G hc hn h v)⟩

private theorem low_diam_at_six (G : SimpleGraph V) (hc : G.Connected)
    (hn : Fintype.card V = 6) (hi : IntegralPremise G) (hd : diameter G ≤ 2) :
    WellTotalDominated G := by
  classical
  have edge_dominates {a b : V} (hab : G.Adj a b) :
      TotalDominates G {a,b} := by
    intro v
    by_cases ha : G.Adj v a
    · exact ⟨a, by simp, ha⟩
    by_cases hb : G.Adj v b
    · exact ⟨b, by simp, hb⟩
    have hva : v ≠ a := fun e => hb (e ▸ hab)
    have hvb : v ≠ b := fun e => ha (e ▸ hab.symm)
    have hdva : G.dist v a = diameter G := by
      have hpos := hc.pos_dist_of_ne hva
      have hne : G.dist v a ≠ 1 := fun e => ha (dist_eq_one_iff_adj.mp e)
      have hle := (dist_le_ecc G v a).trans (ecc_le_diam G v)
      omega
    have hdvb : G.dist v b = diameter G := by
      have hpos := hc.pos_dist_of_ne hvb
      have hne : G.dist v b ≠ 1 := fun e => hb (dist_eq_one_iff_adj.mp e)
      have hle := (dist_le_ecc G v b).trans (ecc_le_diam G v)
      omega
    have he := antipode_sum G hc hn hi hdva b
    rw [hdvb, dist_eq_one_iff_adj.mpr hab] at he
    omega
  have size_two {S : Finset V} (hs : TotalDominates G S) : ∃ a b,
      a ∈ S ∧ b ∈ S ∧ G.Adj a b := by
    obtain ⟨v⟩ := hc.nonempty
    obtain ⟨a,ha,_⟩ := hs v
    obtain ⟨b,hb,hab⟩ := hs a
    exact ⟨a,b,ha,hb,hab⟩
  intro S hs T ht
  obtain ⟨a,b,ha,hb,hab⟩ := size_two hs.1
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hpair : ({a,b} : Finset V) = S := by
    by_contra hne
    exact hs.2 _ (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩) (edge_dominates hab)
  rw [← hpair, card_pair hab.ne]
  obtain ⟨x,y,hx,hy,hxy⟩ := size_two ht
  exact one_lt_card.mpr ⟨x,hx,y,hy,hxy.ne⟩

private theorem degree_at_least_two_at_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : Fintype.card V = 6) (hi : IntegralPremise G)
    (hd : 3 ≤ diameter G) (v : V) : 2 ≤ G.degree v := by
  classical
  by_contra! hlow
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  obtain ⟨pw⟩ := hc.preconnected v u
  let w := pw.snd
  have hvw : G.Adj v w := pw.adj_snd (Walk.not_nil_of_ne hu.symm)
  have unique_neighbor (u : V) (hvu : G.Adj v u) : u = w :=
    card_le_one.mp (by
      rw [card_neighborFinset_eq_degree]
      omega) _
      ((G.mem_neighborFinset v u).mpr hvu) _ ((G.mem_neighborFinset v w).mpr hvw)
  obtain ⟨x,hx⟩ := antipode_exists G hc hn hi w
  have hne : v ≠ x := by
    intro e
    have hwv := dist_eq_one_iff_adj.mpr hvw.symm
    rw [e, hx] at hwv
    omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v x
  cases p with
  | nil => exact hne rfl
  | cons ha q =>
    have hq := G.dist_le q
    have eq := unique_neighbor _ ha
    have hdiam : diameter G ≤ q.length :=
      (hx.symm.trans (congrArg (fun a => G.dist a x) eq.symm)).le.trans hq
    have hvx := (dist_le_ecc G v x).trans (ecc_le_diam G v)
    simp only [Walk.length_cons] at hp
    omega

private theorem degree_two_at_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : Fintype.card V = 6) (hi : IntegralPremise G)
    (hd : 3 ≤ diameter G) (v : V) : G.degree v = 2 := by
  classical
  obtain ⟨w,hw⟩ := antipode_exists G hc hn hi v
  have hne : v ≠ w := by
    intro e
    rw [e, dist_self] at hw
    omega
  have hnAdj : ¬G.Adj v w := fun h => by
    have hd₁ := dist_eq_one_iff_adj.mpr h
    omega
  let A := G.neighborFinset v
  let B := G.neighborFinset w
  have hdj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have ha := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v z).mp hz₁)
    have hb := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset w z).mp hz₂).symm
    have ht := hc.dist_triangle (u := v) (v := z) (w := w)
    omega
  have hsub : A ∪ B ⊆ (univ.erase v).erase w := by
    intro z hz
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_,mem_univ _⟩⟩
    · intro e
      subst z
      rcases mem_union.mp hz with h1 | h2
      · exact hnAdj ((G.mem_neighborFinset v w).mp h1)
      · exact G.loopless _ ((G.mem_neighborFinset w w).mp h2)
    · intro e
      subst z
      rcases mem_union.mp hz with h1 | h2
      · exact G.loopless _ ((G.mem_neighborFinset v v).mp h1)
      · exact hnAdj ((G.mem_neighborFinset w v).mp h2).symm
  have hcard := card_le_card hsub
  have hv := card_erase_add_one (s := (univ : Finset V)) (mem_univ v)
  have hw' := card_erase_add_one (s := (univ : Finset V).erase v)
    (mem_erase.mpr ⟨hne.symm, mem_univ _⟩)
  rw [card_univ, hn] at hv
  rw [card_union_of_disjoint hdj] at hcard
  change G.degree v + G.degree w ≤ _ at hcard
  have hmin₁ := degree_at_least_two_at_six G hc hn hi hd v
  have hmin₂ := degree_at_least_two_at_six G hc hn hi hd w
  omega


section Census

variable {n : ℕ}

private def triangular : ℕ → ℕ
  | 0 => 0
  | k+1 => triangular k + k

private theorem triangular_mono : Monotone triangular :=
  monotone_nat_of_le_succ (fun _ => Nat.le_add_right _ _)

private def pairIndex (u v : Fin n) : ℕ := triangular v.val + u.val

private theorem pairIndex_lt {u v : Fin n} (h : u < v) :
    pairIndex u v < triangular n := by
  have h₁ : pairIndex u v < triangular (v.val + 1) := by
    change triangular v.val + u.val < triangular v.val + v.val
    exact Nat.add_lt_add_left h _
  exact h₁.trans_le (triangular_mono (by omega : v.val + 1 ≤ n))

private theorem pairIndex_inj {u v u' v' : Fin n} (h : u < v) (h' : u' < v')
    (he : pairIndex u v = pairIndex u' v') : u = u' ∧ v = v' := by
  have vv : v = v' := by
    rcases lt_trichotomy v v' with hlt | heq | hgt
    · have h₁ : pairIndex u v < triangular (v.val+1) := by
        change triangular v.val + u.val < triangular v.val + v.val
        exact Nat.add_lt_add_left h _
      have h₂ := triangular_mono (show v.val+1 ≤ v'.val from Nat.succ_le_of_lt hlt)
      have h₃ : triangular v'.val ≤ pairIndex u' v' := Nat.le_add_right _ _
      omega
    · exact heq
    · have h₁ : pairIndex u' v' < triangular (v'.val+1) := by
        change triangular v'.val + u'.val < triangular v'.val + v'.val
        exact Nat.add_lt_add_left h' _
      have h₂ := triangular_mono (show v'.val+1 ≤ v.val from Nat.succ_le_of_lt hgt)
      have h₃ : triangular v.val ≤ pairIndex u v := Nat.le_add_right _ _
      omega
  subst v'
  exact ⟨Fin.ext (Nat.add_left_cancel he), rfl⟩

private theorem encode_bits (m : ℕ) (f : Fin m → Bool) :
    ∃ b < 2^m, ∀ i : Fin m, Nat.testBit b i.val = f i := by
  induction m with
  | zero => exact ⟨0, by decide, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨b,hb,he⟩ := ih (fun i => f i.succ)
    let addBit : ℕ := if f 0 then 1 else 0
    have hadd : addBit < 2 := by unfold addBit; split <;> decide
    refine ⟨2*b + addBit, ?_, ?_⟩
    · rw [pow_succ]; omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.val_zero, Nat.testBit_zero]
        have hmod : (2*b + addBit) % 2 = addBit := by omega
        rw [hmod]
        unfold addBit
        cases f 0 <;> decide
      · rw [Fin.val_succ, Nat.testBit_succ]
        have hdiv : (2*b + addBit) / 2 = b := by omega
        rw [hdiv]
        exact he j

private def adjOfMask (m : ℕ) (u v : Fin n) : Prop :=
  (u < v ∧ m.testBit (pairIndex u v) = true) ∨
    (v < u ∧ m.testBit (pairIndex v u) = true)

private instance (m : ℕ) : DecidableRel (@adjOfMask n m) :=
  fun _ _ => by unfold adjOfMask; infer_instance

private def graphOfMask (n m : ℕ) : SimpleGraph (Fin n) where
  Adj := adjOfMask m
  symm := fun _ _ h => h.symm
  loopless := by
    intro u
    simp [adjOfMask]

private instance graphOfMask_decidable (m : ℕ) : DecidableRel (graphOfMask n m).Adj :=
  inferInstanceAs (DecidableRel (@adjOfMask n m))

private theorem masks_cover (G : SimpleGraph (Fin n)) :
    ∃ m < 2 ^ triangular n, G = graphOfMask n m := by
  classical
  let f (i : Fin (triangular n)) : Bool :=
    decide (∃ u v : Fin n, u < v ∧ pairIndex u v = i.val ∧ G.Adj u v)
  obtain ⟨m,hm,hf⟩ := encode_bits _ f
  refine ⟨m,hm,?_⟩
  have edge_iff {u v : Fin n} (h : u < v) :
      m.testBit (pairIndex u v) = true ↔ G.Adj u v := by
    rw [show pairIndex u v = (⟨pairIndex u v,pairIndex_lt h⟩ : Fin (triangular n)).val
      from rfl, hf]
    simp only [f, decide_eq_true_eq, Fin.val_mk]
    constructor
    · rintro ⟨a,b,hab,he,ha⟩
      obtain ⟨hu,hv⟩ := pairIndex_inj hab h he
      simpa [hu,hv] using ha
    · intro ha
      exact ⟨u,v,h,rfl,ha⟩
  ext u v
  change G.Adj u v ↔ adjOfMask m u v
  constructor
  · intro h
    rcases lt_or_gt_of_ne h.ne with he | he
    · exact Or.inl ⟨he,(edge_iff he).mpr h⟩
    · exact Or.inr ⟨he,(edge_iff he).mpr h.symm⟩
  · rintro (⟨he,h⟩ | ⟨he,h⟩)
    · exact (edge_iff he).mp h
    · exact ((edge_iff he).mp h).symm

private instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) :
    Decidable (TotalDominates G s) := by
  unfold TotalDominates
  infer_instance

private def setOfMask (m : ℕ) : Finset (Fin n) :=
  univ.filter fun v => m.testBit v.val = true

private theorem set_mask_cover (S : Finset (Fin n)) :
    ∃ m < 2^n, setOfMask m = S := by
  obtain ⟨m,hm,h⟩ := encode_bits n (fun v => decide (v ∈ S))
  exact ⟨m,hm,by ext v; simp [setOfMask,h v]⟩

private def joinBits (xs : List (Fin n)) (get : Fin n → ℕ) (use : Fin n → Bool) : ℕ :=
  xs.foldr (fun a out => if use a then get a ||| out else out) 0

private theorem testBit_joinBits (xs : List (Fin n)) (get : Fin n → ℕ)
    (use : Fin n → Bool) (k : ℕ) :
    (joinBits xs get use).testBit k = true ↔ ∃ a ∈ xs, use a = true ∧ (get a).testBit k = true := by
  induction xs with
  | nil => simp [joinBits]
  | cons a xs ih =>
    by_cases ha : use a = true
    · simp only [joinBits, List.foldr_cons, ha, if_true, Nat.testBit_or, Bool.or_eq_true]
      change (get a).testBit k = true ∨ (joinBits xs get use).testBit k = true ↔ _
      rw [ih]
      constructor
      · rintro (h | ⟨b,hb,hu,ht⟩)
        · exact ⟨a, List.mem_cons_self .., ha, h⟩
        · exact ⟨b,List.mem_cons_of_mem _ hb,hu,ht⟩
      · rintro ⟨b,hb,hu,ht⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl ht
        · exact Or.inr ⟨b,hb,hu,ht⟩
    · change ((if use a then get a ||| joinBits xs get use else joinBits xs get use).testBit k
          = true) ↔ _
      rw [if_neg ha, ih]
      constructor
      · rintro ⟨b,hb,hu,ht⟩
        exact ⟨b,List.mem_cons_of_mem _ hb,hu,ht⟩
      · rintro ⟨b,hb,hu,ht⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact (ha hu).elim
        · exact ⟨b,hb,hu,ht⟩

private def neighborBits (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) : ℕ :=
  joinBits (List.finRange n) (fun v => 2^v.val) (fun v => decide (G.Adj u v))

private theorem neighborBits_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : (neighborBits G u).testBit v.val = true ↔ G.Adj u v := by
  rw [neighborBits, testBit_joinBits]
  simp only [Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨w,_,hw,he⟩
    exact (Fin.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v,List.mem_ofFn.mpr ⟨v,rfl⟩,hv,rfl⟩

private def neighborRows (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Fin n → ℕ :=
  let rows := Array.ofFn (neighborBits G)
  fun v => rows[v.val]'(by simp [rows])

private theorem neighborRows_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : neighborRows G u = neighborBits G u := by
  simp [neighborRows]

private def tdMask {n : ℕ} (get : Fin n → ℕ) (m : ℕ) : Bool :=
  let allNeighbors := joinBits (List.finRange n) get (fun u => m.testBit u.val)
  (List.finRange n).all (fun v => allNeighbors.testBit v.val)

private theorem tdMask_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) :
    tdMask (neighborRows G) m = true ↔ TotalDominates G (setOfMask m) := by
  unfold tdMask TotalDominates
  simp only [List.all_eq_true, testBit_joinBits, neighborRows_eq, neighborBits_correct,
    setOfMask, mem_filter, mem_univ, true_and]
  constructor
  · intro h v
    obtain ⟨u,_,hm,ha⟩ := h v (List.mem_ofFn.mpr ⟨v,rfl⟩)
    exact ⟨u,hm,ha.symm⟩
  · intro h v _
    obtain ⟨u,hm,ha⟩ := h v
    exact ⟨u,List.mem_ofFn.mpr ⟨u,rfl⟩,hm,ha.symm⟩

private theorem setOfMask_xor (m : ℕ) (v : Fin n) (hv : v ∈ setOfMask m) :
    setOfMask (m ^^^ 2^v.val) = (setOfMask m).erase v := by
  ext w
  have hbit : m.testBit v.val = true := (mem_filter.mp hv).2
  simp only [setOfMask,mem_filter,mem_univ,true_and,mem_erase,Nat.testBit_xor,Nat.testBit_two_pow]
  by_cases h : w = v
  · subst w
    simp [hbit]
  · have hn : v.val ≠ w.val := fun he => h (Fin.ext he.symm)
    simp [h,hn]

private def minimalMask {n : ℕ} (get : Fin n → ℕ) (m : ℕ) : Bool :=
  tdMask get m && (List.finRange n).all
    (fun v => !m.testBit v.val || !(tdMask get (m ^^^ 2^v.val)))

private def goodMasks (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  (List.range (2^n)).filter (minimalMask (neighborRows G))

private theorem minimal_mem_goodMasks {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} (hm : m < 2^n) (h : MinimalTotalDominates G (setOfMask m)) :
    m ∈ goodMasks G := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr hm, ?_⟩
  simp only [minimalMask, Bool.and_eq_true]
  refine ⟨(tdMask_correct G m).mpr h.1, ?_⟩
  apply List.all_eq_true.mpr
  intro v _
  by_cases hbit : m.testBit v.val = true
  · have hv : v ∈ setOfMask m := mem_filter.mpr ⟨mem_univ _,hbit⟩
    have hn := h.2 _ (erase_ssubset hv)
    simp only [hbit, Bool.not_true, Bool.false_or, Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro ht
    have ht' := (tdMask_correct G _).mp ht
    rw [setOfMask_xor m v hv] at ht'
    exact hn ht'
  · have hfalse := Bool.eq_false_iff.mpr hbit
    simp [hfalse]

private def checkWell (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Bool :=
  match goodMasks G with
  | [] => true
  | m :: ms => ms.all fun x => decide
      ((setOfMask (n := n) x).card = (setOfMask (n := n) m).card)

private theorem checkWell_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : checkWell G = true) : WellTotalDominated G := by
  intro S hs T ht
  let choices := T.powerset.filter (TotalDominates G)
  have hn : choices.Nonempty := ⟨T, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, ht⟩⟩
  obtain ⟨U, hU, hminU⟩ := exists_min_image choices card hn
  have hu := mem_filter.mp hU
  have humin : MinimalTotalDominates G U := by
    refine ⟨hu.2, fun A hA hAd => ?_⟩
    have hmem : A ∈ choices :=
      mem_filter.mpr ⟨mem_powerset.mpr (hA.subset.trans (mem_powerset.mp hu.1)), hAd⟩
    exact (Nat.not_lt_of_ge (hminU A hmem)) (card_lt_card hA)
  obtain ⟨s,hslim,hsSet⟩ := set_mask_cover S
  obtain ⟨u,hulim,huSet⟩ := set_mask_cover U
  have hsGood := minimal_mem_goodMasks hslim (hsSet.symm ▸ hs)
  have huGood := minimal_mem_goodMasks hulim (huSet.symm ▸ humin)
  unfold checkWell at h
  cases he : goodMasks G with
  | nil =>
    rw [he] at hsGood
    exact (List.not_mem_nil hsGood).elim
  | cons a js =>
    rw [he] at h hsGood huGood
    have hsame (x : ℕ) (hx : x ∈ a :: js) :
        (setOfMask (n := n) x).card = (setOfMask (n := n) a).card := by
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact decide_eq_true_eq.mp (List.all_eq_true.mp h x hx)
    have heq := (hsame s hsGood).trans (hsame u huGood).symm
    rw [hsSet,huSet] at heq
    rw [heq]
    exact card_le_card (mem_powerset.mp hu.1)

private def within (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℕ → Fin n → Fin n → Bool
  | 0, u, v => decide (u = v)
  | k+1, u, v => decide (u = v) || (List.finRange n).any
      (fun x => decide (G.Adj u x) && within G k x v)

private theorem within_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (u v : Fin n) :
    within G k u v = true ↔ ∃ p : G.Walk u v, p.length ≤ k := by
  induction k generalizing u with
  | zero =>
    simp only [within, decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨.nil, le_rfl⟩
    · rintro ⟨p,hp⟩
      exact p.eq_of_length_eq_zero (Nat.le_zero.mp hp)
  | succ k ih =>
    simp only [within, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro (rfl | ⟨x,_,hx,hw⟩)
      · exact ⟨.nil, Nat.zero_le _⟩
      · obtain ⟨p,hp⟩ := (ih x).mp hw
        exact ⟨.cons hx p, Nat.succ_le_succ hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl rfl
      | @cons a b c e p =>
        have hb : b ∈ List.finRange n := List.mem_ofFn.mpr ⟨b,rfl⟩
        exact Or.inr ⟨b, hb, e, (ih b).mpr ⟨p, Nat.le_of_succ_le_succ hp⟩⟩

private def calcDist (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) : ℕ :=
  (List.range n).findIdx (fun k => within G k u v)

private theorem calcDist_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : G.Connected) (u v : Fin n) : calcDist G u v = G.dist u v := by
  obtain ⟨p,hp,hl⟩ := hc.exists_path_of_dist u v
  have hsize := hp.length_lt
  rw [hl, show Fintype.card (Fin n) = n by simp] at hsize
  unfold calcDist
  apply (List.findIdx_eq (by simpa : G.dist u v < (List.range n).length)).mpr
  constructor
  · simpa only [List.getElem_range] using (within_spec G _ _ _).mpr ⟨p,hl.le⟩
  · intro j hj
    rw [List.getElem_range]
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q,hq⟩ := (within_spec G j u v).mp h
    exact (not_le_of_gt hj) ((G.dist_le q).trans hq)

private def checkPremise (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  n * univ.sup (fun v => ∑ w, calcDist G v w) ≤
    3 * ∑ v, univ.sup (calcDist G v)

private instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Decidable (checkPremise G) := by unfold checkPremise; infer_instance

private theorem checkPremise_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : G.Connected) : checkPremise G ↔ IntegralPremise G := by
  have he : calcDist G = G.dist := funext (fun u => funext (calcDist_correct G hc u))
  simp only [checkPremise, he, IntegralPremise, Fintype.card_fin,
    maxTransmission, sumEccentricities, eccentricity]
  rfl

private def checkedSmall (n m : ℕ) : Prop :=
  checkWell (graphOfMask n m) = true ∨ ¬checkPremise (graphOfMask n m)

private instance (n m : ℕ) : Decidable (checkedSmall n m) := by
  unfold checkedSmall
  infer_instance

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false

private theorem census_two : ∀ m : Fin 2, checkedSmall 2 m.val := by decide +kernel
private theorem census_three : ∀ m : Fin 8, checkedSmall 3 m.val := by decide +kernel
private theorem census_four : ∀ m : Fin 64, checkedSmall 4 m.val := by decide +kernel

#eval "Orders 2–4 checked"

private theorem census_five_blocks (i : Fin 16) :
    ∀ j : Fin 64, checkedSmall 5 (i.val * 64 + j.val) := by
  fin_cases i <;> decide +kernel

private theorem census_five (m : Fin 1024) : checkedSmall 5 m.val := by
  let i : Fin 16 := ⟨m.val/64, by omega⟩
  let j : Fin 64 := ⟨m.val%64, by omega⟩
  have h : i.val * 64 + j.val = m.val := by dsimp [i,j]; omega
  simpa only [h] using census_five_blocks i j

#eval "Order 5 checked"

private theorem small_order_good (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hi : IntegralPremise G) (h : ∀ m : Fin (2^triangular n), checkedSmall n m.val) :
    WellTotalDominated G := by
  obtain ⟨m,hm,rfl⟩ := masks_cover G
  rcases h ⟨m,hm⟩ with h | h
  · exact checkWell_sound h
  · exact (h ((checkPremise_correct _ hc).mpr hi)).elim

/-- The two diametral endpoints have disjoint pairs of neighbors.
The only remaining choices are the six edges among the four other vertices. -/
private def exterior (u v : Fin 6) : Prop :=
  (u = 4 ∧ (v = 0 ∨ v = 1)) ∨ (u = 5 ∧ (v = 2 ∨ v = 3))

private def patternAdj (G : SimpleGraph (Fin 4)) (u v : Fin 6) : Prop :=
  if h : u.val < 4 ∧ v.val < 4 then G.Adj ⟨u.val,h.1⟩ ⟨v.val,h.2⟩
  else exterior u v ∨ exterior v u

private def patternGraph (G : SimpleGraph (Fin 4)) : SimpleGraph (Fin 6) where
  Adj := patternAdj G
  symm := by
    intro u v h
    by_cases hu : u.val < 4 ∧ v.val < 4
    · have hv : v.val < 4 ∧ u.val < 4 := hu.symm
      rw [patternAdj, dif_pos hu] at h
      rw [patternAdj, dif_pos hv]
      exact h.symm
    · have hv : ¬ (v.val < 4 ∧ u.val < 4) := fun h => hu h.symm
      rw [patternAdj, dif_neg hu] at h
      rw [patternAdj, dif_neg hv]
      exact h.symm
  loopless := by
    intro u
    rw [patternAdj]
    split
    · exact G.loopless _
    · simp only [or_self, exterior, not_or, not_and]
      constructor <;> intro h <;> subst u <;> decide

private instance patternAdj_decidable (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    DecidableRel (patternGraph G).Adj := fun u v => by
  change Decidable (patternAdj G u v)
  unfold patternAdj exterior
  infer_instance

private def checkedPattern (m : ℕ) : Prop :=
  checkWell (patternGraph (graphOfMask 4 m)) = true ∨
    ¬checkPremise (patternGraph (graphOfMask 4 m))

private instance (m : ℕ) : Decidable (checkedPattern m) := by
  unfold checkedPattern
  infer_instance

private theorem census_six : ∀ m : Fin 64, checkedPattern m.val := by decide +kernel

private theorem pattern_good (H : SimpleGraph (Fin 6)) (hc : H.Connected)
    (hi : IntegralPremise H) (ha : ∀ v, H.Adj 4 v ↔ v = 0 ∨ v = 1)
    (hb : ∀ v, H.Adj 5 v ↔ v = 2 ∨ v = 3) :
    WellTotalDominated H := by
  let e : Fin 4 → Fin 6 := Fin.castLE (by decide)
  let inner := H.comap e
  have ha' (u : Fin 6) : H.Adj u 4 ↔ u = 0 ∨ u = 1 := (H.adj_comm _ _).trans (ha u)
  have hb' (u : Fin 6) : H.Adj u 5 ↔ u = 2 ∨ u = 3 := (H.adj_comm _ _).trans (hb u)
  have heq : H = patternGraph inner := by
    ext u v
    change H.Adj u v ↔ patternAdj inner u v
    by_cases hh : u.val < 4 ∧ v.val < 4
    · rw [patternAdj, dif_pos hh]
      rfl
    · rw [patternAdj, dif_neg hh]
      have small : u = 4 ∨ u = 5 ∨ v = 4 ∨ v = 5 := by
        have hu := u.isLt
        have hv := v.isLt
        simp only [Fin.ext_iff] at *
        change u.val = 4 ∨ u.val = 5 ∨ v.val = 4 ∨ v.val = 5
        omega
      rcases small with rfl | rfl | rfl | rfl
      · simp [exterior,ha]
      · simp [exterior,hb]
      · simp [exterior,ha']
      · simp [exterior,hb']
  rw [heq] at hc hi ⊢
  obtain ⟨m,hm,hinner⟩ := masks_cover inner
  rw [hinner] at hc hi ⊢
  rcases census_six ⟨m,hm⟩ with h | h
  · exact checkWell_sound h
  · exact (h ((checkPremise_correct _ hc).mpr hi)).elim

end Census

section Relabeling

variable {W : Type*} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

omit [Fintype V] [Fintype W] in
private theorem iso_dist (e : G ≃g H) (hc : G.Connected) (u v : V) :
    G.dist u v = H.dist (e u) (e v) := by
  have hh := hc.map e.toHom e.surjective
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  obtain ⟨q,hq⟩ := hh.exists_walk_length_eq_dist (e u) (e v)
  apply le_antisymm
  · have hqu : e.symm.toHom (e u) = u := e.symm_apply_apply u
    have hqv : e.symm.toHom (e v) = v := e.symm_apply_apply v
    simpa only [Walk.length_map, hq, hqu, hqv] using G.dist_le (q.map e.symm.toHom)
  · simpa only [Walk.length_map, hp] using H.dist_le (p.map e.toHom)

private theorem sup_relabel {f : V → ℕ} {g : W → ℕ} (e : V ≃ W)
    (he : ∀ v, f v = g (e v)) : univ.sup f = univ.sup g := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    rw [he]
    exact le_sup (f := g) (mem_univ _)
  · apply Finset.sup_le
    intro w _
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [← he]
    exact le_sup (f := f) (mem_univ _)

private theorem relabel_premise (e : G ≃g H) (hc : G.Connected) (h : IntegralPremise G) :
    IntegralPremise H := by
  have ht (v : V) : transmission G v = transmission H (e v) :=
    Fintype.sum_equiv e.toEquiv _ _ (iso_dist e hc v)
  have hm : maxTransmission G = maxTransmission H := sup_relabel e.toEquiv ht
  have he (v : V) : eccentricity G v = eccentricity H (e v) :=
    sup_relabel e.toEquiv (iso_dist e hc v)
  have hs : sumEccentricities G = sumEccentricities H :=
    Fintype.sum_equiv e.toEquiv _ _ he
  unfold IntegralPremise at h ⊢
  rwa [← e.card_eq, ← hm, ← hs]

omit [Fintype V] [Fintype W] in
private theorem totalDominates_map_iff (e : G ≃g H) (S : Finset V) :
    TotalDominates H (S.map e.toEquiv.toEmbedding) ↔ TotalDominates G S := by
  constructor
  · intro h v
    obtain ⟨w,hw,ha⟩ := h (e v)
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hw
    exact ⟨u,hu,e.map_adj_iff.mp ha⟩
  · intro h w
    obtain ⟨v,rfl⟩ := e.surjective w
    obtain ⟨u,hu,ha⟩ := h v
    exact ⟨e u,mem_map.mpr ⟨u,hu,rfl⟩,e.map_adj_iff.mpr ha⟩

omit [Fintype V] [Fintype W] in
private theorem wellTotalDominated_of_iso (e : G ≃g H) (h : WellTotalDominated H) :
    WellTotalDominated G := by
  intro S hs T ht
  let S' := S.map e.toEquiv.toEmbedding
  let T' := T.map e.toEquiv.toEmbedding
  have hS : MinimalTotalDominates H S' := by
    refine ⟨(totalDominates_map_iff e S).mpr hs.1, ?_⟩
    intro U hu hU
    let U' := U.map e.symm.toEquiv.toEmbedding
    have hemb :
        e.symm.toEquiv.toEmbedding.trans e.toEquiv.toEmbedding = Function.Embedding.refl W := by
      ext w
      exact e.apply_symm_apply w
    have heq : U'.map e.toEquiv.toEmbedding = U := by
      change (U.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding = U
      rw [Finset.map_map, hemb, Finset.map_refl]
    rw [← heq] at hu hU
    exact hs.2 U' ((Finset.map_ssubset_map).mp hu) ((totalDominates_map_iff e U').mp hU)
  have ht' : TotalDominates H T' := (totalDominates_map_iff e T).mpr ht
  have hcard := h S' hS T' ht'
  simpa only [S', T', card_map] using hcard

end Relabeling

private theorem high_diam_at_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : Fintype.card V = 6) (hi : IntegralPremise G)
    (hd : 3 ≤ diameter G) : WellTotalDominated G := by
  classical
  haveI := hc.nonempty
  obtain ⟨a,b,hab⟩ := diam_attained G
  have habne : a ≠ b := by
    intro h
    rw [h,dist_self] at hab
    omega
  have habna : ¬G.Adj a b := fun h => by
    have hp := dist_eq_one_iff_adj.mpr h
    omega
  have hdeg (v : V) : (G.neighborFinset v).card = 2 :=
    degree_two_at_six G hc hn hi hd v
  obtain ⟨x₀,x₁,hxx,hna⟩ := card_eq_two.mp (hdeg a)
  obtain ⟨y₀,y₁,hyy,hnb⟩ := card_eq_two.mp (hdeg b)
  have hxa (x : V) : G.Adj a x ↔ x = x₀ ∨ x = x₁ := by
    rw [← G.mem_neighborFinset, hna]
    simp
  have hyb (y : V) : G.Adj b y ↔ y = y₀ ∨ y = y₁ := by
    rw [← G.mem_neighborFinset, hnb]
    simp
  have hx₀ := (hxa x₀).mpr (Or.inl rfl)
  have hx₁ := (hxa x₁).mpr (Or.inr rfl)
  have hy₀ := (hyb y₀).mpr (Or.inl rfl)
  have hy₁ := (hyb y₁).mpr (Or.inr rfl)
  have xb {x : V} (hx : G.Adj a x) : x ≠ b := fun he => habna (he ▸ hx)
  have ya {y : V} (hy : G.Adj b y) : y ≠ a := fun he => habna (he ▸ hy).symm
  have xy {x y : V} (hx : G.Adj a x) (hy : G.Adj b y) : x ≠ y := by
    intro he
    subst y
    have hax := dist_eq_one_iff_adj.mpr hx
    have hxb := dist_eq_one_iff_adj.mpr hy.symm
    have ht := hc.dist_triangle (u := a) (v := x) (w := b)
    omega
  let l : List V := [x₀,x₁,y₀,y₁,a,b]
  have hnList : l.Nodup := by
    simp [l, List.nodup_cons, hxx, hyy, habne, hx₀.ne.symm, hx₁.ne.symm,
      hy₀.ne.symm, hy₁.ne.symm, xb hx₀, xb hx₁, ya hy₀, ya hy₁,
      xy hx₀ hy₀, xy hx₀ hy₁, xy hx₁ hy₀, xy hx₁ hy₁]
  let f (v : Fin 6) : V := l.get (Fin.cast (by simp [l]) v)
  have hf : Function.Injective f := by
    intro u v h
    exact Fin.ext (congrArg Fin.val (hnList.get_inj_iff.mp h))
  let e : Fin 6 ≃ V := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp [hn]⟩)
  let H := G.comap e.toEmbedding
  let i : H ≃g G := SimpleGraph.Iso.comap e G
  have ea : e 4 = a := rfl
  have eb : e 5 = b := rfl
  have ex₀ : e 0 = x₀ := rfl
  have ex₁ : e 1 = x₁ := rfl
  have ey₀ : e 2 = y₀ := rfl
  have ey₁ : e 3 = y₁ := rfl
  have ha (v : Fin 6) : H.Adj 4 v ↔ v = 0 ∨ v = 1 := by
    change G.Adj (e 4) (e v) ↔ _
    rw [ea, hxa, ←ex₀, ←ex₁]
    simp only [e.injective.eq_iff]
  have hb (v : Fin 6) : H.Adj 5 v ↔ v = 2 ∨ v = 3 := by
    change G.Adj (e 5) (e v) ↔ _
    rw [eb, hyb, ←ey₀, ←ey₁]
    simp only [e.injective.eq_iff]
  exact wellTotalDominated_of_iso i.symm
    (pattern_good H (hc.map i.symm.toHom i.symm.surjective)
      (relabel_premise i.symm hc hi) ha hb)

private theorem labelled_good {n : ℕ} (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hn : 1 < n) (hbound : n ≤ 6) (hi : IntegralPremise G) :
    WellTotalDominated G := by
  have hs : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact small_order_good G hc hi census_two
  · exact small_order_good G hc hi census_three
  · exact small_order_good G hc hi census_four
  · exact small_order_good G hc hi census_five
  · by_cases hd : diameter G ≤ 2
    · exact low_diam_at_six G hc (by simp) hi hd
    · classical
      exact high_diam_at_six G hc (by simp) hi (by omega)

/-- The exact catalogue claim on connected finite simple graphs of order greater than one. -/
theorem conjecture321 (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < Fintype.card V)
    (h : MetricPremise G) : WellTotalDominated G := by
  classical
  have hi := (premise_iff_integral G (by omega)).mp h
  have hbound := order_le_six G hc hn hi
  let f := Fintype.equivFin V
  let H := G.comap f.symm.toEmbedding
  let e : G ≃g H := (SimpleGraph.Iso.comap f.symm G).symm
  exact wellTotalDominated_of_iso e
    (labelled_good H (hc.map e.toHom e.surjective) hn hbound (relabel_premise e hc hi))

#print axioms order_le_six
#print axioms degree_two_at_six
#print axioms census_five
#print axioms census_six
#print axioms conjecture321

end Graffiti321
