import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace KelmansAffine
open Finset

abbrev Point := Fin 9
abbrev Line := Fin 12

/-- Points encode (x,y) as 3x+y. Lines encode slope group and intercept
as 3s+b; slopes 0,1,2 are affine, group 3 is vertical. -/
def Incident (p : Point) (l : Line) : Prop :=
  if l.val / 3 = 3 then p.val / 3 = l.val % 3
  else p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3

instance (p : Point) (l : Line) : Decidable (Incident p l) := by
  unfold Incident
  split <;> infer_instance

def onLine (l : Line) : Finset Point := Finset.univ.filter (fun p => Incident p l)
def throughPoint (p : Point) : Finset Line := Finset.univ.filter (Incident p)

@[simp] theorem mem_onLine {p : Point} {l : Line} : p ∈ onLine l ↔ Incident p l := by
  simp [onLine]

@[simp] theorem mem_throughPoint {p : Point} {l : Line} : l ∈ throughPoint p ↔ Incident p l := by
  simp [throughPoint]

theorem control_degree : ∀ l : Line, (onLine l).card = 3 := by decide
theorem cell_degree : ∀ p : Point, (throughPoint p).card = 4 := by decide

def shareLine (p q : Point) : Finset Line := (throughPoint p) ∩ (throughPoint q)

/-- The small incidence table is checked by kernel reduction, not native code. -/
theorem distinct_points_share_count :
    ∀ p q : Point, p ≠ q → (shareLine p q).card = 1 := by decide

theorem distinct_points_unique_line :
    ∀ p q : Point, p ≠ q → ∃! l : Line, Incident p l ∧ Incident q l := by
  intro p q h
  obtain ⟨l,he⟩ := Finset.card_eq_one.mp (distinct_points_share_count p q h)
  have hm (l' : Line) : (Incident p l' ∧ Incident q l') ↔ l'=l := by
    rw [← mem_throughPoint,← mem_throughPoint,← Finset.mem_inter]
    change l' ∈ shareLine p q ↔ _
    simp [he]
  exact ⟨l,(hm l).mpr rfl,fun l' h' => (hm l').mp h'⟩

/-- At least two points of each line survive any deletion of at most one cell. -/
theorem residual_control_degree (S : Finset Point) (hs : 8 ≤ S.card) (l : Line) :
    2 ≤ (S ∩ onLine l).card := by
  have eq := Finset.card_union_add_card_inter S (onLine l)
  have hU := Finset.card_le_univ (s := S ∪ onLine l)
  rw [show Fintype.card Point = 9 by decide] at hU
  rw [control_degree] at eq
  omega

def redPoints (S : Finset Point) (color : Point → Bool) : Finset Point :=
  S.filter fun p => color p = true

def bluePoints (S : Finset Point) (color : Point → Bool) : Finset Point :=
  S.filter fun p => color p = false

def redOn (S : Finset Point) (color : Point → Bool) (l : Line) : Finset Point :=
  redPoints S color ∩ onLine l

def blueOn (S : Finset Point) (color : Point → Bool) (l : Line) : Finset Point :=
  bluePoints S color ∩ onLine l

def mixedLines (S : Finset Point) (color : Point → Bool) : Finset Line :=
  Finset.univ.filter fun l => (redOn S color l).Nonempty ∧ (blueOn S color l).Nonempty

private theorem red_blue_disjoint (S : Finset Point) (color : Point → Bool) :
    Disjoint (redPoints S color) (bluePoints S color) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  have e := (Finset.mem_filter.mp hp).2
  have e' := (Finset.mem_filter.mp hp').2
  cases e.symm.trans e'

theorem red_blue_card (S : Finset Point) (color : Point → Bool) :
    (redPoints S color).card + (bluePoints S color).card = S.card := by
  rw [← Finset.card_union_of_disjoint (red_blue_disjoint S color)]
  congr 1
  ext p
  cases e : color p <;> simp [redPoints,bluePoints,e]

private theorem opposite_pairs_ge_seven (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hs : 8 ≤ a+b) : 7 ≤ a*b := by
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      rw [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega

private theorem onLine_split_le_three (S : Finset Point) (color : Point → Bool) (l : Line) :
    (redOn S color l).card + (blueOn S color l).card ≤ 3 := by
  have hd : Disjoint (redOn S color l) (blueOn S color l) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (red_blue_disjoint S color)
  rw [← Finset.card_union_of_disjoint hd,← control_degree l]
  exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)

/-- Pairs of opposite colors belong to their unique mixed line. Each line
contains at most two such pairs, even if one point is absent. -/
theorem card_mixed_ge_four (S : Finset Point) (color : Point → Bool) (hs : 8 ≤ S.card)
    (hr : (redPoints S color).Nonempty) (hb : (bluePoints S color).Nonempty) :
    4 ≤ (mixedLines S color).card := by
  classical
  let pairs (l : Line) := (redOn S color l) ×ˢ (blueOn S color l)
  let M := mixedLines S color
  have cover : redPoints S color ×ˢ bluePoints S color ⊆ M.biUnion pairs := by
    rintro ⟨p,q⟩ hpq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    have ne : p ≠ q := by
      intro e; subst q
      exact Finset.disjoint_left.mp (red_blue_disjoint S color) hp hq
    obtain ⟨l,⟨hpl,hql⟩,_⟩ := distinct_points_unique_line p q ne
    have hl : p ∈ redOn S color l := Finset.mem_inter.mpr ⟨hp,mem_onLine.mpr hpl⟩
    have hl' : q ∈ blueOn S color l := Finset.mem_inter.mpr ⟨hq,mem_onLine.mpr hql⟩
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨p,hl⟩,⟨q,hl'⟩⟩,
      Finset.mem_product.mpr ⟨hl,hl'⟩⟩
  have localcap (l : Line) (hl : l ∈ M) : (pairs l).card ≤ 2 := by
    obtain ⟨hr,hb⟩ := (Finset.mem_filter.mp hl).2
    have hr' := Finset.card_pos.mpr hr
    have hb' := Finset.card_pos.mpr hb
    have hs' := onLine_split_le_three S color l
    have e : (redOn S color l).card = 1 ∨ (blueOn S color l).card = 1 := by omega
    change ((redOn S color l) ×ˢ (blueOn S color l)).card ≤ 2
    rw [Finset.card_product]
    rcases e with e|e
    · rw [e,Nat.one_mul]
      omega
    · rw [e,Nat.mul_one]
      omega
  have hup := (Finset.card_le_card cover).trans
    (Finset.card_biUnion_le_card_mul M pairs 2 localcap)
  rw [Finset.card_product] at hup
  change _ ≤ (mixedLines S color).card * 2 at hup
  have htot := red_blue_card S color
  have hlow := opposite_pairs_ge_seven _ _ (Finset.card_pos.mpr hr) (Finset.card_pos.mpr hb)
    (by omega)
  omega

#print axioms cell_degree
#print axioms control_degree
#print axioms distinct_points_unique_line
#print axioms residual_control_degree
#print axioms card_mixed_ge_four
end KelmansAffine
