import FourRingCutAux

open Finset
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every proper split, including a singleton, has at least three edges. -/
def MinBoundaryThree (G : SimpleGraph V) : Prop :=
  ∀ c : V→Bool, (∃x,c x=true) → (∃x,c x=false) → 3≤(boundary G c).card

/-- Four nonempty zones mean a genuinely crossing pair of splits. -/
def Crosses {V : Type*} (c d : V→Bool) : Prop :=
  ∀ a b : Bool, ∃ x,c x=a ∧ d x=b

private def both {V : Type*} (c d : V→Bool) (x : V) : Bool := c x && d x
private def either {V : Type*} (c d : V→Bool) (x : V) : Bool := c x || d x
private def neg {V : Type*} (c : V→Bool) (x : V) : Bool := !(c x)
private def bit (a b : Bool) : ℕ := if a && b then 1 else 0

private def between (G : SimpleGraph V) (c d : V→Bool) : ℕ := by
  classical
  exact (univ.filter (fun e : V×V=>c e.1=true ∧ d e.2=true ∧ G.Adj e.1 e.2)).card

private def crossingValue (G : SimpleGraph V) (c d : V→Bool) (e : V×V) : ℕ := by
  classical
  exact if G.Adj e.1 e.2 then bit (c e.1) (d e.2) else 0

omit [DecidableEq V] in
private theorem between_sum (G : SimpleGraph V) (c d : V→Bool) :
    between G c d=∑ e,crossingValue G c d e := by
  classical
  let p : V×V→Prop := fun e=>c e.1=true ∧ d e.2=true ∧ G.Adj e.1 e.2
  change (univ.filter p).card=_
  calc
    (univ.filter p).card = ∑ e∈univ.filter p,(1:ℕ) := by simp
    _ = ∑ e, if p e then (1:ℕ) else 0 := by rw [sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro e _
      by_cases ed : G.Adj e.1 e.2
      · by_cases hc : c e.1=true
        · by_cases hd : d e.2=true
          · simp [p,crossingValue,bit,ed,hc,hd]
          · simp [p,crossingValue,bit,ed,hc,Bool.eq_false_iff.mpr hd]
        · simp [p,crossingValue,bit,ed,Bool.eq_false_iff.mpr hc]
      · simp [p,crossingValue,ed]

omit [DecidableEq V] in
private theorem swap_between (G : SimpleGraph V) (c d : V→Bool) :
    between G c d=between G d c := by
  classical
  unfold between
  apply card_bij (fun e _=>e.swap)
  · intro e he
    obtain ⟨c0,d0,e0⟩ := (mem_filter.mp he).2
    exact mem_filter.mpr ⟨mem_univ _,d0,c0,G.symm e0⟩
  · intro a _ b _ e
    exact Prod.swap_injective e
  · intro e he
    obtain ⟨d0,c0,e0⟩ := (mem_filter.mp he).2
    exact ⟨e.swap,mem_filter.mpr ⟨mem_univ _,c0,d0,G.symm e0⟩,Prod.swap_swap _⟩

omit [DecidableEq V] in
private theorem bw_delta (G : SimpleGraph V) (c : V→Bool) :
    between G c (neg c)=(boundary G c).card := by
  classical
  unfold between boundary
  congr 1
  ext e
  cases h : c e.2 <;> simp [neg,h]

private theorem table_uncross : ∀ a b c d : Bool,
    bit a (!c)+bit b (!d) =
      bit (a&&b) (!(c&&d)) + bit (a||b) (!(c||d)) +
      bit (a && !b) ((!c)&&d) + bit ((!a)&&b) (c && !d) := by decide

private theorem table_A : ∀ a b c d : Bool,
    bit (a&&b) (!(c&&d)) =
      bit (a&&b) (c && !d) + bit (a&&b) ((!c)&&d) + bit (a&&b) ((!c)&&(!d)) := by decide

private theorem table_B : ∀ a b c d : Bool,
    bit (a && !b) (!(c && !d)) =
      bit (a && !b) (c&&d)+bit (a && !b) ((!c)&&d)+bit (a && !b) ((!c)&&(!d)) := by decide

private theorem table_S : ∀ a b c d : Bool,
    bit a (!c) =
      bit (a&&b) ((!c)&&d)+bit (a&&b) ((!c)&&(!d)) +
      bit (a && !b) ((!c)&&d)+bit (a && !b) ((!c)&&(!d)) := by decide

omit [DecidableEq V] in
private theorem count_bad_diag (G : SimpleGraph V) (c d : V→Bool) :
    (boundary G c).card+(boundary G d).card=
      (boundary G (both c d)).card+(boundary G (either c d)).card +
      between G (both c (neg d)) (both (neg c) d) +
      between G (both (neg c) d) (both c (neg d)) := by
  classical
  simp only [←bw_delta,between_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases h : G.Adj e.1 e.2
  · simpa only [crossingValue,if_pos h,both,either,neg] using
      table_uncross (c e.1) (d e.1) (c e.2) (d e.2)
  · simp [crossingValue,h]

omit [DecidableEq V] in
private theorem count_from_A (G : SimpleGraph V) (c d : V→Bool) :
    let A := both c d
    let B := both c (neg d)
    let C := both (neg c) d
    let D := both (neg c) (neg d)
    (boundary G A).card=between G A B+between G A C+between G A D := by
  classical
  simp only [←bw_delta,between_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases h : G.Adj e.1 e.2
  · simpa only [crossingValue,if_pos h,both,neg] using table_A (c e.1) (d e.1) (c e.2) (d e.2)
  · simp [crossingValue,h]

omit [DecidableEq V] in
private theorem count_from_B (G : SimpleGraph V) (c d : V→Bool) :
    let A := both c d
    let B := both c (neg d)
    let C := both (neg c) d
    let D := both (neg c) (neg d)
    (boundary G B).card=between G B A+between G B C+between G B D := by
  classical
  simp only [←bw_delta,between_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases h : G.Adj e.1 e.2
  · simpa only [crossingValue,if_pos h,both,neg] using table_B (c e.1) (d e.1) (c e.2) (d e.2)
  · simp [crossingValue,h]

omit [DecidableEq V] in
private theorem count_from_S (G : SimpleGraph V) (c d : V→Bool) :
    let A := both c d
    let B := both c (neg d)
    let C := both (neg c) d
    let D := both (neg c) (neg d)
    (boundary G c).card=between G A C+between G A D+between G B C+between G B D := by
  classical
  simp only [←bw_delta,between_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases h : G.Adj e.1 e.2
  · simpa only [crossingValue,if_pos h,both,neg] using table_S (c e.1) (d e.1) (c e.2) (d e.2)
  · simp [crossingValue,h]

omit [DecidableEq V] in
private theorem diagonals_vanish (G : SimpleGraph V) (min : MinBoundaryThree G)
    (c d : V→Bool) (hc : (boundary G c).card=3) (hd : (boundary G d).card=3)
    (cross : Crosses c d) :
    (boundary G (both c d)).card=3 ∧ between G (both c (neg d)) (both (neg c) d)=0 := by
  obtain ⟨a,ca,da⟩ := cross true true
  obtain ⟨b,cb,db⟩ := cross false false
  have t : 3≤(boundary G (both c d)).card :=
    min _ ⟨a,by simp [both,ca,da]⟩ ⟨b,by simp [both,cb,db]⟩
  have u : 3≤(boundary G (either c d)).card :=
    min _ ⟨a,by simp [either,ca,da]⟩ ⟨b,by simp [either,cb,db]⟩
  have tally := count_bad_diag G c d
  omega

/-- Two proper minimum cuts of odd size three cannot cross. This
lemma uses only the global lower bound of three, not cubicity. -/
theorem no_crossing_minimum_three_cuts (G : SimpleGraph V) (min : MinBoundaryThree G)
    (c d : V→Bool) (hc : (boundary G c).card=3) (hd : (boundary G d).card=3) :
    ¬Crosses c d := by
  intro cross
  have hd' : (boundary G (neg d)).card=3 := (boundary_flip_card G d).trans hd
  have cc' : Crosses c (neg d) := by
    intro a b
    obtain ⟨v,av,bv⟩ := cross a (!b)
    exact ⟨v,av,by simp [neg,bv]⟩
  have inv : neg (neg d)=d := funext (fun x=>by simp [neg])
  obtain ⟨aa,bc⟩ := diagonals_vanish G min c d hc hd cross
  obtain ⟨bb,ad⟩ := diagonals_vanish G min c (neg d) hc hd' cc'
  rw [inv] at ad
  have equality := swap_between G (both c d) (both c (neg d))
  have a := count_from_A G c d
  have b := count_from_B G c d
  have s := count_from_S G c d
  dsimp only at a b s
  omega

#print axioms no_crossing_minimum_three_cuts
end
end KelmansCactus.AtomicBridge.OddUncross
