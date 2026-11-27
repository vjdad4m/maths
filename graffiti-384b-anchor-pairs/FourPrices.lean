import FourSample
import OuterSeparation
namespace Graffiti384b.AnchorPairs
open Finset SimpleGraph JointRank Simplicial16 TwoEars
open private AnchorPairs.active25 from FourSample
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def base (r : ℕ) := if r=0 then 525996 else if r=1 then 485298
  else if r<4 then 436050 else if r<8 then 327522 else if r<13 then 235582
  else if r<19 then 203758 else 184310
private def price (fee r : ℕ) := max (base r) (160000+fee)
private def refund (r d : ℕ) := if r=0 ∧ d=3 then 26334 else if r+2=d.choose 2 then
    (24:ℕ).choose 7-FiniteRange.badCount 25 7 d else 0
private theorem table : ∀ r : Fin 25,∀ d : Fin 11,3≤d.val → (r.val+2≤d.val.choose 2 ∨ d.val=10) →
    max (FiniteRange.badCount 25 8 d) ((25-d.val).choose 8+160000)≤base r+refund r d := by
  unfold base refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

set_option maxHeartbeats 1500000 in
private theorem budget (X E A : Finset V) (xs : X.card=25) (es : E.card=2) (xe : Disjoint X E)
    (xa : Disjoint X A) (xh : X⊆high G) (two : ∀ v∈E,G.degree v=2)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (none : ∀ u∈X,∀ v∈E,¬G.Adj u v)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (bad : Fintype.card V<gamma G+16) (fee : ℕ) :
    4*1081575+(X.filter (fun v => 0<nbr G v A)).card*160000+
      (X.filter (fun v => 2≤nbr G v A)).card*fee≤∑ r∈range 25,price fee r := by
  classical
  let r := rank X (trianglesAt G)
  let K := X.powersetCard 8
  let bill := fun v => (K.filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => (K.filter (fun s => v∈activated G X s)).card
  let ext := fun v => (K.filter (fun s => v∈TwoEars.extra G X E s)).card
  have ex (w : V) (wm : w∈E) : nbr G w X=0 := card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr
    (fun i h => none i (mem_filter.mp h).1 w wm (mem_filter.mp h).2.symm))
  have free (v : V) (vx : v∈X) : nbr G v E=0 := card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr
    (fun i h => none v vx i (mem_filter.mp h).1 (mem_filter.mp h).2))
  have each (v : V) (vx : v∈X) :
      bill v+(if 0<nbr G v A then 160000 else 0)+(if 2≤nbr G v A then fee else 0)≤
      price fee (r v)+act v+ext v := by
    have rk : r v<25 := by
      have h := mem_image_of_mem (rank X (trianglesAt G)) vx
      rwa [rank_range _ _ inj,xs,mem_range] at h
    let d := min (G.degree v) 10
    have dl : d≤10 := min_le_right ..
    have dg : d≤G.degree v := min_le_left ..
    have lr := rank_lower X (trianglesAt G) inj 2 lo vx
    change 2+r v≤trianglesAt G v at lr
    have cap := Repair.triangles_le_choose G v
    have dh : d=10 ∨ d=G.degree v := by dsimp only [d]; omega
    have dc : r v+2≤d.choose 2 ∨ d=10 := dh.elim (fun h => Or.inr h)
      (fun h => Or.inl (by rw [h,Nat.add_comm]; exact lr.trans cap))
    have tab := table ⟨r v,rk⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp (xh vx)).2 (by decide)) dc
    dsimp only at tab
    have saved : refund (r v) d≤act v+ext v := by
      unfold refund
      split_ifs with first eq
      · obtain ⟨zero,three⟩ := first
        have dd : G.degree v=3 := by rcases dh with h|h <;> omega
        rw [dd,show (3:ℕ).choose 2=3 by decide] at cap
        by_cases sc : trianglesAt G v=2
        · exact (cubic25 G X E xs vx sc dd (free v vx)).trans (Nat.le_add_left ..)
        · have sat : saturated G v := by unfold saturated; rw [dd,show (3:ℕ).choose 2=3 by decide]; omega
          have b := AnchorPairs.active25 G X xs vx sat 7 3 (by omega) (by decide)
          exact (show 26334≤(24:ℕ).choose 7-FiniteRange.badCount 25 7 3 by simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]; decide).trans (b.trans (Nat.le_add_right ..))
      · have dd : d=G.degree v := dh.resolve_left (fun ten => by
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega)
        have sat : saturated G v := by unfold saturated; rw [←dd] at cap ⊢; omega
        exact (AnchorPairs.active25 G X xs vx sat 7 d dg (by omega)).trans (Nat.le_add_right ..)
      · exact Nat.zero_le _
    by_cases dbl : 2≤nbr G v A
    · have zero : bill v=0 := by
        apply card_eq_zero.mpr; apply eq_empty_iff_forall_not_mem.mpr
        intro s sm; have lw := (mem_filter.mp (mem_filter.mp sm).2).2
        have sub : A⊆Xᶜ∪s := fun w wa => mem_union_left _ (mem_compl.mpr (fun wx => disjoint_left.mp xa wx wa))
        exact (not_lt_of_ge (dbl.trans (card_le_card (filter_subset_filter _ sub)))) lw
      rw [zero,if_pos dbl,if_pos (by omega),Nat.zero_add]
      exact (le_max_right ..).trans (by change price fee (r v)≤_; omega)
    · rw [if_neg dbl,Nat.add_zero]
      have left := le_max_left (base (r v)) (160000+fee)
      change base (r v)≤price fee (r v) at left
      by_cases hit : 0<nbr G v A
      · obtain ⟨w,wm⟩ := card_pos.mp hit
        obtain ⟨wa,vw⟩ := mem_filter.mp wm
        have b := EarCredit.credited G vx (fun wx => disjoint_left.mp xa wx wa) vw 8
        rw [xs] at b
        have h := Nat.add_le_add_right (b.trans (Nat.choose_le_choose 8 (show 25-G.degree v≤25-d by omega))) 160000
        change bill v+160000≤_ at h
        have z := (le_max_right ..).trans tab
        rw [if_pos hit]; omega
      · have b := FiniteRange.count_bad G X 8 d v vx dg (by omega)
        rw [xs] at b
        have h := b.trans ((le_max_left ..).trans tab)
        change bill v≤_ at h
        rw [if_neg hit,Nat.add_zero]; omega
  have sum := sum_le_sum (s:=X) each
  have pay1 : (∑ v∈X,if 0<nbr G v A then 160000 else 0)=(X.filter (fun v => 0<nbr G v A)).card*160000 := by rw [←sum_filter]; simp
  have pay2 : (∑ v∈X,if 2≤nbr G v A then fee else 0)=(X.filter (fun v => 2≤nbr G v A)).card*fee := by rw [←sum_filter]; simp
  have total := sum_by_rank X (trianglesAt G) inj (price fee)
  rw [xs] at total; change (∑ v∈X,price fee (r v))=_ at total
  simp only [sum_add_distrib,pay1,pay2,total] at sum
  have mass := AnchorPairs.extra_mass G X E xs xe ind two xh inj bad
  have gains : (∑ v∈E,(25-nbr G v X).choose (8-nbr G v X))=2*1081575 := by
    rw [sum_congr rfl (fun v vm => show (25-nbr G v X).choose (8-nbr G v X)=1081575 by rw [ex v vm]; decide),
      sum_const,es,smul_eq_mul]
  rw [gains,show (25:ℕ).choose 8=1081575 by rw [Nat.choose_eq_fast_choose]; decide] at mass
  change 2*1081575+2*1081575+(∑ v∈X,act v)+(∑ v∈X,ext v)≤∑ v∈X,bill v at mass
  omega

/-- Necessary incidence bounds when four high vertices retain all supports of
two independent ear omissions. Distinct vertices are counted in both columns. -/
theorem incidence (X E A : Finset V) (xs : X.card=25) (es : E.card=2) (xe : Disjoint X E)
    (xa : Disjoint X A) (xh : X⊆high G) (two : ∀ v∈E,G.degree v=2)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (none : ∀ u∈X,∀ v∈E,¬G.Adj u v)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (bad : Fintype.card V<gamma G+16) :
    let m := (X.filter (fun v => 0<nbr G v A)).card
    let b := (X.filter (fun v => 2≤nbr G v A)).card
    m≤14 ∧ (m=14 → b≤5) ∧ (m=13 → b≤9) := by
  have h := budget G X E A xs es xe xa xh two ind none inj lo bad
  have cap1 := h 24310
  have cap2 := h 43758
  rw [show (∑ r∈range 25,price 24310 r)=6699800 by decide] at cap1
  rw [show (∑ r∈range 25,price 43758 r)=6816488 by decide] at cap2
  dsimp only; omega

end Graffiti384b.AnchorPairs
#print axioms Graffiti384b.AnchorPairs.incidence
