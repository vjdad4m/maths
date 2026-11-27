import RootMass
import EarTriangle
namespace Graffiti384b.TwoEars
open Finset SimpleGraph JointRank Simplicial16
open private TwoEars.active28 from RootMass
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def row (r : ℕ) (hit : Bool) := if r=0 then (if hit then 3375825 else 7298337)
  else if r<4 then (if hit then 2496144 else 5928342)
  else if r<8 then (if hit then 1352078 else 3938662)
  else if r<13 then (if hit then 705432 else 2469012)
  else if r<19 then (if hit then 352716 else 1461252)
  else if r<25 then (if hit then 167960 else 814606)
  else (if hit then 75582 else 425646)
private def fee (k : ℕ) := if k<5 then 350064 else 646646
private def price (k r : ℕ) := max (row r false) (row r true+fee k)
private def refund (r d : ℕ) := if r=0 ∧ d=3 then 1081575 else if r+2=d.choose 2 then
    (27:ℕ).choose 10-FiniteRange.badCount 28 10 d else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
private theorem tables :
    (∀ r : Fin 29,∀ d : Fin 11,3≤d.val → (r.val+2≤d.val.choose 2 ∨ d.val=10) →
      (d.val=10 ∨ d.val+r.val+1≤29+2*(d.val.choose 2-(r.val+2))) →
      FiniteRange.badCount 28 11 d≤row r false+refund r d ∧
      (28-d.val).choose 11≤row r true+refund r d) ∧
    (∀ k : Fin 10,∀ p : Fin 29,(k.val=9 ∨ p.val≤k.val.choose 2) →
      (∑ r∈range 29,price k r)+36537≤3*21474180+price k p+k.val*fee k) := by
  unfold row refund price fee row FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]; decide

set_option maxHeartbeats 2000000 in
/-- Pin a high vertex and omit any single degree-two vertex whose entire
neighborhood is outside the resulting pool. -/
theorem pinned (t : (types G).card=31) (hs : (high G).card=29)
    (es : (LowSample.twos G).card=2) {c e : V} (ch : c∈high G)
    (de : G.degree e=2) (away : ∀ w∈(high G).erase c,¬G.Adj e w) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨inj,lo,_,_⟩ := Repair.maximal_diversity G (by omega)
  let X := (high G).erase c
  let E : Finset V := {e}
  have xs : X.card=28 := by dsimp [X]; rw [card_erase_of_mem ch,hs]
  have xh : X⊆high G := erase_subset ..
  have cx : c∉X := not_mem_erase _ _
  have xe : Disjoint X E := disjoint_left.mpr (fun i ix em => by
    have h := (mem_filter.mp (xh ix)).2; rw [mem_singleton.mp em,de] at h; omega)
  have free (i : V) (ix : i∈X) : nbr G i E=0 := by simp [E,nbr,filter_singleton,show ¬G.Adj i e from fun h => away i ix h.symm]
  have ec : nbr G e X=0 := by
    apply card_eq_zero.mpr; exact eq_empty_iff_forall_not_mem.mpr (fun i h => away i (mem_filter.mp h).1 (mem_filter.mp h).2)
  let m := nbr G c X
  let k := min m 9
  have ks : k<10 := by dsimp [k]; omega
  let r := rank (high G) (trianglesAt G)
  have rk {v : V} (vh : v∈high G) : r v<29 := by
    have mm := mem_image_of_mem (rank (high G) (trianglesAt G)) vh
    rwa [rank_range _ _ inj,hs,mem_range] at mm
  have lr {v : V} (vh : v∈high G) : 2+r v≤trianglesAt G v := rank_lower _ _ inj 2 lo vh
  have fit {v : V} (vh : v∈high G) :
      G.degree v+r v+1≤29+2*((G.degree v).choose 2-(r v+2)) := by
    let L := (high G).filter (fun w => trianglesAt G w<trianglesAt G v)
    let U := (G.neighborFinset v).filter (fun w => trianglesAt G v≤trianglesAt G w)
    have inc : insert v L⊆high G := insert_subset vh (filter_subset ..)
    have off : v∉L := fun h => lt_irrefl _ (mem_filter.mp h).2
    have sub : U⊆high G\insert v L := by
      intro w wm; obtain ⟨wn,sw⟩ := mem_filter.mp wm
      have wh : w∈high G := by
        by_contra h
        have lw : G.degree w≤2 := Nat.le_of_not_gt (fun h' => h (mem_filter.mpr ⟨mem_univ _,h'⟩))
        have limit := (Repair.triangles_le_choose G w).trans (Nat.choose_le_choose 2 lw)
        have vv := lo v vh
        rw [show (2:ℕ).choose 2=1 by decide] at limit; omega
      exact mem_sdiff.mpr ⟨wh,fun h => (mem_insert.mp h).elim (fun eq => G.not_mem_neighborFinset_self _ (eq ▸ wn)) (fun sm => (not_lt_of_ge sw) (mem_filter.mp sm).2)⟩
    have count := card_le_card sub
    rw [card_sdiff inc,hs,card_insert_of_not_mem off] at count
    have lc : L.card=r v := rfl
    have dense := JointDense.dense_neighbor_bound G v
    change G.degree v≤U.card+_ at dense
    have lower := lr vh
    have small := rk vh
    rw [lc] at count; omega
  have rootScore := Shared.score_cap G c X m (le_refl _) (fun i _ ci _ _ ih _ => mem_erase.mpr ⟨ci.ne.symm,ih⟩)
  rw [es] at rootScore
  have mode : k=9 ∨ r c≤k.choose 2 := by
    by_cases h : 9≤m
    · exact Or.inl (min_eq_right h)
    · have cc := lr ch
      rw [show k=m from min_eq_left (by omega)]; omega
  let bill := fun v => ((X.powersetCard 11).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 11).filter (fun s => v∈activated G X s)).card
  let ext := fun v => ((X.powersetCard 11).filter (fun s => v∈extra G X E s)).card
  have each (v : V) (vx : v∈X) :
      bill v+(if G.Adj c v then fee k else 0)≤price k (r v)+act v+ext v := by
    have vh := xh vx
    let d := min (G.degree v) 10
    have dl : d≤10 := min_le_right ..
    have dg : d≤G.degree v := min_le_left ..
    have dlr := lr vh
    have cap := Repair.triangles_le_choose G v
    have dh : d=10 ∨ d=G.degree v := by dsimp only [d]; omega
    have dc : r v+2≤d.choose 2 ∨ d=10 := dh.elim (fun h => Or.inr h) (fun h => Or.inl (by rw [h,Nat.add_comm]; exact dlr.trans cap))
    have db := tables.1 ⟨r v,rk vh⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp vh).2 (by decide)) dc
      (dh.imp_right (fun eq => eq ▸ fit vh))
    dsimp only at db
    have saved : refund (r v) d≤act v+ext v := by
      unfold refund
      split_ifs with first eq
      · obtain ⟨zero,three⟩ := first
        have dd : G.degree v=3 := by rcases dh with h|h <;> omega
        rw [dd,show (3:ℕ).choose 2=3 by decide] at cap
        by_cases two : trianglesAt G v=2
        · exact (extra_fiber G X E xs vx two dd (free v vx)).trans (Nat.le_add_left ..)
        · have sat : saturated G v := by unfold saturated; rw [dd,show (3:ℕ).choose 2=3 by decide]; omega
          have b := TwoEars.active28 G X xs vx sat 10 3 (by omega) (by decide)
          exact (show 1081575≤(27:ℕ).choose 10-FiniteRange.badCount 28 10 3 by simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]; decide).trans (b.trans (Nat.le_add_right ..))
      · have dd : d=G.degree v := dh.resolve_left (fun ten => by
          have sm := rk vh; rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega)
        have sat : saturated G v := by unfold saturated; rw [←dd] at cap ⊢; omega
        exact (TwoEars.active28 G X xs vx sat 10 d dg (by omega)).trans (Nat.le_add_right ..)
      · exact Nat.zero_le _
    by_cases edge : G.Adj c v
    · have b := EarCredit.credited G vx cx edge.symm 11
      rw [xs] at b
      have h := (b.trans (Nat.choose_le_choose 11 (show 28-G.degree v≤28-d by omega))).trans db.2
      change bill v≤_ at h
      rw [if_pos edge]; have := le_max_right (row (r v) false) (row (r v) true+fee k)
      change _≤max _ _+_+_; omega
    · have b := FiniteRange.count_bad G X 11 d v vx dg (by omega)
      rw [xs] at b
      have h := b.trans db.1
      change bill v≤_ at h
      rw [if_neg edge,Nat.add_zero]; have := le_max_left (row (r v) false) (row (r v) true+fee k)
      change _≤max _ _+_+_; omega
  have total := sum_by_rank (high G) (trianglesAt G) inj (price k)
  rw [hs] at total
  have split := sum_erase_add (high G) (fun v => price k (r v)) ch
  change (∑ v∈X,price k (r v))+price k (r c)=(∑ v∈high G,price k (r v)) at split
  have num := tables.2 ⟨k,ks⟩ ⟨r c,rk ch⟩ mode
  dsimp only at num
  have sum := sum_le_sum (s:=X) each
  have paid : (∑ v∈X,if G.Adj c v then fee k else 0)=m*fee k := by rw [←sum_filter]; simp [m,nbr]
  simp only [sum_add_distrib,paid] at sum
  have km := Nat.mul_le_mul_right (fee k) (min_le_left m 9)
  change k*fee k≤m*fee k at km
  rw [bound,t] at bad
  have mass := extra_mass G X E xs xe (fun i im j jm => by rw [mem_singleton.mp im,mem_singleton.mp jm]; exact G.loopless e)
    (fun i im => mem_singleton.mp im ▸ de) xh (inj.mono (show (X:Set V)⊆high G from xh)) (by omega)
  simp only [E,sum_singleton,ec,Nat.sub_zero,show (28:ℕ).choose 11=21474180 by rw [Nat.choose_eq_fast_choose]; decide] at mass
  change 2*21474180+21474180+(∑ v∈X,act v)+(∑ v∈X,ext v)≤∑ v∈X,bill v at mass
  change (∑ v∈high G,price k (r v))=_ at total
  omega
end Graffiti384b.TwoEars
#print axioms Graffiti384b.TwoEars.pinned
