import SimplicialRanks
namespace Graffiti384b.Reserved16
open Finset SimpleGraph JointRank Simplicial16
open private Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
open private Repair.nbr_mono Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def loss (d j : ℕ) := if j=0 then FiniteRange.badCount 27 10 d else if j=1 then (27-d).choose 10 else 0
private theorem fiber {W A : Finset V} (ws : W.card=27) (aw : Disjoint A W)
    {v : V} (vm : v∈W) :
    ((W.powersetCard 10).filter (fun k => v∈FiniteRange.bad G W k)).card≤
    loss (min (G.degree v) 10) (nbr G v A) := by
  classical
  let d := min (G.degree v) 10
  have dr : d≤G.degree v := min_le_left ..
  have ds : d≤10 := min_le_right ..
  have asub : A⊆Wᶜ := fun z zm => mem_compl.mpr (fun wm => disjoint_left.mp aw zm wm)
  by_cases none : nbr G v A=0
  · have cap := FiniteRange.count_bad G W 10 d v vm dr (by rw [ws]; omega)
    rw [ws] at cap; simpa [loss,none,d] using cap
  by_cases one : nbr G v A=1
  · obtain ⟨z,zm⟩ := card_pos.mp (show 0<nbr G v A by omega)
    obtain ⟨za,vz⟩ := mem_filter.mp zm
    have cap := EarCredit.credited G vm (mem_compl.mp (asub za)) vz 10
    rw [ws] at cap
    simpa [loss,one,d] using cap.trans (Nat.choose_le_choose 10 (Nat.sub_le_sub_left dr 27))
  have empty : ((W.powersetCard 10).filter (fun k => v∈FiniteRange.bad G W k))=∅ := eq_empty_of_forall_not_mem (by
    intro k km
    have low := (mem_filter.mp (mem_filter.mp km).2).2
    have up := Repair.nbr_mono G v (asub.trans (subset_union_left (s₂:=k)))
    omega)
  simp [loss,empty,none,one]
private def mark (single : Bool) (r : ℕ) := if single then (if r<9 then r+2 else r+3)
  else if r<13 then r+2 else r+4
private theorem mark_lower (r s p q : ℕ) (ps : p≠s) (qs : q≠s) (pq : p≠q)
    (mode : p≤11 ∨ q≤11 ∨ (p≤16 ∧ q≤16))
    (rb : 2+r≤s-(if p<s then 1 else 0)-(if q<s then 1 else 0)) :
    mark (decide (p≤11 ∨ q≤11)) r≤s := by
  by_cases m : p≤11 ∨ q≤11
  · simp only [m,decide_true,mark,ite_true] 
    split_ifs <;> split_ifs at rb <;> omega
  · simp only [m,decide_false,mark,Bool.false_eq_true,ite_false]
    split_ifs <;> split_ifs at rb <;> omega

private theorem mark_limit : ∀ m : Bool,∀ r : Fin 27,mark m r<45 := by decide

private def row (s : ℕ) := if s=2 then 3595636 else if s=3 then 2759218 else if s<6 then 2636326
  else if s<10 then 1822366 else if s<15 then 1192516 else if s<21 then 739024 else 646646
private def refund (s d : ℕ) := if s=d.choose 2 then (26:ℕ).choose 9-FiniteRange.badCount 27 9 d else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem table :
    (∀ m : Bool,∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
      (mark m r≤d.val.choose 2 ∨ d.val=10) → 3≤d.val →
      loss d (a.val+b.val)+554268*a.val+46189*b.val≤row (mark m r)+refund (mark m r) d) ∧
    (∀ m : Bool,(∑ i∈range 27,row (mark m i))≤34302106) := by
  unfold mark loss row refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

/-- Each paid incidence to either other ear is counted individually, including
when an exterior vertex is adjacent to both. The rank pays for both charges. -/
theorem reserved_rank (X A F : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (p q : ℕ) (p2 : 2≤p) (q2 : 2≤q) (pq : p≠q)
    (outside : ∀ v∈X,trianglesAt G v≠p ∧ trianglesAt G v≠q)
    (mode : p≤11 ∨ q≤11 ∨ (p≤16 ∧ q≤16)) :
    (∑ v∈X,((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      554268*(∑ v∈X,nbr G v A)+46189*(∑ v∈X,nbr G v F)≤34302106+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈activated G X s)).card) := by
  classical
  let bill := fun v => ((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 10).filter (fun s => v∈activated G X s)).card
  let f := fun v => trianglesAt G v-(if p<trianglesAt G v then 1 else 0)-(if q<trianglesAt G v then 1 else 0)
  have fi : Set.InjOn f (X:Set V) := by
    intro u um v vm eq
    obtain ⟨up,uq⟩ := outside u um
    obtain ⟨vp,vq⟩ := outside v vm
    apply inj um vm
    dsimp [f] at eq; split_ifs at eq <;> omega
  have floor (v : V) (vm : v∈X) : 2≤f v := by
    have hv := lo v vm
    obtain ⟨vp,vq⟩ := outside v vm
    dsimp [f]; split_ifs <;> omega
  let single := decide (p≤11 ∨ q≤11)
  let r := rank X f
  have each (v : V) (vm : v∈X) : bill v+554268*nbr G v A+46189*nbr G v F≤row (mark single (r v))+act v := by
    have rk := mem_image_of_mem (rank X f) vm
    rw [rank_range X _ fi,sz,mem_range] at rk
    have idx := rank_lower X f fi 2 floor vm
    change 2+r v≤f v at idx
    obtain ⟨vp,vq⟩ := outside v vm
    have lr := mark_lower (r v) (trianglesAt G v) p q vp.symm vq.symm pq mode idx
    change mark single (r v)≤trianglesAt G v at lr
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : mark single (r v)≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have b := fiber G sz sep vm
    rw [Repair.nbr_add G v af] at b
    have cf' := card_le_card (filter_subset (G.Adj v) F)
    have z := table.1 single ⟨r v,rk⟩ ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ dc (le_min (mem_filter.mp (hx vm)).2 (by decide))
    have rb : refund (mark single (r v)) d≤act v := by
      unfold refund; split_ifs with eq
      · have lt : d<10 := by
          by_contra! ge
          have ten : d=10 := by omega
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
          exact (Nat.ne_of_lt (mark_limit single ⟨r v,rk⟩)) eq
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated
          apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq]; exact lr
        exact Simplicial16.active_fiber G X sz vm sat 9 d (min_le_left ..) (by omega)
      · exact Nat.zero_le _
    exact ((Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z).trans (Nat.add_le_add_left rb _)
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rw [sum_by_rank X f fi (fun j => row (mark single j)),sz] at sum
  have last := table.2 single
  exact sum.trans (Nat.add_le_add_right last _)

end Graffiti384b.Reserved16
#print axioms Graffiti384b.Reserved16.reserved_rank
