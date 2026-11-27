import IndependentThirteen
namespace Graffiti384b.Twelve
open Finset SimpleGraph JointRank Simplicial16
open private Reserved16.fiber Reserved16.loss from ReservedRanks
open private Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private def row (r : ℕ) := #[3595636,2759218,2636326,2636326,1822366,1822366,1822366,1822366,1192516,1192516,1192516,1192516,1192516,739024,739024,739024,739024,739024,739024,646646,646646,646646,646646,646646,646646,646646,646646][r]!
private def refund (r d : ℕ) := if r+2=d.choose 2 then (26:ℕ).choose 9-FiniteRange.badCount 27 9 d else 0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
private theorem table : (∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
    (r.val+2≤d.val.choose 2 ∨ d.val=10) → 3≤d.val →
    Reserved16.loss d (a.val+b.val)+554268*a.val+46189*b.val≤row r+refund r d) ∧
    (∑ r∈range 27,row r)=34486862 := by
  unfold Reserved16.loss refund FiniteRange.badCount row; simp only [Nat.choose_eq_fast_choose]; decide
theorem unreserved (X A F : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      554268*(∑ v∈X,nbr G v A)+46189*(∑ v∈X,nbr G v F)≤34486862+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈activated G X s)).card) := by
  classical
  let bill := fun v => ((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 10).filter (fun s => v∈activated G X s)).card
  let r := rank X (trianglesAt G)
  have each (v : V) (vm : v∈X) : bill v+554268*nbr G v A+46189*nbr G v F≤row (r v)+act v := by
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd,Nat.add_comm]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have b := Reserved16.fiber G sz sep vm
    rw [Repair.nbr_add G v af] at b
    have cf' := card_le_card (filter_subset (G.Adj v) F)
    have z := table.1 ⟨r v,rk⟩ ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ dc (le_min (mem_filter.mp (hx vm)).2 (by decide))
    have rb : refund (r v) d≤act v := by
      unfold refund; split_ifs with eq
      · have lt : d<10 := by
          by_contra! ge
          have ten : d=10 := by omega
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
          change r v<27 at rk; omega
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated
          apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq,Nat.add_comm]; exact lr
        exact Simplicial16.active_fiber G X sz vm sat 9 d (min_le_left ..) (by omega)
      · exact Nat.zero_le _
    exact ((Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z).trans (Nat.add_le_add_left rb _)
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rwa [sum_by_rank X _ inj row,sz,table.2] at sum

end Graffiti384b.Twelve
#print axioms Graffiti384b.Twelve.unreserved
