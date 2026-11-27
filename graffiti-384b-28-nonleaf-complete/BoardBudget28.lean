import MixedTrials28

namespace Graffiti384b.FiveBoard28
open Finset SimpleGraph Thin28 HighSquare28
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem center_zero (W O : Finset V) {t : V} (o : V) (ts : (G.neighborFinset t).card=3) :
    payment G W (G.neighborFinset t) O t o t=0 := by
  let T := G.neighborFinset t
  have credit (x : V) (xm : x∈T) : 2≤nbr G t (T.erase x) := by
    unfold nbr
    rw [filter_true_of_mem (fun _ m => (G.mem_neighborFinset ..).mp (mem_erase.mp m).2),card_erase_of_mem xm]
    change 2≤(G.neighborFinset t).card-1; omega
  have d : doubleCost G W T O t=0 := sum_eq_zero (fun x xm => sum_eq_zero (fun y _ =>
    supported_zero G 7 ((credit x xm).trans (Repair.nbr_mono G t (show T.erase x⊆T.erase x∪O.erase y from subset_union_left)))))
  have a : singleCost G W T o t=0 := sum_eq_zero (fun x xm => supported_zero G 8
    ((credit x xm).trans (Repair.nbr_mono G t (subset_insert o (T.erase x)))))
  have b : singleCost G W O t t=0 := sum_eq_zero (fun y _ => kept G (mem_insert_self t (O.erase y)))
  change 3*doubleCost G W T O t+2*(singleCost G W T o t+singleCost G W O t t)=0
  rw [d,a,b]

theorem lower_mass {W T O : Finset V} (t o : V) (ws : W.card=20) (ts : T.card=3) (os : O.card=3)
    (large : 14≤gamma G) : 10814040≤∑ z,payment G W T O t o z := by
  classical
  have two {D : Finset V} (size : D.card=3) {x : V} (xm : x∈D) : (D.erase x).card=2 := by
    rw [card_erase_of_mem xm,size]
  have both (x : V) (xm : x∈T) (y : V) (ym : y∈O) :
      232560≤∑ z,hit G W (T.erase x∪O.erase y) 7 z := by
    have sz := card_union_le (T.erase x) (O.erase y)
    rw [two ts xm,two os ym] at sz
    have k := budget G W (T.erase x∪O.erase y) 7
    rw [ws] at k
    exact (Nat.mul_le_mul_left ((20:ℕ).choose 7) (by omega : 3≤gamma G-(T.erase x∪O.erase y).card-7)).trans k
  have one {D : Finset V} (size : D.card=3) (p x : V) (xm : x∈D) :
      377910≤∑ z,hit G W (insert p (D.erase x)) 8 z := by
    have sz := card_insert_le p (D.erase x)
    rw [two size xm] at sz
    have k := budget G W (insert p (D.erase x)) 8
    rw [ws] at k
    exact (Nat.mul_le_mul_left ((20:ℕ).choose 8) (by omega : 3≤gamma G-(insert p (D.erase x)).card-8)).trans k
  have dj := sum_le_sum (s:=T) (fun x xm => sum_le_sum (s:=O) (both x xm))
  have tj := sum_le_sum (s:=T) (one ts o)
  have oj := sum_le_sum (s:=O) (one os t)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,ts,os] at dj tj oj
  have ed : (∑ z,doubleCost G W T O z)=∑ x∈T,∑ y∈O,∑ z,hit G W (T.erase x∪O.erase y) 7 z := by
    unfold doubleCost; rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_comm)
  have ec (D : Finset V) (p : V) : (∑ z,singleCost G W D p z)=∑ x∈D,∑ z,hit G W (insert p (D.erase x)) 8 z := sum_comm
  simp only [payment,sum_add_distrib,←mul_sum,ed,ec]
  omega

end Graffiti384b.FiveBoard28
#print axioms Graffiti384b.FiveBoard28.center_zero
#print axioms Graffiti384b.FiveBoard28.lower_mass
