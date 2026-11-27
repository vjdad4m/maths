import SixRows28

namespace Graffiti384b.FiveBoard28
open Finset SimpleGraph Thin28 HighSquare28
open private Repair.nbr_add Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def doubleCost (W T O : Finset V) (z : V) :=
  ∑ x∈T,∑ y∈O,hit G W (T.erase x∪O.erase y) 7 z
def singleCost (W T : Finset V) (o z : V) :=
  ∑ x∈T,hit G W (insert o (T.erase x)) 8 z
def payment (W T O : Finset V) (t o z : V) :=
  3*doubleCost G W T O z+2*(singleCost G W T o z+singleCost G W O t z)

theorem payment_swap (W T O : Finset V) (t o z : V) :
    payment G W T O t o z=payment G W O T o t z := by
  unfold payment doubleCost
  rw [sum_comm (s:=T) (t:=O)]
  simp only [union_comm (T.erase _) (O.erase _),Nat.add_comm (singleCost G W T o z)]

theorem exterior_cost {W T O : Finset V} {t o z : V} (ws : W.card=20)
    (ts : T.card=3) (os : O.card=3) (sep : Disjoint T O) (tw : Disjoint T W) (ow : Disjoint O W)
    (toff : t∉W) (ooff : o∉W) (zm : z∈W) (nt : ¬G.Adj z t) (no : ¬G.Adj z o) :
    payment G W T O t o z≤ interior (nbr G z W) (nbr G z T) (nbr G z O) := by
  let d := nbr G z W
  have single {A : Finset V} {p : V} (ac : A.card=3) (aw : Disjoint A W) (po : p∉W) (np : ¬G.Adj z p) :
      singleCost G W A p z≤rotation (nbr G z A) (bill 20 8 d) := by
    rw [←rotation_sum G ac z]; apply sum_le_sum
    intro a _
    have dis : Disjoint (insert p (A.erase a)) W := disjoint_insert_left.mpr ⟨po,aw.mono_left (erase_subset ..)⟩
    have k := bill_bound G dis zm 8
    have c : nbr G z (insert p (A.erase a))=nbr G z (A.erase a) := by simp [nbr,filter_insert,np]
    rwa [ws,c] at k
  have joint : doubleCost G W T O z≤rotation (nbr G z T)
      (fun g => rotation (nbr G z O) (fun h => bill 20 7 d (g+h))) := by
    rw [←rotation_sum G ts z]; apply sum_le_sum; intro x _
    rw [←rotation_sum G os z]; apply sum_le_sum; intro y _
    have dis := disjoint_union_left.mpr ⟨tw.mono_left (erase_subset x T),ow.mono_left (erase_subset y O)⟩
    have k := bill_bound G dis zm 7
    rwa [ws,Repair.nbr_add G z (sep.mono (erase_subset x T) (erase_subset y O))] at k
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 joint)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add (single ts tw ooff no) (single os ow toff nt)))

/-- A boundary vertex is outside the sampled pool. One fixed neighbor
leaves only those samples missing every exterior neighbor to pay for. -/
theorem boundary_hit {W P : Finset V} {w : V} (ws : W.card=20) (out : w∉W) (dis : Disjoint P W)
    (k g : ℕ) (pos : 1≤g) (credit : g≤nbr G w P) : hit G W P k w≤outsideBill k (nbr G w W) g := by
  by_cases enough : 2≤g
  · rw [supported_zero G k (enough.trans credit),outsideBill,if_pos enough]
  · have one : 0<(P.filter (G.Adj w)).card := pos.trans credit
    obtain ⟨x,xm⟩ := card_pos.mp one
    obtain ⟨xp,wx⟩ := mem_filter.mp xm
    have ns : x∉W := fun xw => disjoint_left.mp dis xp xw
    simpa only [outsideBill,if_neg enough,ws,if_neg out,Nat.sub_zero] using credited G (b:=k) xp ns wx

/-- For a vertex w in T only the orientation dropping w from T can
charge it. The opposite-center trial, and all three trials retaining
its own center, use the same exterior degree d. -/
theorem boundary_cost {W T O : Finset V} {t o w : V} (ws : W.card=20) (os : O.card=3)
    (sep : Disjoint T O) (tw : Disjoint T W) (ow : Disjoint O W)
    (toff : t∉W) (ooff : o∉W) (tO : t∉O) (wt : G.Adj w t) (wm : w∈T) (low : 1≤nbr G w T) :
    payment G W T O t o w≤boundary (nbr G w W) (nbr G w T) (nbr G w O) := by
  classical
  let d := nbr G w W
  let i := nbr G w T
  let j := nbr G w O
  have emptyW : w∉W := fun h => disjoint_left.mp tw wm h
  have self : nbr G w (T.erase w)=i := by
    change ((T.erase w).filter (G.Adj w)).card=(T.filter (G.Adj w)).card
    congr 1; ext z
    simp only [mem_filter,mem_erase]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.ne.symm,h.1⟩,h.2⟩⟩
  have joint : doubleCost G W T O w≤rotation j (fun h => outsideBill 7 d (i+h)) := by
    unfold doubleCost
    rw [sum_eq_single_of_mem w wm (by
      intro x _ xw; apply sum_eq_zero; intro y _
      exact kept G (mem_union_left (O.erase y) (mem_erase.mpr ⟨xw.symm,wm⟩)))]
    rw [show j=nbr G w O from rfl,←rotation_sum G os w]
    apply sum_le_sum; intro y _
    have dis := disjoint_union_left.mpr ⟨tw.mono_left (erase_subset w T),ow.mono_left (erase_subset y O)⟩
    apply boundary_hit G ws emptyW dis 7 _ (by change 1≤nbr G w T+_; omega)
    rw [Repair.nbr_add G w (sep.mono (erase_subset w T) (erase_subset y O)),self]
  have own : singleCost G W T o w≤outsideBill 8 d i := by
    unfold singleCost
    rw [sum_eq_single_of_mem w wm (by
      intro x _ xw; exact kept G (mem_insert_of_mem (mem_erase.mpr ⟨xw.symm,wm⟩)))]
    apply boundary_hit G ws emptyW (disjoint_insert_left.mpr ⟨ooff,tw.mono_left (erase_subset ..)⟩) 8 i low
    exact self ▸ Repair.nbr_mono G w (subset_insert o (T.erase w))
  have other : singleCost G W O t w≤rotation j (fun h => outsideBill 8 d (1+h)) := by
    rw [show j=nbr G w O from rfl,←rotation_sum G os w]
    apply sum_le_sum; intro y _
    apply boundary_hit G ws emptyW (disjoint_insert_left.mpr ⟨toff,ow.mono_left (erase_subset ..)⟩) 8 _ (by omega)
    have no : t∉O.erase y := fun h => tO ((erase_subset ..) h)
    simp [nbr,filter_insert,wt,no,card_insert_of_not_mem,Nat.add_comm]
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 joint) (Nat.mul_le_mul_left 2 (Nat.add_le_add own other))

end Graffiti384b.FiveBoard28
#print axioms Graffiti384b.FiveBoard28.exterior_cost
#print axioms Graffiti384b.FiveBoard28.boundary_cost
