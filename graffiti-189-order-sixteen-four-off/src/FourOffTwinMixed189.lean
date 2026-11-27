import FourOffTwinCompat189
import FourOffTwinMarks189
import FourOffTwinRows189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private hamilton_of_labeled_chain order_sixteen_four_off_labeling length_eleven_left_block_of_small_path_d2 left_boundary_porters_at_most_two right_boundary_porters_at_most_two from FourOffGraphCore189
open private mark_holes_of_pin_and_missing_endpoint from FourOffGraphSupport189

open private order_sixteen_four_off_mixed_marks from FourOffTwinMarks189

open private model16_twin_compatible model16_d2_upper_twin from FourOffTwinCompat189
open OffFour16Twin in
private theorem length_eleven_four_off_two_pin_mixed_spans
    (boundaryTwo : ∀ (_hc : G.Connected) (_even : ∀ v,(EvenFrom G v).card≤5)
    {a b x : V} {p : G.Walk a b} (_hp : IsLongest p) (_ah : 4≤G.degree a) (_bh : 4≤G.degree b)
    (_len : 6≤p.length) (_xo : x∉p.support) (_xi : 1∈Pins p x)
    (S : Finset V) (_off : ∀ z∈S,z∉p.support) (_pins : ∀ z∈S,1∈Pins p z),
    S.card≤2)
    (table : ∀ j : ℕ,4≤j → j≤9 → row j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (xo : x∉p.support) {j : ℕ} (h1 : 1∈Pins p x) (hj : j∈Pins p x) (jlo : 4≤j) (jhi : j≤9)
    (ports : ∀ z∉p.support,Pins p z⊆({1,j}:Finset ℕ))
    (clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w)
    (hole1 : 1∉LeftMarks p∪RightMarks p) (holep : j-1∉LeftMarks p∪RightMarks p)
    (holej : j∉LeftMarks p∪RightMarks p) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  obtain ⟨φ,inj,onto,φ12,value,out⟩ := order_sixteen_four_off_labeling hp len off xo
  obtain ⟨m,m0,m10,H,N,ml,mr,L,R⟩ :=
    order_sixteen_four_off_mixed_marks hp ah bh len xo h1 jlo jhi hole1 holep holej
  let u : Fin 4→Fin 16 := fun k => ⟨12+k.val,by have n := k.isLt; omega⟩
  have ui : Function.Injective u := by
    intro a b e
    have g := congrArg Fin.val e
    apply Fin.ext
    change 12+a.val=12+b.val at g
    omega
  have U (k : Fin 4) : φ (u k)∉p.support := out _ (by change 12≤12+k.val; omega)
  let c : Slots := fun k => if 1∈Pins p (φ (u k)) then (if j∈Pins p (φ (u k)) then 3 else 1)
    else (if j∈Pins p (φ (u k)) then 2 else 0)
  have c0 : c 0=3 := by
    have u0 : u 0=12 := rfl
    simp [c,u0,φ12,h1,hj]
  have lp (k : Fin 4) : (c k=1 ∨ c k=3) ↔ 1∈Pins p (φ (u k)) := by
    by_cases l : 1∈Pins p (φ (u k)) <;> by_cases r : j∈Pins p (φ (u k)) <;> simp [c,l,r]
  have rp (k : Fin 4) : (c k=2 ∨ c k=3) ↔ j∈Pins p (φ (u k)) := by
    by_cases l : 1∈Pins p (φ (u k)) <;> by_cases r : j∈Pins p (φ (u k)) <;> simp [c,l,r]
  have v0 (k : Fin 4) (hk : c k=0) : ¬4≤G.degree (φ (u k)) := by
    intro high
    have bd := degree_off_bound hp (U k)
    rw [off] at bd
    obtain ⟨i,im⟩ := card_pos.mp (show 0<(Pins p (φ (u k))).card by omega)
    have is : i=1 ∨ i=j := by simpa using ports _ (U k) im
    rcases is with rfl|rfl
    · have q := (lp k).mpr im
      simp [hk] at q
    · have q := (rp k).mpr im
      simp [hk] at q
  let Nil := univ.filter (fun k : Fin 4 => c k=0)
  have one : Nil.card≤1 := by
    by_contra n
    obtain ⟨v,vm,w,wm,vw⟩ := one_lt_card.mp (Nat.lt_of_not_ge n)
    have ne : φ (u v)≠φ (u w) := fun e => vw (ui (inj e))
    exact (degree _ _ ne).elim (v0 _ (mem_filter.mp vm).2) (v0 _ (mem_filter.mp wm).2)
  have ac : 3≤acount c := by
    have S := filter_card_add_filter_neg_card_eq_card (s:=(univ : Finset (Fin 4))) (fun k => c k=0)
    change Nil.card+acount c=(univ : Finset (Fin 4)).card at S
    rw [card_univ,Fintype.card_fin] at S
    omega
  let I := univ.filter (fun k : Fin 4 => c k=1 ∨ c k=3)
  let B := I.image (fun k=>φ (u k))
  have lc : lcount c≤2 := by
    have ou (z : V) (zb : z∈B) : z∉p.support := by
      obtain ⟨k,_,rfl⟩ := mem_image.mp zb
      exact U k
    have pi (z : V) (zb : z∈B) : 1∈Pins p z := by
      obtain ⟨k,km,rfl⟩ := mem_image.mp zb
      exact (lp k).mp (mem_filter.mp km).2
    have sm := boundaryTwo hc even hp ah bh (by omega) xo h1 B ou pi
    change (I.image (fun k => φ (u k))).card≤2 at sm
    have ce := card_image_of_injective I (inj.comp ui)
    change (I.image (fun k => φ (u k))).card=I.card at ce
    rw [ce] at sm
    exact sm
  have interpret (w : Fin 16) (wo : 12≤w.val) :
      ∃ k : Fin 4, portAt c w.val=c k ∧ u k=w := by
    have wu : w.val<16 := w.isLt
    let k : Fin 4 := ⟨w.val-12,by omega⟩
    exact ⟨k,by simp [portAt,wo,wu,k],Fin.ext (by change 12+(w.val-12)=w.val; omega)⟩
  have il (w : Fin 16) (wo : 12≤w.val) :
      (portAt c w.val=1 ∨ portAt c w.val=3) ↔ 1∈Pins p (φ w) := by
    obtain ⟨k,pk,uk⟩ := interpret w wo
    rw [pk,←uk]
    exact lp k
  have ir (w : Fin 16) (wo : 12≤w.val) :
      (portAt c w.val=2 ∨ portAt c w.val=3) ↔ j∈Pins p (φ w) := by
    obtain ⟨k,pk,uk⟩ := interpret w wo
    rw [pk,←uk]
    exact rp k
  obtain ⟨edgeOK,leftE,rightE⟩ := model16_twin_compatible hp len jhi φ inj value out clique m c L R il ir
  have cap := fun y => distanceTwo_le_of_even 4 y (even y)
  have E0 : (d2Set j m c 0).card≤4 := model16_d2_upper_twin hc φ inj _ 0 edgeOK leftE (cap _)
  have E11 : (d2Set j m c 11).card≤4 := model16_d2_upper_twin hc φ inj _ 11 edgeOK rightE (cap _)
  obtain ⟨l,nd,all,chain⟩ := check_row (table j jlo jhi) m0 m10 H N ml mr c0 ac lc E0 E11
  letI : Nonempty V := ⟨a⟩
  exact hamilton_of_labeled_chain φ inj onto l nd all (chain.imp (fun u v h => edgeOK u v h))

#print axioms length_eleven_four_off_two_pin_mixed_spans
end Graffiti189LongestPath.TwoCut.SmallOrderFour
