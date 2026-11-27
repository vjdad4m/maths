import FourOffTwinModel189
import SmallOrderFour189
import Batteries.Tactic.OpenPrivate

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189


private theorem model16_d2_upper_twin (hc : G.Connected)
    (φ : Fin 16 → V) (inj : Function.Injective φ)
    (E : Fin 16 → Fin 16 → Bool) (z : Fin 16)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card≤4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 16,E z u=true ∧ E u y=true).card≤4 := by
  classical
  let Q := univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 16,E z u=true ∧ E u y=true
  have sub : Q.image φ ⊆ DistanceTwo G (φ z) := by
    intro y hy
    obtain ⟨v,vq,rfl⟩ := mem_image.mp hy
    obtain ⟨vne,no,w,zw,wv⟩ := (mem_filter.mp vq).2
    have ne : φ z≠φ v := fun e => vne (inj e).symm
    have no' : ¬G.Adj (φ z) (φ v) := fun e => by
      have r := rev v e
      simp [r] at no
    exact mem_distanceTwo.mpr (dist_two hc ne no' (forw z w zw) (forw w v wv))
  have c := card_le_card sub
  rw [card_image_of_injective _ inj] at c
  exact c.trans cap


open OffFour16Twin in
private theorem model16_twin_compatible
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=11) {j : ℕ} (jhi : j≤9)
    (φ : Fin 16→V) (inj : Function.Injective φ)
    (value : ∀ k : Fin 16,k.val≤11 → φ k=p.getVert k.val)
    (out : ∀ k : Fin 16,12≤k.val → φ k∉p.support)
    (clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w)
    (m : Marks) (c : Slots)
    (L : ∀ k : Fin 11,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 11,m k=2 ↔ G.Adj b (p.getVert k.val))
    (lp : ∀ w : Fin 16,12≤w.val →
      ((portAt c w.val=1 ∨ portAt c w.val=3) ↔ 1∈Pins p (φ w)))
    (rp : ∀ w : Fin 16,12≤w.val →
      ((portAt c w.val=2 ∨ portAt c w.val=3) ↔ j∈Pins p (φ w))) :
    (∀ v w,edge j m c v w=true → G.Adj (φ v) (φ w)) ∧
    (∀ v,G.Adj (φ 0) (φ v) → edge j m c 0 v=true) ∧
    (∀ v,G.Adj (φ 11) (φ v) → edge j m c 11 v=true) := by
  classical
  have a0 : φ 0=a := by rw [value 0 (by decide)]; exact p.getVert_zero
  have b11 : φ 11=b := by rw [value 11 (by decide)]; simpa only [len] using p.getVert_length
  have direction (v w : Fin 16) (h : dir j m c v w=true) : G.Adj (φ v) (φ w) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with ((((ha|hb)|hc)|he)|hf)
    · rw [value v (by omega),value w ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · exact clique _ (out _ hb.1) _ (out _ (by omega))
        (fun e => by have g := congrArg Fin.val (inj e); omega)
    · have wo : 12≤w.val := by
        by_cases yes : 12≤w.val
        · exact yes
        · have o : portAt c w.val=0 := by simp [portAt,yes]
          rw [o] at hc
          exfalso
          rcases hc with ⟨_,E⟩|⟨_,E⟩
          · rcases E with E|E
            · exact (by decide : (0:Fin 4)≠1) E
            · exact (by decide : (0:Fin 4)≠3) E
          · rcases E with E|E
            · exact (by decide : (0:Fin 4)≠2) E
            · exact (by decide : (0:Fin 4)≠3) E
      rcases hc with ⟨v1,kl⟩|⟨vj,kr⟩
      · rw [value v (by omega),v1]
        exact (pin_data ((lp w wo).mp kl)).2.symm
      · rw [value v (by omega),vj]
        exact (pin_data ((rp w wo).mp kr)).2.symm
    · by_cases q : v.val=0 ∧ 1≤w.val ∧ w.val≤11
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [value v (by omega),value w q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨w.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (w.val-1+1)) at h
        rwa [show w.val-1+1=w.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : w.val=11 ∧ v.val<11
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [value v (by omega),value w (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨v.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  have edgeOK (v w : Fin 16) (h : edge j m c v w=true) : G.Adj (φ v) (φ w) := by
    simp only [edge,Bool.or_eq_true] at h
    exact h.elim (direction _ _) (fun e => (direction _ _ e).symm)
  have leftE (v : Fin 16) (va : G.Adj (φ 0) (φ v)) : edge j m c 0 v=true := by
    have vp : v.val≤11 := by
      by_cases yes : v.val≤11
      · exact yes
      · exact False.elim ((no_endpoints hp (out v (by omega))).1 ((a0 ▸ va).symm))
    have up : 1≤v.val := by
      by_cases yes : 1≤v.val
      · exact yes
      · have ev : v=0 := Fin.ext (show v.val=(0:Fin 16).val by change v.val=0; omega)
        exact False.elim (G.loopless _ (ev ▸ va))
    have q : (0:Fin 16).val=0 ∧ 1≤v.val ∧ v.val≤11 := ⟨rfl,up,vp⟩
    have ia : G.Adj a (p.getVert ((v.val-1)+1)) := by
      rw [show v.val-1+1=v.val by omega,←value v vp,←a0]
      exact va
    have h : m ⟨v.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [edge,Bool.or_eq_true]
    left
    simp [dir,q,h]
  have rightE (v : Fin 16) (vb : G.Adj (φ 11) (φ v)) : edge j m c 11 v=true := by
    have vp : v.val≤11 := by
      by_cases yes : v.val≤11
      · exact yes
      · exact False.elim ((no_endpoints hp (out v (by omega))).2 ((b11 ▸ vb).symm))
    have up : v.val<11 := by
      by_cases yes : v.val<11
      · exact yes
      · have ev : v=11 := Fin.ext (show v.val=(11:Fin 16).val by change v.val=11; omega)
        exact False.elim (G.loopless _ (ev ▸ vb))
    have q : (11:Fin 16).val=11 ∧ v.val<11 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert v.val) := by
      rw [←value v vp,←b11]
      exact vb
    have h : m ⟨v.val,up⟩=2 := (R _).mpr ib
    simp only [edge,Bool.or_eq_true]
    right
    simp [dir,q,h]
  exact ⟨edgeOK,leftE,rightE⟩

#print axioms model16_twin_compatible

end Graffiti189LongestPath.TwoCut.SmallOrderFour
