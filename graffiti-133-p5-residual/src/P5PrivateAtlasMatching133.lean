import P5PrivateAtlasGraph133

namespace Graffiti133P5PrivateAtlas
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133PrivateGeneric
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def qid (i : Fin 5) : Fin 15 := ⟨i.val+10,by have := i.isLt; omega⟩
private def extras (i : Fin 5) : List (Bit 15) := [(qid i,qid (i+4),true)]
private def mRow (i : Nat) : Tree 15 :=
  match i with
  | 0 => (.split 10 12 (.split 10 13 (.split 11 13 (.split 11 14 (.split 12 14 (.split 13 14 (.path ![11,10,14,9,7,2,3,8,13]) (.path ![0,1,2,3,8,13,14,10,11])) (.four 7 14 9 12)) (.four 6 14 9 11)) (.four 6 13 8 11)) (.four 5 13 8 10)) (.four 5 12 7 10))
  | 1 => (.split 10 12 (.split 10 13 (.split 11 13 (.split 11 14 (.split 12 14 (.split 12 13 (.path ![10,11,12,7,9,4,3,8,13]) (.path ![0,1,2,3,8,13,12,11,10])) (.four 7 14 9 12)) (.four 6 14 9 11)) (.four 6 13 8 11)) (.four 5 13 8 10)) (.four 5 12 7 10))
  | 2 => (.split 10 12 (.split 10 13 (.split 11 13 (.split 11 14 (.split 12 14 (.split 10 11 (.path ![10,5,0,4,9,6,11,12,13]) (.path ![0,1,2,3,8,13,12,11,10])) (.four 7 14 9 12)) (.four 6 14 9 11)) (.four 6 13 8 11)) (.four 5 13 8 10)) (.four 5 12 7 10))
  | 3 => (.split 10 12 (.split 10 13 (.split 11 13 (.split 11 14 (.split 12 14 (.split 10 14 (.path ![10,5,0,1,6,9,14,13,12]) (.path ![0,4,3,2,7,12,13,14,10])) (.four 7 14 9 12)) (.four 6 14 9 11)) (.four 6 13 8 11)) (.four 5 13 8 10)) (.four 5 12 7 10))
  | 4 => (.split 10 12 (.split 10 13 (.split 11 13 (.split 11 14 (.split 12 14 (.split 12 13 (.path ![10,14,13,8,6,1,2,7,12]) (.path ![0,4,3,2,7,12,13,14,10])) (.four 7 14 9 12)) (.four 6 14 9 11)) (.four 6 13 8 11)) (.four 5 13 8 10)) (.four 5 12 7 10))
  | _ => .four 0 0 0 0

private theorem petersen_double (i : Fin 5) :
    checked (outerSpec 31 (min i (i+1)) (max i (i+1))) (extras i) (mRow i.val)=true := by
  fin_cases i <;> decide

private theorem layer_at_q (H : Hole G 5) (w q : Fin 5→V) (i : Fin 5) :
    layerFifteen H w q (qid i)=q i := by
  rw [layerFifteen,dif_neg (by simp [qid])]
  congr 1

private theorem cyclic_pair_exact : ∀ i j k : Fin 5,Cyclic i j → Cyclic i k → j≠k →
    (j=i+1 ∧ k=i+4) ∨ (k=i+1 ∧ j=i+4) := by decide

theorem petersen_outer_matching (H : Hole G 5)
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (cy : ∀ i,H.c i∈D)
    (w q : Fin 5→V) (wd : ∀ i,w i∈D) (wo : ∀ i,Outside H.c (w i))
    (wpriv : ∀ i j,G.Adj (w i) (H.c j)↔j=i)
    (qpriv : ∀ i,PrivateAt G D (w i) (q i))
    (bits : ∀ i : Fin 5,(31:Nat).testBit i.val=decide (G.Adj (w i) (w (i+2)))) :
    (∀ i j,G.Adj (q i) (q j)→Cyclic i j) ∧
      ∀ i j k,G.Adj (q i) (q j)→G.Adj (q i) (q k)→j=k := by
  classical
  have wi : Function.Injective w := by
    intro i j e
    exact ((wpriv j i).mp (e ▸ (wpriv i i).mpr rfl))
  have qi : Function.Injective q := by
    intro i j e
    by_contra ne
    exact (qpriv j).2.2 (w i) (wd i) (fun he=>ne (wi he)) (e ▸ (qpriv i).2.1)
  let a := layerTen H w
  have ai : Function.Injective a := ten_layer_injective H w wo wi
  have ad (i : Fin 10) : a i∈D := by
    dsimp only [a]
    by_cases lo : i.val<5
    · rw [layerTen,dif_pos lo]
      exact cy _
    · rw [layerTen,dif_neg lo]
      exact wd _
  have aFit : ∀ i j : Fin 10,G.Adj (a i) (a j)↔firstEdge 31 i.val j.val=true :=
    ten_layer_fit H h4 w wo wpriv 31 bits
  have certain (i : Fin 5) : G.Adj (w i) (w (i+2)) := by
    have full : ∀ i : Fin 5,(31:Nat).testBit i.val=true := by decide
    exact of_decide_eq_true ((bits i).symm.trans (full i))
  have cyclic (i j : Fin 5) (e : G.Adj (q i) (q j)) : Cyclic i j := by
    have wiq : w i≠q j := fun h=>(qpriv j).1 (h ▸ wd i)
    have qiw : q i≠w j := fun h=>(qpriv i).1 (h.symm ▸ wd j)
    have ne : ¬G.Adj (w i) (w j) := by
      intro ed
      exact qiw (h4 (w i) (q j) (q i) (w j) wiq (qpriv i).2.1.symm e.symm ed (qpriv j).2.1)
    rcases two_steps_cases i j with rfl|h|h|h
    · exact (e.ne rfl).elim
    · exact h
    · exact (ne (h ▸ certain i)).elim
    · exact (ne (h ▸ certain j).symm).elim
  refine ⟨cyclic,?_⟩
  have impossible (i : Fin 5) (e : G.Adj (q i) (q (i+1))) (d : G.Adj (q i) (q (i+4))) :
      False := by
    have fresh (i : Fin 5) (j : Fin 10) : q i≠a j := fun e=>(qpriv i).1 (e.symm ▸ ad j)
    have only (i : Fin 5) (j : Fin 10) : G.Adj (a j) (q i)↔j.val=i.val+5 := by
      have qn : G.Adj (a j) (q i) ↔ a j=w i := by
        constructor
        · intro edge
          by_contra he
          exact (qpriv i).2.2 (a j) (ad j) he edge.symm
        · intro eq
          exact eq.symm ▸ (qpriv i).2.1.symm
      rw [qn]
      have wj : a ⟨i.val+5,by have := i.isLt; omega⟩=w i := by
        dsimp only [a]
        rw [layerTen,dif_neg (by omega : ¬i.val+5<5)]
        congr 1
      rw [←wj,ai.eq_iff,Fin.ext_iff]
    let bf := layerFifteen H w q
    have bfI : Function.Injective bf := fifteen_layer_injective H w q ai qi fresh
    have e0 : G.Adj (q (min i (i+1))) (q (max i (i+1))) := by
      rcases le_total i (i+1) with b|b
      · simpa [min_eq_left b,max_eq_right b] using e
      · simpa [min_eq_right b,max_eq_left b] using e.symm
    have bfFit := fifteen_layer_fit H w q 31 (min i (i+1)) (max i (i+1)) aFit only e0
    have fitExtra : BitsOK G bf (extras i) := by
      intro t ht
      have same := List.mem_singleton.mp ht
      subst t
      change G.Adj (layerFifteen H w q (qid i)) (layerFifteen H w q (qid (i+4))) ↔ true=true
      rw [layer_at_q,layer_at_q]
      exact iff_of_true d rfl
    exact checked_sound h4 h9 bfI _ bfFit _ _ fitExtra (petersen_double i)
  intro i j k a b
  apply Classical.byContradiction
  intro ne
  rcases cyclic_pair_exact i j k (cyclic i j a) (cyclic i k b) ne with ⟨e,d⟩|⟨e,d⟩
  · exact impossible i (e ▸ a) (d ▸ b)
  · exact impossible i (e ▸ b) (d ▸ a)

#print axioms petersen_outer_matching
end Graffiti133P5PrivateAtlas
