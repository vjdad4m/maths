import Indexed183
import Run4Cert183
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti183.ExampleRun4
open SimpleGraph Graffiti183.Exceptional
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

theorem attach_model (f : Fin 7 ↪ V) (z l r : V)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hz : z ∉ indexSet f) (hl : l ∉ indexSet f) (hr : r ∉ indexSet f)
    (nzl : z ≠ l) (nzr : z ≠ r) (nlr : l ≠ r)
    (azl : ¬G.Adj z l) (azr : ¬G.Adj z r)
    (zA : ∀ i : Fin 7, G.Adj z (f i) ↔ i.val ≤ 3)
    (lA : ∀ i : Fin 7, G.Adj l (f i) ↔ i.val = 6 ∨ i.val ≤ 1 ∨ (G.Adj l (f 2) ∧ i.val = 2))
    (rA : ∀ i : Fin 7, G.Adj r (f i) ↔ (2 ≤ i.val ∧ i.val ≤ 4) ∨ (G.Adj r (f 1) ∧ i.val = 1)) :
    ∃ F : Fin 10 ↪ V, (∀ i j, G.Adj (F i) (F j) ↔
      Graffiti183.Run4Cert.adj (decide (G.Adj l (f 2))) (decide (G.Adj r (f 1))) (decide (G.Adj l r)) i j) ∧
      ∀ i : Fin 7, F (Graffiti183.Run4Cert.cyc i) = f i := by
  let o : Fin 3 → V := ![z,l,r]
  let M : Fin 10 → V := Fin.append f o
  have left (i : Fin 7) : M (Fin.castAdd 3 i) = f i := Fin.append_left _ _ _
  have right (j : Fin 3) : M (Fin.natAdd 7 j) = o j := Fin.append_right _ _ _
  have mix (i : Fin 7) (j : Fin 3) : f i ≠ o j := by
    have hz' : f i ≠ z := fun h => hz (mem_indexSet.mpr ⟨i,h⟩)
    have hl' : f i ≠ l := fun h => hl (mem_indexSet.mpr ⟨i,h⟩)
    have hr' : f i ≠ r := fun h => hr (mem_indexSet.mpr ⟨i,h⟩)
    fin_cases j <;> simpa [o]
  have mi : Function.Injective M := by
    intro i j
    revert j
    refine Fin.addCases (m:=7) (n:=3) (motive:=fun x => ∀ y : Fin 10, M x = M y → x = y) ?_ ?_ i
    · intro a j
      refine Fin.addCases (m:=7) (n:=3) (motive:=fun y => M _ = M y → _ = y) ?_ ?_ j
      · intro b h
        rw [left,left] at h
        exact congrArg (Fin.castAdd 3) (f.injective h)
      · intro b h
        rw [left,right] at h
        exact (mix a b h).elim
    · intro a j
      refine Fin.addCases (m:=7) (n:=3) (motive:=fun y => M _ = M y → _ = y) ?_ ?_ j
      · intro b h
        rw [right,left] at h
        exact (mix b a h.symm).elim
      · intro b h
        rw [right,right] at h
        fin_cases a <;> fin_cases b <;> simp [o,nzl,nzr,nlr,nzl.symm,nzr.symm,nlr.symm] at h ⊢
  let F : Fin 10 ↪ V := ⟨M,mi⟩
  let L := decide (G.Adj l (f 2))
  let R := decide (G.Adj r (f 1))
  let E := decide (G.Adj l r)
  have v7 : (7 : Fin 10).val = 7 := rfl
  have v8 : (8 : Fin 10).val = 8 := rfl
  have v9 : (9 : Fin 10).val = 9 := rfl
  have model (i j : Fin 10) : G.Adj (M i) (M j) ↔ Graffiti183.Run4Cert.adj L R E i j := by
    revert j
    refine Fin.addCases (m:=7) (n:=3)
      (motive:=fun x => ∀ y : Fin 10, G.Adj (M x) (M y) ↔ Graffiti183.Run4Cert.adj L R E x y) ?_ ?_ i
    · intro a j
      refine Fin.addCases (m:=7) (n:=3)
        (motive:=fun y => G.Adj (M _) (M y) ↔ Graffiti183.Run4Cert.adj L R E _ y) ?_ ?_ j
      · intro b
        rw [left,left,hcyc]
        have ha := a.isLt
        have hb := b.isLt
        unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj CycleAdj
        simp [Fin.castAdd,Fin.castLE]
        omega
      · intro b
        rw [left,right]
        have ha := a.isLt
        have zsym := (G.adj_comm (f a) z).trans (zA a)
        have lsym := (G.adj_comm (f a) l).trans (lA a)
        have rsym := (G.adj_comm (f a) r).trans (rA a)
        fin_cases b
        · change G.Adj (f a) z ↔ Graffiti183.Run4Cert.adj L R E (Fin.castAdd 3 a) 7
          rw [zsym]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9]; omega
        · change G.Adj (f a) l ↔ Graffiti183.Run4Cert.adj L R E (Fin.castAdd 3 a) 8
          rw [lsym]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9, L]; omega
        · change G.Adj (f a) r ↔ Graffiti183.Run4Cert.adj L R E (Fin.castAdd 3 a) 9
          rw [rsym]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          have na8 : a.val ≠ 8 := by omega
          have n10a : 10 ≠ a.val := by omega
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9, R, na8, n10a]
    · intro a j
      refine Fin.addCases (m:=7) (n:=3)
        (motive:=fun y => G.Adj (M _) (M y) ↔ Graffiti183.Run4Cert.adj L R E _ y) ?_ ?_ j
      · intro b
        rw [right,left]
        have hb := b.isLt
        fin_cases a
        · change G.Adj z (f b) ↔ Graffiti183.Run4Cert.adj L R E 7 (Fin.castAdd 3 b)
          rw [zA]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9]; omega
        · change G.Adj l (f b) ↔ Graffiti183.Run4Cert.adj L R E 8 (Fin.castAdd 3 b)
          rw [lA]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9, L]; omega
        · change G.Adj r (f b) ↔ Graffiti183.Run4Cert.adj L R E 9 (Fin.castAdd 3 b)
          rw [rA]
          unfold Graffiti183.Run4Cert.adj Graffiti183.Run4Cert.halfAdj
          have nb8 : b.val ≠ 8 := by omega
          have n10b : 10 ≠ b.val := by omega
          simp [Fin.castAdd,Fin.castLE, v7,v8,v9, R, nb8, n10b]
      · intro b
        rw [right,right]
        have alz : ¬ G.Adj l z := fun h => azl h.symm
        have arz : ¬ G.Adj r z := fun h => azr h.symm
        have arl := G.adj_comm r l
        fin_cases a <;> fin_cases b <;>
          simp [o,azl,azr,alz,arz,arl,Fin.natAdd,v7,v8,v9,
            Graffiti183.Run4Cert.adj,Graffiti183.Run4Cert.halfAdj,L,R,E]
  exact ⟨F,model,left⟩

#print axioms attach_model
end Graffiti183.ExampleRun4
