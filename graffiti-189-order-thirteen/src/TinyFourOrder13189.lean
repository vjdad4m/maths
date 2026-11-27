import TinyFourOrder13Row4
import TinyFourOrder13Row5
import TinyFourOrder13Row6
import TinyFourOrder13Row7
import TinyFourOrder13Row8
import TinyFourOrder13Row9
import TinyFourOrder13Row10

namespace FourOrder13
open Finset

private theorem rows (j : ℕ) (jl : 4≤j) (jh : j≤10) (hj : j<13) : Table j hj := by
  have eq : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases eq with e|e|e|e|e|e|e <;> subst j
  · exact tbl4
  · exact tbl5
  · exact tbl6
  · exact tbl7
  · exact tbl8
  · exact tbl9
  · exact tbl10

private theorem mem_allDigits (d : List (Fin 3)) : d ∈ allDigits d.length := by
  induction d with
  | nil => simp [allDigits]
  | cons a as ih => fin_cases a <;> simp [allDigits,ih]

private theorem mem_allBits (d : List Bool) : d ∈ allBits d.length := by
  induction d with
  | nil => simp [allBits]
  | cons a as ih => cases a <;> simp [allBits,ih]

private theorem coord_fits (j : ℕ) (jl : 4≤j) (jh : j≤10) (k : Fin 11)
    (_h0 : k.val≠0) (h10 : k.val≠10)
    (hh : ¬(k.val=1 ∨ k.val+1=j ∨ k.val=j ∧ j≠10)) :
    (coord j k.val).val < (if j=10 then 7 else 6) := by
  have b := k.isLt
  by_cases h : j=10
  · simp [h]
  · rw [if_neg h]
    change min 6 (if j<10 ∧ j<k.val then k.val-4 else k.val-2)<6
    split
    · omega
    · have a : k.val+1≠j := fun e => hh (.inr (.inl e))
      have n : k.val≠j := fun e => hh (.inr (.inr ⟨e,h⟩))
      omega

private theorem checked (j : ℕ) (jl : 4≤j) (jh : j≤10) (m : Marks) (e f g h : Bool)
    (h0 : m 0=1) (h10 : m 10=2) (h1 : m 1=0)
    (hj1 : ∀ k : Fin 11, k.val+1=j → m k=0)
    (hj : ∀ k : Fin 11, k.val=j → j≠10 → m k=0)
    (hl : 4≤markCount m 1) (hr : 4≤markCount m 2) :
    check j m e f g h (by omega) := by
  let n := if j=10 then 7 else 6
  have nb : n≤7 := by dsimp [n]; split <;> omega
  let data := List.ofFn fun t : Fin n => m (site j ⟨t.val,by have z := t.isLt; omega⟩)
  have datalen : data.length = n := List.length_ofFn
  have me : proposedMarks j data = m := by
    have E := decode_complete j jl jh m h0 h10 h1 hj1 hj
    change decode j _ = m
    rw [← E]
    apply funext
    intro k
    simp only [decode]
    split
    · rfl
    split
    · rfl
    split
    · rfl
    next hh =>
      have h00 : k.val≠0 := by assumption
      have h10' : k.val≠10 := by assumption
      have cf : (coord j k.val).val < n := coord_fits j jl jh k h00 h10' hh
      simp only [data,List.getElem?_ofFn,dif_pos cf,Option.getD_some]
  let flags : List Bool := [e,f,g,h]
  have bm : flags ∈ allBits 4 := mem_allBits flags
  have npos : 3≤n := by dsimp [n]; split <;> omega
  have splitData : ∃ a b c tail, data=a::b::c::tail ∧ tail.length=n-3 := by
    match q : data with
    | [] => simp [q] at datalen; omega
    | a::[] => simp [q] at datalen; omega
    | a::b::[] => simp [q] at datalen; omega
    | a::b::c::tail =>
      refine ⟨a,b,c,tail,rfl,?_⟩
      simp only [q,List.length_cons] at datalen
      omega
  obtain ⟨a,b,c,tail,dt,lt⟩ := splitData
  have hlt : tail.length = (if j=10 then 4 else 3) := by
    by_cases h : j=10 <;> simp [n,h] at lt ⊢ <;> exact lt
  have mt : tail∈allDigits (if j=10 then 4 else 3) := hlt ▸ mem_allDigits tail
  have A := List.all_eq_true.mp (show TableShard j (by omega) a b c from rows j jl jh (by omega) a b c) tail mt
  have B : (allBits 4).all (evalModel j (by omega) data) = true := by
    rw [←dt] at A
    simpa only [me,if_pos (And.intro hl hr)] using A
  have C := List.all_eq_true.mp B flags bm
  have V : (!admissible j m e f g h (by omega) || success j m e f g)=true := by
    simpa [evalModel,flags,show decode j (fun k => (data[k.val]?).getD 0)=m from me] using C
  intro _ _ dg1 dgj d0 d1 dj d11 d12
  have Y : admissible j m e f g h (by omega) = true := by
    simp [admissible,hl,hr,dg1,dgj,d0,d1,dj,d11,d12]
  simpa [Y,success,Bool.and_eq_true,and_assoc] using V

/-- Finite certificate for the normalized one-omission patterns. -/
theorem tiny (j : ℕ) (jl : 4≤j) (jh : j≤10) (m : Marks) (e f g h : Bool)
    (h0 : m 0=1) (h10 : m 10=2) (h1 : m 1=0)
    (hj1 : ∀ k : Fin 11, k.val+1=j → m k=0)
    (hj : ∀ k : Fin 11, k.val=j → j≠10 → m k=0)
    (LEFT : 4≤markCount m 1) (RIGHT : 4≤markCount m 2)
    (deg1 : 4≤degree j m e f g h 1) (degj : 4≤degree j m e f g h ⟨j,by omega⟩)
    (d0 : (d2Set j m e f g h 0).card≤4) (d1 : (d2Set j m e f g h 1).card≤4)
    (dj : (d2Set j m e f g h ⟨j,by omega⟩).card≤4)
    (d11 : (d2Set j m e f g h 11).card≤4) (d12 : (d2Set j m e f g h 12).card≤4) :
    ∃ l : List Vertex, l.Nodup ∧ (∀ k : Vertex,k∈l) ∧
      l.Chain' (fun u v => edge j m e f g h u v=true) := by
  have r := checked j jl jh m e f g h h0 h10 h1 hj1 hj LEFT RIGHT
  obtain ⟨rfl,rfl,rfl,rfl,eq⟩ := r LEFT RIGHT deg1 degj d0 d1 dj d11 d12
  have M : m=winning := funext eq
  let L : List Vertex := [0,1,2,3,11,4,5,6,7,8,9,10,12]
  refine ⟨L,by decide,by decide,?_⟩
  have paths : ∀ h : Bool, L.Chain' (fun u v => edge 10 winning true true true h u v=true) := by decide
  simpa only [M] using paths h

#print axioms tbl4
#print axioms tbl10
#print axioms tiny

end FourOrder13
