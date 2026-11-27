import TinyFourOrder14OnePrune

namespace FourOrder14One
open Finset

def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (allBits n).map (false :: ·) ++ (allBits n).map (true :: ·)

def allDigits : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => (allDigits n).map ((0 : Fin 3) :: ·) ++
    (allDigits n).map ((1 : Fin 3) :: ·) ++ (allDigits n).map ((2 : Fin 3) :: ·)

private theorem mem_allDigits (d : List (Fin 3)) : d ∈ allDigits d.length := by
  induction d with
  | nil => simp [allDigits]
  | cons a as ih => fin_cases a <;> simp [allDigits,ih]

private theorem mem_allBits (d : List Bool) : d ∈ allBits d.length := by
  induction d with
  | nil => simp [allBits]
  | cons a as ih => cases a <;> simp [allBits,ih]

noncomputable def admissible (i j : ℕ) (m : Marks) (e f g h t : Bool) (hi : i<14) (hj : j<14) : Bool :=
  decide (4≤degree i j m e f g h t ⟨i,hi⟩) &&
  decide (4≤degree i j m e f g h t ⟨j,hj⟩) &&
  decide ((d2Set i j m e f g h t 0).card≤4) &&
  decide ((d2Set i j m e f g h t ⟨i,hi⟩).card≤4) &&
  decide ((d2Set i j m e f g h t ⟨j,hj⟩).card≤4) &&
  decide ((d2Set i j m e f g h t 12).card≤4)

noncomputable def evalModel (i j : ℕ) (hi : i<14) (hj : j<14) (d : List (Fin 3)) (flags : List Bool) : Bool :=
  let m := decode i j d
  let g := fun k : ℕ => (flags[k]?).getD false
  !admissible i j m (g 0) (g 1) (g 2) (g 3) (g 4) hi hj ||
  hasPath i j m (g 0) (g 1) (g 2) (g 3) (g 4) || exceptionB i j m (g 1) (g 2) (g 3) (g 4)

def Shard (i j : ℕ) (hi : i<14) (hj : j<14) (a b c d : Fin 3) : Prop :=
  (allDigits ((sites i j).length-4)).all (fun tail =>
    let ds := a::b::c::d::tail
    let m := decode i j ds
    if 4≤markCount m 1 ∧ 4≤markCount m 2 ∧
      (d2Set i j m false false false false false 0).card≤4 ∧
      (d2Set i j m false false false false false 12).card≤4 then
      (allBits 5).all (evalModel i j hi hj ds)
    else true) = true

def Table (i j : ℕ) (hi : i<14) (hj : j<14) : Prop :=
  ∀ a b c d : Fin 3, Shard i j hi hj a b c d

theorem checked (i j : ℕ) (hi : i<14) (hj : j<14) (ip : 1≤i) (sep : i+3≤j) (jp : j≤11)
    (tabs : Table i j hi hj)
    (enough : 4≤(sites i j).length) (m : Marks) (e f g h t : Bool)
    (h0 : m 0=1) (h12 : m 11=2)
    (holes : ∀ k : Fin 12, hole i j k.val → m k=0)
    (LEFT : 4≤markCount m 1) (RIGHT : 4≤markCount m 2)
    (di : 4≤degree i j m e f g h t ⟨i,hi⟩)
    (dj : 4≤degree i j m e f g h t ⟨j,hj⟩)
    (_exactPin : pinExact i j m e f g h t hi hj)
    (d0 : (d2Set i j m e f g h t 0).card≤4)
    (d2i : (d2Set i j m e f g h t ⟨i,hi⟩).card≤4)
    (d2j : (d2Set i j m e f g h t ⟨j,hj⟩).card≤4)
    (d12 : (d2Set i j m e f g h t 12).card≤4)
    (_d13 : (d2Set i j m e f g h t 13).card≤4) :
    Spanning i j m e f g h t ∨ Exceptional i j m e f g h t := by
  let data := (sites i j).map m
  have m_eq : decode i j data = m := decode_full i j m h0 h12 holes
  have length_eq : data.length=(sites i j).length := List.length_map _
  have length_ok : 4≤data.length := length_eq.symm ▸ enough
  have ds : ∃ a b c d tail, data=a::b::c::d::tail ∧ tail.length=(sites i j).length-4 := by
    match q : data with
    | [] => simp [q] at length_ok
    | a::[] => simp [q] at length_ok
    | a::b::[] => simp [q] at length_ok
    | a::b::c::[] => simp [q] at length_ok
    | a::b::c::d::tail =>
      refine ⟨a,b,c,d,tail,rfl,?_⟩
      simp only [q,List.length_cons] at length_eq
      omega
  obtain ⟨a,b,c,d,tail,ds,lt⟩ := ds
  have mt : tail∈allDigits ((sites i j).length-4) := lt ▸ mem_allDigits tail
  have A := List.all_eq_true.mp (show Shard i j hi hj a b c d from tabs a b c d) tail mt
  have base0 : (d2Set i j m false false false false false 0).card≤4 :=
    (card_le_card (baseD2_subset i j ip sep jp m e f g h t 0 (.inl rfl))).trans d0
  have base12 : (d2Set i j m false false false false false 12).card≤4 :=
    (card_le_card (baseD2_subset i j ip sep jp m e f g h t 12 (.inr rfl))).trans d12
  have games : (allBits 5).all (evalModel i j hi hj data)=true := by
    rw [←ds] at A
    simpa only [m_eq,if_pos (And.intro LEFT (And.intro RIGHT (And.intro base0 base12)))] using A
  let flags : List Bool := [e,f,g,h,t]
  have fm : flags∈allBits 5 := mem_allBits flags
  have V := List.all_eq_true.mp games flags fm
  have checks : admissible i j m e f g h t hi hj=true := by
    simp [admissible,di,dj,d0,d2i,d2j,d12]
  have V' : (hasPath i j m e f g h t || exceptionB i j m f g h t)=true := by
    simpa [evalModel,flags,m_eq,checks] using V
  simp only [Bool.or_eq_true] at V'
  exact V'.elim (fun a => Or.inl (hasPath_sound a)) (fun a => Or.inr (exceptionB_sound a))

#print axioms checked
end FourOrder14One
