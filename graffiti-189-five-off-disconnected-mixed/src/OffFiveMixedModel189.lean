import FourOffTwinModel189
import Mathlib.Tactic.NormNum

namespace OffFive16DisconnectedMixed
open Finset
abbrev Marks := Fin 10 → Fin 3
abbrev Vertex := Fin 13

def dir (m : Marks) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤10) ||
  decide ((a=1 ∨ a=8) ∧ b=11) ||
  decide ((a=2 ∨ a=9) ∧ b=12) ||
  (if h : a=0 ∧ 1≤b ∧ b≤10 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if h : b=10 ∧ a<10 then decide (m ⟨a,h.2⟩=2) else false)

def edge (m : Marks) (u v : Vertex) : Bool := dir m u v || dir m v u

def two (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge m u v=true ∧
    ∃ w : Vertex, edge m u w=true ∧ edge m w v=true

def count (m : Marks) (c : Fin 3) : ℕ :=
  (univ.filter fun k => m k=c).card

def decode (d : List (Fin 3)) (k : Fin 10) : Fin 3 :=
  if k.val=0 then 1 else if k.val=9 then 2
  else if k.val=1 ∨ k.val=8 then 0 else d[k.val-2]?.getD 0

def code (m : Marks) : List (Fin 3) :=
  [m 2,m 3,m 4,m 5,m 6,m 7]

theorem decode_code (m : Marks) (h0 : m 0=1) (h9 : m 9=2)
    (h1 : m 1=0) (h8 : m 8=0) : decode (code m)=m := by
  funext k
  fin_cases k <;> norm_num [decode,code,h0,h9,h1,h8] <;>
    first | rfl | exact h8.symm | exact h9.symm

def A : Marks := decode [1,1,1,2,2,2]
def B : Marks := decode [2,2,2,1,1,1]

def allowed (d : List (Fin 3)) : Bool :=
  let m := decode d
  !(decide (count m 1=4 ∧ count m 2=4 ∧
    (two m 0).card≤4 ∧ (two m 10).card≤4 ∧
    (two m 11).card≤4 ∧ (two m 12).card≤4)) ||
  (decide (m=A ∨ m=B))

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
theorem all_codes : (OffFour16Twin.bitlists 6).all allowed=true := by decide +kernel

theorem classify (m : Marks) (h0 : m 0=1) (h9 : m 9=2)
    (h1 : m 1=0) (h8 : m 8=0) (hn : ∀ k : Fin 10,2≤k.val → k.val≤7 → m k≠0)
    (mc1 : count m 1=4) (mc2 : count m 2=4)
    (a0 : (two m 0).card≤4) (a10 : (two m 10).card≤4)
    (a11 : (two m 11).card≤4) (a12 : (two m 12).card≤4) :
    m=A ∨ m=B := by
  have nn : ∀ e∈code m,e≠0 := by
    intro e he
    simp only [code,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hn _ (by decide) (by decide)
  have d : code m∈OffFour16Twin.bitlists 6 := by
    have c := OffFour16Twin.mem_bitlists nn
    simpa [code] using c
  have t := List.all_eq_true.mp all_codes _ d
  simpa [allowed,decode_code m h0 h9 h1 h8,mc1,mc2,a0,a10,a11,a12] using t

#print axioms classify
end OffFive16DisconnectedMixed

namespace OffFive16DisconnectedMixed

def aPort : ℕ := 2
def bPort : ℕ := 5

def center_cap (m : Marks) : Prop := (two m 0).card=4 ∧ (two m 10).card=4

theorem a_cap : center_cap A := by unfold center_cap; decide +kernel
theorem b_cap : center_cap B := by unfold center_cap; decide +kernel

def othersSeeEnd (m : Marks) (r : ℕ) : Prop :=
  ∀ k : Fin 13,1≤k.val → k.val≤9 → k.val≠1 → k.val≠8 → k.val≠r →
    edge m 0 k=true ∨ edge m 10 k=true

theorem a_see : othersSeeEnd A aPort := by unfold othersSeeEnd; decide +kernel
theorem b_see : othersSeeEnd B bPort := by unfold othersSeeEnd; decide +kernel

def edgeFull (m : Marks) (r : ℕ) (v w : Fin 16) : Bool :=
  ((if p : v.val<13 ∧ w.val<13 then
    edge m ⟨v.val,p.1⟩ ⟨w.val,p.2⟩ else false) ||
    decide (12≤v.val ∧ 12≤w.val ∧ v≠w)) ||
    decide ((v.val=r ∧ 13≤w.val) ∨ (w.val=r ∧ 13≤v.val))

def pathA : List (Fin 16) := [0,1,11,8,7,6,5,4,3,2,13,14,15,12,9,10]
def pathB : List (Fin 16) := [0,1,2,3,4,10,9,12,13,14,15,5,6,7,8,11]

def FullPath (m : Marks) (r : ℕ) (l : List (Fin 16)) : Prop :=
  l.Nodup ∧ (∀ k : Fin 16,k∈l) ∧ l.Chain' (fun v w => edgeFull m r v w=true)

theorem a_path : FullPath A aPort pathA := by unfold FullPath; decide +kernel
theorem b_path : FullPath B bPort pathB := by unfold FullPath; decide +kernel

#print axioms a_cap
#print axioms b_cap
#print axioms a_see
#print axioms b_see
#print axioms a_path
#print axioms b_path

end OffFive16DisconnectedMixed
