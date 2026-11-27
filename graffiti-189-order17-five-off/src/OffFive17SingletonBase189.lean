import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffFive17Singleton
open Finset
abbrev Mark := Fin 11→Fin 3
abbrev Label := Fin 15

def pins (j k : ℕ) : Prop := k=1 ∨ k=j ∨ k=4 ∨ k=7
instance (j k : ℕ) : Decidable (pins j k) := by unfold pins; infer_instance

def dir (j : ℕ) (m : Mark) (u v : Label) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b ≤ 11) ||
  decide (((a=1 ∨ a=j) ∧ b=12) ∨ (a=4 ∧ b=13) ∨ (a=7 ∧ b=14)) ||
  (if q : a=0 ∧ 1 ≤ b ∧ b ≤ 11 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=11 ∧ a<11 then decide (m ⟨a,q.2⟩=2) else false)

def edge (j : ℕ) (m : Mark) (u v : Label) : Bool := dir j m u v || dir j m v u

def two (j : ℕ) (m : Mark) (u : Label) : Finset Label :=
  univ.filter fun v => v≠u ∧ !edge j m u v=true ∧
    ∃ w : Label, edge j m u w=true ∧ edge j m w v=true

def mids (j : ℕ) (v : Label) : List Label :=
  if v.val=0 ∨ v.val=11 then List.finRange 15
  else if v.val ≤ 11 then [Fin.ofNat' 15 (v.val-1),Fin.ofNat' 15 (v.val+1),0,11]
  else if v.val=12 then [1,Fin.ofNat' 15 j]
  else if v.val=13 then [4] else [7]

def fast (j : ℕ) (m : Mark) (u : Label) : Finset Label :=
  univ.filter fun v=>v≠u ∧ !edge j m u v=true ∧
    (mids j v).any (fun w=>edge j m u w && edge j m w v)=true

theorem fast_sub (j : ℕ) (m : Mark) (u : Label) : fast j m u⊆two j m u := by
  intro v vm
  obtain ⟨_,ne,no,m⟩ := mem_filter.mp vm
  obtain ⟨w,_,wh⟩ := List.any_eq_true.mp m
  simp only [Bool.and_eq_true] at wh
  exact mem_filter.mpr ⟨mem_univ _,ne,no,w,wh.1,wh.2⟩

def count (m : Mark) (c : Fin 3) : ℕ := (univ.filter fun k=>m k=c).card

def validMark (j k : ℕ) (v : Fin 3) : Prop :=
  (v=1 → ¬pins j k) ∧ (v=2 → ¬pins j (k+1))

instance (j k : ℕ) (v : Fin 3) : Decidable (validMark j k v) := by
  unfold validMark
  infer_instance

def choices (j k : ℕ) : List (Fin 3) := (List.finRange 3).filter fun v=>decide (validMark j k v)

def words (j : ℕ) : List ℕ→List (List (Fin 3))
  | [] => [[]]
  | k::ks => (choices j k).flatMap fun v => (words j ks).map (v::·)

theorem words_mem (j : ℕ) (m : Mark) (L : List (Fin 11))
    (ok : ∀ k∈L,validMark j k.val (m k)) :
    L.map m∈words j (L.map Fin.val) := by
  induction L with
  | nil => simp [words]
  | cons k l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨m k,?_,?_⟩
    · simp [choices,ok k (by simp)]
    · exact List.mem_map.mpr ⟨l.map m,ih (fun i hi=>ok i (by simp [hi])),rfl⟩

def sites : List (Fin 11) := (List.finRange 11).filter fun k=>decide (k.val≠0 ∧ k.val≠10)

def decode (d : List (Fin 3)) (k : Fin 11) : Fin 3 :=
  if k.val=0 then 1 else if k.val=10 then 2 else d[k.val-1]?.getD 0

theorem decode_exact (m : Mark) (lo : m 0=1) (hi : m 10=2) :
    decode (sites.map m)=m := by
  funext k
  fin_cases k <;> first | exact lo.symm | exact hi.symm | rfl

def gate (j : ℕ) (d : List (Fin 3)) : Bool :=
  let m := decode d
  !(decide (4 ≤ count m 1 ∧ 4 ≤ count m 2) &&
    decide ((fast j m 0).card ≤ 4 ∧ (fast j m 11).card ≤ 4))

def row (j : ℕ) : Bool := (words j (sites.map Fin.val)).all (gate j)

theorem row_sound {j : ℕ} {m : Mark} (h : row j=true)
    (m0 : m 0=1) (m10 : m 10=2)
    (valid : ∀ k : Fin 11,validMark j k.val (m k))
    (cl : 4 ≤ count m 1) (cr : 4 ≤ count m 2)
    (dl : (two j m 0).card ≤ 4) (dr : (two j m 11).card ≤ 4) : False := by
  have c := List.all_eq_true.mp h (sites.map m) (words_mem j m sites (fun k _=>valid k))
  have l := (card_le_card (fast_sub j m 0)).trans dl
  have r := (card_le_card (fast_sub j m 11)).trans dr
  simp [gate,decode_exact m m0 m10,cl,cr,l,r] at c

#print axioms row_sound
end OffFive17Singleton
