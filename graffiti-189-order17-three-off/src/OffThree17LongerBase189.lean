import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffThree17Longer
open Finset

abbrev Marks := Fin 13→Fin 3
abbrev Vertex := Fin 17

def dir (i j : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤13) ||
  decide (14≤a ∧ a<b) ||
  decide ((a=i ∨ a=j) ∧ (b=14 ∨ b=15)) ||
  (if q : a=0 ∧ 1≤b ∧ b≤13 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=13 ∧ a<13 then decide (m ⟨a,q.2⟩=2) else false)

def edge (i j : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  dir i j m u v || dir i j m v u

def d2Set (i j : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j m u v=true ∧
    ∃ w : Vertex, edge i j m u w=true ∧ edge i j m w v=true

def witness (i j : ℕ) (v : Vertex) : List Vertex :=
  if v.val=0 ∨ v.val=13 then List.finRange 17
  else if v.val<13 then [Fin.ofNat' 17 (v.val-1),Fin.ofNat' 17 (v.val+1),0,13]
  else [Fin.ofNat' 17 i,Fin.ofNat' 17 j]

def fast (i j : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j m u v=true ∧
    (witness i j v).any (fun w => edge i j m u w && edge i j m w v)=true

theorem fast_sub (i j : ℕ) (m : Marks) (u : Vertex) :
    fast i j m u⊆d2Set i j m u := by
  intro v vm
  obtain ⟨_,ne,no,mem⟩ := mem_filter.mp vm
  obtain ⟨w,_,wyes⟩ := List.any_eq_true.mp mem
  simp only [Bool.and_eq_true] at wyes
  exact mem_filter.mpr ⟨mem_univ _,ne,no,w,wyes.1,wyes.2⟩

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def Hole (i j k : ℕ) : Prop := k≠0 ∧ k≠12 ∧ (k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j)

instance (i j k : ℕ) : Decidable (Hole i j k) := by unfold Hole; infer_instance

def sites (i j : ℕ) : List (Fin 13) :=
  (List.finRange 13).filter (fun k => decide (k.val≠0 ∧ k.val≠12 ∧ ¬Hole i j k.val))

def pick : List (Fin 13) → List (Fin 3) → Fin 13 → Fin 3
  | a::as,b::bs,k => if k=a then b else pick as bs k
  | _,_,_ => 0

theorem pick_map {m : Marks} {L : List (Fin 13)} {k : Fin 13} (H : k∈L) :
    pick L (L.map m) k = m k := by
  induction L with
  | nil => simp at H
  | cons a l ih =>
    by_cases eq : k=a
    · simp [pick,eq]
    · simp [pick,eq,ih ((List.mem_cons.mp H).resolve_left eq)]

def decode (i j : ℕ) (d : List (Fin 3)) (k : Fin 13) : Fin 3 :=
  if k.val=0 then 1 else if k.val=12 then 2
  else if Hole i j k.val then 0 else pick (sites i j) d k

theorem decode_full (i j : ℕ) (m : Marks) (h0 : m 0=1) (h11 : m 12=2)
    (holes : ∀ k : Fin 13, Hole i j k.val → m k=0) :
    decode i j ((sites i j).map m) = m := by
  funext k
  unfold decode
  split
  next H =>
    have eq : k=(0:Fin 13) := Fin.ext H
    simpa only [eq] using h0.symm
  next H =>
    split
    next J =>
      have eq : k=(12:Fin 13) := Fin.ext J
      simpa only [eq] using h11.symm
    next J =>
      split
      next K => exact (holes k K).symm
      next K =>
        apply pick_map
        have H' : k≠0 := fun e => H (congrArg Fin.val e)
        simp [sites,H,H',J,K]


def words : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => (words n).flatMap (fun l => [0::l,1::l,2::l])

theorem words_mem (l : List (Fin 3)) : l∈words l.length := by
  induction l with
  | nil => simp [words]
  | cons x l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨l,ih,?_⟩
    fin_cases x <;> simp

def Chain (i j : ℕ) (m : Marks) (l : List Vertex) : Prop :=
  l.length=15 ∧ l.Nodup ∧ l.Chain' (fun a b => edge i j m a b=true)

instance (i j : ℕ) (m : Marks) (l : List Vertex) : Decidable (Chain i j m l) := by
  unfold Chain
  infer_instance

def pool (i j : ℕ) : List (List Vertex) :=
  if i=2 ∧ j=5 then [[0,1,2,14,16,15,5,6,7,8,9,10,11,12,13]]
  else
  if i=2 ∧ j=6 then [[0,1,2,3,4,13,11,10,9,8,7,6,14,15,16],[0,1,2,3,13,12,11,10,9,8,7,6,14,15,16]]
  else
  if i=2 ∧ j=7 then [[0,1,2,3,4,13,12,11,10,9,8,7,14,15,16],[0,5,4,3,2,14,16,15,7,8,9,10,11,12,13]]
  else
  if i=2 ∧ j=8 then [[0,6,5,4,3,2,14,16,15,8,9,10,11,12,13],[0,1,2,3,4,5,13,12,11,10,9,8,14,15,16],[0,7,6,5,4,3,2,14,15,8,9,10,11,12,13]]
  else
  if i=2 ∧ j=9 then [[0,1,2,14,9,8,7,6,5,4,3,13,12,11,10],[0,1,2,3,4,5,6,7,13,11,10,9,14,15,16],[0,1,2,14,15,9,8,7,6,5,4,13,10,11,12],[0,1,2,3,4,5,6,13,12,11,10,9,14,15,16]]
  else
  if i=2 ∧ j=10 then [[0,1,2,14,10,9,8,7,6,5,4,3,13,11,12],[0,1,2,3,4,5,6,7,13,12,11,10,14,15,16],[0,1,2,3,4,13,5,6,7,8,9,10,14,15,16]]
  else
  if i=2 ∧ j=11 then [[0,1,2,3,4,5,6,7,8,9,10,11,14,15,16]]
  else
  if i=3 ∧ j=6 then [[0,1,2,3,14,16,15,6,7,8,9,10,11,12,13]]
  else
  if i=3 ∧ j=7 then [[0,1,2,3,4,5,13,11,10,9,8,7,14,15,16],[0,6,5,4,3,14,16,15,7,8,9,10,11,12,13],[0,1,2,3,4,13,12,11,10,9,8,7,14,15,16]]
  else
  if i=3 ∧ j=8 then [[1,0,6,5,4,3,14,16,15,8,9,10,11,12,13],[0,1,2,3,4,5,13,12,11,10,9,8,14,15,16],[0,7,6,5,4,3,14,16,15,8,9,10,11,12,13]]
  else
  if i=3 ∧ j=9 then [[0,1,2,3,14,9,8,7,6,5,4,13,12,11,10],[0,1,2,3,4,5,6,7,13,12,11,10,9,14,15],[0,1,13,11,10,9,8,7,6,5,4,3,14,15,16],[0,1,2,3,14,15,9,8,7,6,5,13,10,11,12],[0,1,2,3,4,5,6,13,12,11,10,9,14,15,16]]
  else
  if i=3 ∧ j=10 then [[0,1,2,3,4,13,5,6,7,8,9,10,14,15,16],[0,1,2,3,4,5,6,7,13,12,11,10,14,15,16],[0,1,2,3,4,5,13,6,7,8,9,10,14,15,16],[0,1,2,3,14,10,9,8,7,6,5,4,13,11,12]]
  else
  if i=4 ∧ j=7 then [[0,1,2,3,4,14,16,15,7,8,9,10,11,12,13]]
  else
  if i=4 ∧ j=8 then [[1,0,7,6,5,4,14,16,15,8,9,10,11,12,13],[0,1,2,3,4,5,6,13,11,10,9,8,14,15,16],[1,2,0,6,5,4,14,16,15,8,9,10,11,12,13],[0,1,2,3,4,5,13,12,11,10,9,8,14,15,16]]
  else
  if i=4 ∧ j=9 then [[0,1,2,3,4,5,6,13,12,11,10,9,14,15,16],[0,1,2,13,12,11,10,9,8,7,6,5,4,14,15],[0,1,2,3,4,14,9,8,7,6,5,13,10,11,12],[0,1,2,3,4,5,6,7,13,12,11,10,9,14,15],[0,1,13,12,11,10,9,8,7,6,5,4,14,15,16]]
  else
  if i=5 ∧ j=8 then [[0,1,2,3,4,5,14,16,15,8,9,10,11,12,13]]
  else
  []


def hasLonger (i j : ℕ) (m : Marks) : Bool :=
  (pool i j).any (fun l => decide (Chain i j m l))

def gate (i j : ℕ) (d : List (Fin 3)) : Bool :=
  let m := decode i j d
  !(decide (4≤markCount m 1 ∧ 4≤markCount m 2) &&
    decide ((fast i j m 0).card≤4 ∧ (fast i j m 13).card≤4)) || hasLonger i j m

def row (i j : ℕ) : Bool := (words (sites i j).length).all (gate i j)

theorem row_sound {i j : ℕ} {m : Marks} (h : row i j=true)
    (h0 : m 0=1) (h12 : m 12=2) (holes : ∀ k : Fin 13,Hole i j k.val → m k=0)
    (cl : 4≤markCount m 1) (cr : 4≤markCount m 2)
    (dl : (d2Set i j m 0).card≤4) (dr : (d2Set i j m 13).card≤4) :
    ∃ l, Chain i j m l := by
  let d := (sites i j).map m
  have dm : d∈words (sites i j).length := by
    have q := words_mem d
    simpa [d] using q
  have g := List.all_eq_true.mp h d dm
  have eq := decode_full i j m h0 h12 holes
  have fl := (card_le_card (fast_sub i j m 0)).trans dl
  have fr := (card_le_card (fast_sub i j m 13)).trans dr
  have yes : hasLonger i j m=true := by simpa [gate, d, eq, cl, cr, fl, fr] using g
  obtain ⟨l,_,lq⟩ := List.any_eq_true.mp yes
  exact ⟨l,of_decide_eq_true lq⟩

#print axioms row_sound
end OffThree17Longer
