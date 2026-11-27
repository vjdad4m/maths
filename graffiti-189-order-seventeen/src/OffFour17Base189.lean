import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffFour17
open Finset
abbrev Marks := Fin 12 → Fin 3
abbrev Label := Fin 17

/-- 0 = clique, distinct single carriers 15 and 16.
1 or 2 = star center 16 dual-pinned, extra carrier 15 at i or j.
3 = dual triangle 13,14,15 and disjoint dual singleton 16. -/
def attach (t i j k l a b : ℕ) : Prop :=
  if t=0 then (a=i ∧ b=15) ∨ (a=j ∧ b=16)
  else if t=1 ∨ t=2 then
    ((a=i ∨ a=j) ∧ b=16) ∨ (b=15 ∧ ((t=1 ∧ a=i) ∨ (t=2 ∧ a=j)))
  else ((a=i ∨ a=j) ∧ 13 ≤ b ∧ b ≤ 15) ∨ ((a=k ∨ a=l) ∧ b=16)

instance (t i j k l a b : ℕ) : Decidable (attach t i j k l a b) := by
  unfold attach
  infer_instance

def core (t a b : ℕ) : Prop :=
  13 ≤ a ∧ a<b ∧ (if t=0 then True else if t=3 then b ≤ 15 else b=16)

instance (t a b : ℕ) : Decidable (core t a b) := by
  unfold core
  infer_instance

def dir (t i j k l : ℕ) (m : Marks) (u v : Label) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b ≤ 12) || decide (core t a b) || decide (attach t i j k l a b) ||
  (if h : a=0 ∧ 1 ≤ b ∧ b ≤ 12 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if h : b=12 ∧ a<12 then decide (m ⟨a,h.2⟩=2) else false)

def edge (t i j k l : ℕ) (m : Marks) (u v : Label) : Bool :=
  dir t i j k l m u v || dir t i j k l m v u

def two (t i j k l : ℕ) (m : Marks) (u : Label) : Finset Label :=
  univ.filter fun v=>v≠u ∧ !edge t i j k l m u v=true ∧
    ∃ w : Label,edge t i j k l m u w=true ∧ edge t i j k l m w v=true

def mids (i j k l : ℕ) (v : Label) : List Label :=
  if v.val=0 ∨ v.val=12 then List.finRange 17
  else if v.val<12 then [Fin.ofNat' 17 (v.val-1),Fin.ofNat' 17 (v.val+1),0,12]
  else [Fin.ofNat' 17 i,Fin.ofNat' 17 j,Fin.ofNat' 17 k,Fin.ofNat' 17 l]

def fast (t i j k l : ℕ) (m : Marks) (u : Label) : Finset Label :=
  univ.filter fun v=>v≠u ∧ !edge t i j k l m u v=true ∧
    (mids i j k l v).any (fun w=>edge t i j k l m u w && edge t i j k l m w v)=true

theorem fast_sub (t i j k l : ℕ) (m : Marks) (u : Label) :
    fast t i j k l m u⊆two t i j k l m u := by
  intro v vm
  obtain ⟨_,ne,no,mem⟩ := mem_filter.mp vm
  obtain ⟨w,_,wh⟩ := List.any_eq_true.mp mem
  simp only [Bool.and_eq_true] at wh
  exact mem_filter.mpr ⟨mem_univ _,ne,no,w,wh.1,wh.2⟩

def count (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k=>m k=c).card

def hole (i j k : ℕ) : Prop := k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j
instance (i j k : ℕ) : Decidable (hole i j k) := by unfold hole; infer_instance

def valid (t i j k : ℕ) (c : Fin 3) : Prop :=
  (c=1 → k≠i ∧ k≠j) ∧ (c=2 → k+1≠i ∧ k+1≠j) ∧ (t≠0 → hole i j k → c=0)

instance (t i j k : ℕ) (c : Fin 3) : Decidable (valid t i j k c) := by
  unfold valid
  infer_instance

def choices (t i j k : ℕ) : List (Fin 3) :=
  (List.finRange 3).filter fun c=>decide (valid t i j k c)

def words (t i j : ℕ) : List ℕ → List (List (Fin 3))
  | [] => [[]]
  | a::l => (choices t i j a).flatMap fun v => (words t i j l).map (v::·)

theorem words_mem (t i j : ℕ) (m : Marks) (L : List (Fin 12))
    (ok : ∀ k∈L,valid t i j k.val (m k)) : L.map m∈words t i j (L.map Fin.val) := by
  induction L with
  | nil => simp [words]
  | cons k l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨m k,?_,?_⟩
    · simp [choices,ok k (by simp)]
    · exact List.mem_map.mpr ⟨l.map m,ih (fun i hi=>ok i (by simp [hi])),rfl⟩

def interior (t i j : ℕ) : Prop := t≠0 ∧ 2≤i ∧ i+3≤j ∧ j≤10
instance (t i j : ℕ) : Decidable (interior t i j) := by unfold interior; infer_instance

def rowValid (t i j k : ℕ) (c : Fin 3) : Prop :=
  valid t i j k c ∧ (interior t i j → ¬hole i j k → c≠0)
instance (t i j k : ℕ) (c : Fin 3) : Decidable (rowValid t i j k c) := by
  unfold rowValid
  infer_instance

def rowChoices (t i j k : ℕ) : List (Fin 3) :=
  (List.finRange 3).filter fun c=>decide (rowValid t i j k c)

def rowWords (t i j : ℕ) : List ℕ → List (List (Fin 3))
  | [] => [[]]
  | a::l => (rowChoices t i j a).flatMap fun v => (rowWords t i j l).map (v::·)

theorem row_words_mem (t i j : ℕ) (m : Marks) (L : List (Fin 12))
    (ok : ∀ k∈L,rowValid t i j k.val (m k)) :
    L.map m∈rowWords t i j (L.map Fin.val) := by
  induction L with
  | nil => simp [rowWords]
  | cons k l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨m k,?_,?_⟩
    · simp [rowChoices,ok k (by simp)]
    · exact List.mem_map.mpr ⟨l.map m,ih (fun i hi=>ok i (by simp [hi])),rfl⟩

private theorem zeros_card_le_four (m : Marks)
    (cl : 4≤count m 1) (cr : 4≤count m 2) :
    (univ.filter fun k => m k=0).card≤4 := by
  let Z := univ.filter (fun k : Fin 12 => m k=0)
  let A := univ.filter (fun k : Fin 12 => m k=1)
  let B := univ.filter (fun k : Fin 12 => m k=2)
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    have h1 : m a = 1 := (mem_filter.mp ha).2
    have h2 : m a = 2 := (mem_filter.mp hb).2
    rw [h1] at h2
    contradiction
  have hZ : Disjoint Z (A∪B) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hab
    have h0 : m a = 0 := (mem_filter.mp ha).2
    rcases mem_union.mp hab with h|h
    · have h1 : m a = 1 := (mem_filter.mp h).2
      rw [h0] at h1
      contradiction
    · have h2 : m a = 2 := (mem_filter.mp h).2
      rw [h0] at h2
      contradiction
  have hbound := card_le_card (subset_univ (Z∪(A∪B)))
  rw [card_union_of_disjoint hZ,card_union_of_disjoint hAB,card_univ,Fintype.card_fin] at hbound
  change 4≤A.card at cl
  change 4≤B.card at cr
  change Z.card≤4
  omega

theorem row_valid_of_counts {t i j : ℕ} {m : Marks}
    (all : ∀ r : Fin 12,valid t i j r.val (m r))
    (cl : 4≤count m 1) (cr : 4≤count m 2) (r : Fin 12) :
    rowValid t i j r.val (m r) := by
  refine ⟨all r,?_⟩
  rintro ⟨nt,il,gap,jh⟩ nr mr
  let a : Fin 12 := ⟨i-1,by omega⟩
  let b : Fin 12 := ⟨i,by omega⟩
  let c : Fin 12 := ⟨j-1,by omega⟩
  let d : Fin 12 := ⟨j,by omega⟩
  have ha : hole i j a.val := .inl rfl
  have hb : hole i j b.val := .inr (.inl rfl)
  have hc : hole i j c.val := .inr (.inr (.inl rfl))
  have hd : hole i j d.val := .inr (.inr (.inr rfl))
  have zero (k : Fin 12) (hk : hole i j k.val) : m k=0 := (all k).2.2 nt hk
  have hra : r≠a := fun h => nr (h.symm ▸ ha)
  have hrb : r≠b := fun h => nr (h.symm ▸ hb)
  have hrc : r≠c := fun h => nr (h.symm ▸ hc)
  have hrd : r≠d := fun h => nr (h.symm ▸ hd)
  have hab : a≠b := by intro e; have e' := congrArg Fin.val e; dsimp [a,b] at e'; omega
  have hac : a≠c := by intro e; have e' := congrArg Fin.val e; dsimp [a,c] at e'; omega
  have had : a≠d := by intro e; have e' := congrArg Fin.val e; dsimp [a,d] at e'; omega
  have hbc : b≠c := by intro e; have e' := congrArg Fin.val e; dsimp [b,c] at e'; omega
  have hbd : b≠d := by intro e; have e' := congrArg Fin.val e; dsimp [b,d] at e'; omega
  have hcd : c≠d := by intro e; have e' := congrArg Fin.val e; dsimp [c,d] at e'; omega
  let S : Finset (Fin 12) := {r,a,b,c,d}
  have hS : S.card=5 := by
    simp [S,card_insert_of_not_mem,hra,hrb,hrc,hrd,hab,hac,had,hbc,hbd,hcd]
  have inc : S ⊆ univ.filter (fun k => m k=0) := by
    intro k hk
    have key : k=r ∨ k=a ∨ k=b ∨ k=c ∨ k=d := by simpa [S] using hk
    rcases key with rfl|rfl|rfl|rfl|rfl <;> simp [mr,zero _ ha,zero _ hb,zero _ hc,zero _ hd]
  have h := (card_le_card inc).trans (zeros_card_le_four m cl cr)
  omega

def sites : List (Fin 12) := (List.finRange 12).filter fun k=>decide (k.val≠0 ∧ k.val≠11)

def decode (d : List (Fin 3)) (k : Fin 12) : Fin 3 :=
  if k.val=0 then 1 else if k.val=11 then 2 else d[k.val-1]?.getD 0

theorem decode_exact (m : Marks) (lo : m 0=1) (hi : m 11=2) : decode (sites.map m)=m := by
  funext k
  fin_cases k <;> first | exact lo.symm | exact hi.symm | rfl

def sideValid (t k l : ℕ) (m : Marks) : Prop :=
  t=3 → ∀ s : Fin 12, (m s=1 → s.val≠k ∧ s.val≠l) ∧
    (m s=2 → s.val+1≠k ∧ s.val+1≠l)

instance (t k l : ℕ) (m : Marks) : Decidable (sideValid t k l m) := by
  unfold sideValid
  infer_instance

def extra (t i j : ℕ) : List (ℕ×ℕ) :=
  if t=3 then
    (List.range' 1 11).flatMap fun k =>
      ((List.range' 1 11).filter (fun l=>decide (k+3 ≤ l ∧ k≠i ∧ k≠j ∧ l≠i ∧ l≠j))).map (k,·)
  else [(0,0)]

theorem extra_disc {i j k l : ℕ}
    (kp : 1 ≤ k) (lt : k+3 ≤ l) (lr : l ≤ 11)
    (ki : k≠i) (kj : k≠j) (li : l≠i) (lj : l≠j) : (k,l)∈extra 3 i j := by
  simp only [extra,if_pos rfl]
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_range'_1.mpr ⟨kp,by omega⟩,?_⟩
  apply List.mem_map.mpr
  exact ⟨l,List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨by omega,by omega⟩,
    decide_eq_true ⟨lt,ki,kj,li,lj⟩⟩,rfl⟩

def longer (t i j k l : ℕ) (m : Marks) (L : List Label) : Prop :=
  L.length=14 ∧ L.Nodup ∧ L.Chain' (fun x y=>edge t i j k l m x y=true)

instance (t i j k l : ℕ) (m : Marks) (L : List Label) : Decidable (longer t i j k l m L) := by
  unfold longer
  infer_instance

def pool (t i j : ℕ) : List (List Label) :=
  if t=0 ∧ i=4 ∧ j=7 then [[0,1,2,3,4,15,13,14,16,7,8,9,10,11]]
  else
  if t=0 ∧ i=4 ∧ j=8 then [[0,1,2,3,4,15,13,14,16,8,9,10,11,12]]
  else
  if t=1 ∧ i=2 ∧ j=5 then [[0,1,2,3,12,11,10,9,8,7,6,5,16,13]]
  else
  if t=2 ∧ i=2 ∧ j=5 then [[0,1,2,3,12,10,9,8,7,6,5,15,16,13]]
  else
  if t=1 ∧ i=2 ∧ j=6 then [[0,1,2,3,4,12,11,10,9,8,7,6,16,13]]
  else
  if t=2 ∧ i=2 ∧ j=6 then [[0,1,2,3,4,12,10,9,8,7,6,15,16,13]]
  else
  if t=1 ∧ i=2 ∧ j=7 then [[0,1,2,3,4,5,12,11,10,9,8,7,16,13],[0,6,5,4,3,2,15,16,7,8,9,10,11,12]]
  else
  if t=2 ∧ i=2 ∧ j=7 then [[0,1,2,3,4,5,12,11,10,9,8,7,15,16],[0,6,5,4,3,2,16,15,7,8,9,10,11,12]]
  else
  if t=1 ∧ i=2 ∧ j=8 then [[0,1,2,15,16,8,7,6,5,4,3,12,9,10],[0,1,2,3,4,5,6,12,11,10,9,8,16,13]]
  else
  if t=2 ∧ i=2 ∧ j=8 then [[0,1,2,16,8,7,6,5,4,3,12,9,10,11],[0,1,2,3,4,5,6,12,10,9,8,15,16,13]]
  else
  if t=1 ∧ i=2 ∧ j=9 then [[0,1,2,15,16,9,8,7,6,5,4,3,12,10],[0,1,2,3,4,5,6,7,12,11,10,9,16,13]]
  else
  if t=2 ∧ i=2 ∧ j=9 then [[0,1,2,3,12,4,5,6,7,8,9,15,16,13],[0,1,2,3,4,5,6,7,12,10,9,15,16,13]]
  else
  if t=1 ∧ i=2 ∧ j=10 then [[0,1,2,3,4,12,5,6,7,8,9,10,16,13],[0,1,2,3,4,5,6,7,8,12,11,10,16,13]]
  else
  if t=2 ∧ i=2 ∧ j=10 then [[0,1,2,3,4,5,6,7,8,9,10,15,16,13]]
  else
  if t=1 ∧ i=3 ∧ j=6 then [[0,1,2,3,4,12,11,10,9,8,7,6,16,13]]
  else
  if t=2 ∧ i=3 ∧ j=6 then [[0,1,2,3,4,12,10,9,8,7,6,15,16,13]]
  else
  if t=1 ∧ i=3 ∧ j=7 then [[0,1,2,3,4,5,12,11,10,9,8,7,16,13],[1,0,6,5,4,3,15,16,7,8,9,10,11,12]]
  else
  if t=2 ∧ i=3 ∧ j=7 then [[0,1,2,3,4,5,12,10,9,8,7,15,16,13],[1,0,6,5,4,3,16,15,7,8,9,10,11,12]]
  else
  if t=1 ∧ i=3 ∧ j=8 then [[0,1,2,3,4,5,6,12,11,10,9,8,16,13],[0,1,12,10,9,8,7,6,5,4,3,15,16,13],[0,1,2,3,15,16,8,7,6,5,4,12,9,10]]
  else
  if t=2 ∧ i=3 ∧ j=8 then [[0,1,2,3,4,5,6,12,11,10,9,8,15,16],[0,1,12,11,10,9,8,7,6,5,4,3,16,13],[0,1,2,3,16,8,7,6,5,4,12,9,10,11]]
  else
  if t=1 ∧ i=3 ∧ j=9 then [[0,1,2,3,15,16,9,8,7,6,5,4,12,10],[0,1,2,3,4,5,6,7,12,11,10,9,16,13]]
  else
  if t=2 ∧ i=3 ∧ j=9 then [[0,1,2,3,4,12,5,6,7,8,9,15,16,13],[0,1,2,3,4,5,6,7,12,10,9,15,16,13]]
  else
  if t=1 ∧ i=4 ∧ j=7 then [[0,1,2,3,4,5,12,11,10,9,8,7,16,13],[1,2,0,6,5,4,15,16,7,8,9,10,11,12]]
  else
  if t=2 ∧ i=4 ∧ j=7 then [[0,1,2,3,4,5,12,10,9,8,7,15,16,13],[1,2,0,6,5,4,16,15,7,8,9,10,11,12]]
  else
  if t=1 ∧ i=4 ∧ j=8 then [[0,1,2,3,4,5,6,12,11,10,9,8,16,13],[0,1,2,12,10,9,8,7,6,5,4,15,16,13],[0,1,2,3,4,15,16,8,7,6,5,12,9,10]]
  else
  if t=2 ∧ i=4 ∧ j=8 then [[0,1,2,3,4,5,6,12,10,9,8,15,16,13],[0,1,2,12,11,10,9,8,7,6,5,4,16,13],[0,1,2,3,4,5,12,11,10,9,8,15,16,13]]
  else
  if t=3 ∧ i=3 ∧ j=7 then [[0,1,2,16,6,5,4,3,13,7,8,9,10,11],[0,5,6,7,13,14,3,2,16,8,9,10,11,12]]
  else
  if t=3 ∧ i=3 ∧ j=8 then [[0,1,2,3,13,8,7,6,5,4,12,9,10,11]]
  else
  if t=3 ∧ i=3 ∧ j=9 then [[0,1,2,3,4,12,5,6,7,8,9,13,14,15]]
  else
  if t=3 ∧ i=4 ∧ j=7 then [[0,1,2,3,4,13,14,15,7,8,9,10,11,12]]
  else
  if t=3 ∧ i=4 ∧ j=8 then [[0,1,2,3,4,5,12,11,10,9,8,13,14,15]]
  else
  []

def gate (t i j k l : ℕ) (m : Marks) : Bool :=
  !(decide (sideValid t k l m) &&
    decide ((fast t i j k l m 0).card ≤ 4 ∧ (fast t i j k l m 12).card ≤ 4)) ||
  (pool t i j).any (fun L=>decide (longer t i j k l m L))

def row (t i j : ℕ) : Bool :=
  (rowWords t i j (sites.map Fin.val)).all (fun d =>
    let m := decode d
    if 4 ≤ count m 1 ∧ 4 ≤ count m 2 then
      (extra t i j).all (fun q=>gate t i j q.1 q.2 m)
    else true)

theorem row_sound {t i j k l : ℕ} {m : Marks} (h : row t i j=true)
    (ext : (k,l)∈extra t i j) (m0 : m 0=1) (m11 : m 11=2)
    (valid : ∀ r : Fin 12,valid t i j r.val (m r))
    (side : sideValid t k l m)
    (cl : 4 ≤ count m 1) (cr : 4 ≤ count m 2)
    (dl : (two t i j k l m 0).card ≤ 4) (dr : (two t i j k l m 12).card ≤ 4) :
    ∃ L,longer t i j k l m L := by
  have c := List.all_eq_true.mp h (sites.map m) (row_words_mem t i j m sites (fun k _=>row_valid_of_counts valid cl cr k))
  have e : (extra t i j).all (fun q=>gate t i j q.1 q.2 m)=true := by
    simpa [decode_exact m m0 m11,cl,cr] using c
  have g := List.all_eq_true.mp e (k,l) ext
  have fl := (card_le_card (fast_sub t i j k l m 0)).trans dl
  have fr := (card_le_card (fast_sub t i j k l m 12)).trans dr
  have a : (pool t i j).any (fun L=>decide (longer t i j k l m L))=true := by
    simpa [gate,side,fl,fr] using g
  obtain ⟨L,_,lp⟩ := List.any_eq_true.mp a
  exact ⟨L,of_decide_eq_true lp⟩

#print axioms row_sound
end OffFour17
