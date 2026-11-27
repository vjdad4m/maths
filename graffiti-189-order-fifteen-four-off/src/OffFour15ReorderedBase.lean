import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OffFour15
open Finset

abbrev Marks := Fin 10 → Fin 3
abbrev Vertex := Fin 15

def dir (i j x y : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤10) ||
  decide (11≤a ∧ a<b) ||
  decide (a=i ∧ 11≤b ∧ b<11+x) ||
  decide (a=j ∧ 11+x≤b ∧ b<11+x+y) ||
  (if q : a=0 ∧ 1≤b ∧ b≤10 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=10 ∧ a<10 then decide (m ⟨a,q.2⟩=2) else false)

def edge (i j x y : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  dir i j x y m u v || dir i j x y m v u

def d2Set (i j x y : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j x y m u v=true ∧
    ∃ w : Vertex, edge i j x y m u w=true ∧ edge i j x y m w v=true


def edgeWitnesses (i j : ℕ) (v : Vertex) : List Vertex :=
  if v.val=0 ∨ v.val=10 then List.finRange 15
  else if v.val<10 then [Fin.ofNat' 15 (v.val-1), Fin.ofNat' 15 (v.val+1)]
  else [Fin.ofNat' 15 i, Fin.ofNat' 15 j]

def fastD2Set (i j x y : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j x y m u v=true ∧
    (edgeWitnesses i j v).any (fun w => edge i j x y m u w && edge i j x y m w v)=true

theorem fastD2Set_subset (i j x y : ℕ) (m : Marks) (u : Vertex) :
    fastD2Set i j x y m u⊆d2Set i j x y m u := by
  intro v hv
  obtain ⟨_,vne,no,yes⟩ := mem_filter.mp hv
  obtain ⟨w,_,wyes⟩ := List.any_eq_true.mp yes
  simp only [Bool.and_eq_true] at wyes
  exact mem_filter.mpr ⟨mem_univ _,vne,no,w,wyes.1,wyes.2⟩

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def Hole (k s t : ℕ) := k=s ∨ k=t

instance (k s t : ℕ) : Decidable (Hole k s t) := by unfold Hole; infer_instance

def sites (s t : ℕ) : List (Fin 10) :=
  (List.finRange 10).filter (fun k => decide (k.val≠0 ∧ k.val≠9 ∧ ¬Hole k.val s t))

def pick : List (Fin 10) → List (Fin 3) → Fin 10 → Fin 3
  | a::as,b::bs,k => if k=a then b else pick as bs k
  | _,_,_ => 0

theorem pick_map {m : Marks} {L : List (Fin 10)} {k : Fin 10} (H : k∈L) :
    pick L (L.map m) k = m k := by
  induction L with
  | nil => simp at H
  | cons a l ih =>
    by_cases eq : k=a
    · simp [pick,eq]
    · simp [pick,eq,ih ((List.mem_cons.mp H).resolve_left eq)]

def decode (s t : ℕ) (d : List (Fin 3)) (k : Fin 10) : Fin 3 :=
  if k.val=0 then 1 else if k.val=9 then 2
  else if Hole k.val s t then 0 else pick (sites s t) d k

theorem decode_full (s t : ℕ) (m : Marks) (h0 : m 0=1) (h9 : m 9=2)
    (holes : ∀ k : Fin 10, Hole k.val s t → m k=0) :
    decode s t ((sites s t).map m) = m := by
  funext k
  unfold decode
  split
  next H =>
    have eq : k=(0:Fin 10) := Fin.ext H
    simpa only [eq] using h0.symm
  next H =>
    split
    next J =>
      have eq : k=(9:Fin 10) := Fin.ext J
      simpa only [eq] using h9.symm
    next J =>
      split
      next K => exact (holes k K).symm
      next K =>
        apply pick_map
        have H' : k≠0 := fun e => H (congrArg Fin.val e)
        simp [sites,H,H',J,K]

def bitlists : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => (bitlists n).flatMap (fun l => [1::l,2::l])

theorem mem_bitlists {l : List (Fin 3)} (h : ∀ k∈l,k≠0) :
    l∈bitlists l.length := by
  induction l with
  | nil => simp [bitlists]
  | cons a l ih =>
    have hl : l∈bitlists l.length := ih (fun k km => h _ (by simp [km]))
    have ha := h a (by simp)
    apply List.mem_flatMap.mpr
    refine ⟨l,hl,?_⟩
    fin_cases a <;> simp_all

structure Candidate where
  left : ℕ
  right : ℕ
  path : List Vertex

def pool : List Candidate := [
  ⟨1,5,[0,1,11,12,14,13,5,4,3,2,10,9,8,7,6]⟩,
  ⟨1,5,[0,1,11,12,13,14,5,4,3,2,10,9,8,7,6]⟩,
  ⟨1,6,[0,5,4,3,2,1,10,9,8,7,6,12,11,13,14]⟩,
  ⟨1,6,[0,5,4,3,2,1,11,12,14,13,6,7,8,9,10]⟩,
  ⟨1,6,[0,5,4,3,2,1,11,12,13,14,6,7,8,9,10]⟩,
  ⟨2,6,[1,0,5,4,3,2,11,12,14,13,6,7,8,9,10]⟩,
  ⟨2,6,[1,0,5,4,3,2,11,12,13,14,6,7,8,9,10]⟩,
  ⟨3,6,[1,2,0,5,4,3,11,12,14,13,6,7,8,9,10]⟩,
  ⟨3,6,[1,2,0,5,4,3,11,12,13,14,6,7,8,9,10]⟩,
  ⟨4,7,[0,1,2,3,4,11,12,14,13,7,6,5,10,8,9]⟩,
  ⟨4,7,[0,1,2,3,4,11,12,13,14,7,6,5,10,8,9]⟩,
  ⟨4,8,[0,1,2,3,4,11,12,14,13,8,7,6,5,10,9]⟩,
  ⟨4,8,[0,1,2,3,4,11,12,13,14,8,7,6,5,10,9]⟩,
  ⟨4,9,[0,1,2,3,4,5,6,10,7,8,9,12,11,13,14]⟩,
  ⟨4,9,[0,1,2,3,4,5,6,10,7,8,9,13,11,12,14]⟩,
  ⟨4,9,[0,1,2,3,4,5,6,10,7,8,9,14,11,12,13]⟩,
  ⟨5,9,[0,1,2,10,3,4,5,6,7,8,9,13,11,12,14]⟩,
  ⟨5,9,[0,1,2,10,3,4,5,6,7,8,9,14,11,12,13]⟩]

def Spanning (i j x y : ℕ) (m : Marks) : Prop :=
  ∃ l : List Vertex, l.Nodup ∧ (∀ k : Vertex,k∈l) ∧
    l.Chain' (fun u v => edge i j x y m u v=true)

def poolGood (l : List Vertex) : Bool :=
  decide l.Nodup && decide (∀ k : Vertex,k∈l)

theorem pool_valid : pool.all (fun c => poolGood c.path) = true := by decide +kernel

def hasPath (i j x y : ℕ) (m : Marks) : Bool :=
  pool.any fun c => decide (i=c.left ∧ j=c.right) &&
    decide (c.path.Chain' (fun u v => edge i j x y m u v=true))

theorem hasPath_sound {i j x y : ℕ} {m : Marks}
    (ok : hasPath i j x y m=true) : Spanning i j x y m := by
  obtain ⟨c,cm,cc⟩ := List.any_eq_true.mp ok
  have gc := List.all_eq_true.mp pool_valid c cm
  simp only [poolGood,Bool.and_eq_true,decide_eq_true_eq] at gc cc
  exact ⟨c.path,gc.1,gc.2,cc.2⟩

def PinsAllowed (i j : ℕ) (m : Marks) : Bool :=
  (List.finRange 10).all (fun k => decide
      (((k.val=i ∨ k.val=j) → m k≠1) ∧
       ((k.val+1=i ∨ k.val+1=j) → m k≠2)))


def validMarks (i j : ℕ) (m : Marks) : Bool :=
  decide (markCount m 1=4 ∧ markCount m 2=4) && PinsAllowed i j m

def populations : List (ℕ×ℕ) := [(1,2),(2,1),(1,3),(2,2),(3,1)]

def gate (i j x y : ℕ) (m : Marks) : Bool :=
  !(decide ((fastD2Set i j x y m 0).card≤4 ∧ (fastD2Set i j x y m 10).card≤4)) ||
    hasPath i j x y m

def part (i j s t : ℕ) : Bool :=
  (bitlists (sites s t).length).all (fun d =>
    let m := decode s t d
    !validMarks i j m || populations.all (fun (x,y) => gate i j x y m))

def fit (i j s t : ℕ) : Bool :=
  decide (1≤s ∧ s≤8 ∧ 1≤t ∧ t≤8 ∧ (s=i-1 ∨ s=j-1) ∧ (t=i ∨ t=j))

def row (i j : ℕ) : Bool :=
  [i-1,j-1].all fun s => [i,j].all fun t => !fit i j s t || part i j s t

theorem check_row {i j x y s t : ℕ} {m : Marks} (ok : row i j=true)
    (xs : (x,y)∈([(1,2),(2,1),(1,3),(2,2),(3,1)] : List (ℕ×ℕ)))
    (fs : fit i j s t=true) (h0 : m 0=1) (h9 : m 9=2)
    (holes : ∀ k : Fin 10, Hole k.val s t → m k=0)
    (med : ∀ k : Fin 10, ¬Hole k.val s t → m k≠0)
    (ml : markCount m 1=4) (mr : markCount m 2=4)
    (pallow : PinsAllowed i j m=true)
    (dleft : (d2Set i j x y m 0).card≤4)
    (dright : (d2Set i j x y m 10).card≤4) :
    Spanning i j x y m := by
  have F : 1≤s ∧ s≤8 ∧ 1≤t ∧ t≤8 ∧ (s=i-1 ∨ s=j-1) ∧ (t=i ∨ t=j) := by
    simpa only [fit,decide_eq_true_eq] using fs
  unfold row at ok
  have ss : s∈[i-1,j-1] := by simpa using F.2.2.2.2.1
  have tt : t∈[i,j] := by simpa using F.2.2.2.2.2
  have e := List.all_eq_true.mp (List.all_eq_true.mp ok s ss) t tt
  have q : part i j s t=true := by simpa [fs] using e
  let d := (sites s t).map m
  have dd : d∈bitlists (sites s t).length := by
    have a := mem_bitlists (l:=d) (by
      intro k hk
      obtain ⟨j,jm,rfl⟩ := List.mem_map.mp hk
      have hn : ¬Hole j.val s t := by
        have B := (List.mem_filter.mp jm).2
        exact (of_decide_eq_true B).2.2
      exact med j hn)
    simpa [d] using a
  have cb := List.all_eq_true.mp q d dd
  have eq : decode s t d=m := decode_full s t m h0 h9 holes
  have fastleft := (card_le_card (fastD2Set_subset i j x y m 0)).trans dleft
  have fastright := (card_le_card (fastD2Set_subset i j x y m 10)).trans dright
  have yes : validMarks i j m=true := by simp [validMarks,ml,mr,pallow]
  have pop : populations.all (fun (x,y) => gate i j x y m)=true := by
    simpa [eq,yes] using cb
  have cb' := List.all_eq_true.mp pop (x,y) (show (x,y)∈populations from xs)
  have hz : hasPath i j x y m=true := by
    simpa [gate,fastleft,fastright] using cb'
  exact hasPath_sound hz

end OffFour15
