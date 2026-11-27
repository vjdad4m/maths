import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace FourOrder14One
open Finset

abbrev Marks := Fin 12 → Fin 3
abbrev Vertex := Fin 14

def dir (i j : ℕ) (m : Marks) (e f g h t : Bool) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤12) ||
  decide ((a=i ∨ a=j) ∧ b=13) ||
  (if q : a=0 ∧ 1≤b ∧ b≤12 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=12 ∧ a<12 then decide (m ⟨a,q.2⟩=2) else false) ||
  (decide (a=i ∧ b=j) && e) ||
  (decide (a=i ∧ b=j-1) && f) ||
  (decide (j≠11 ∧ a=i ∧ b=j+1) && g) ||
  (decide (i≠1 ∧ a=i-1 ∧ b=j) && h) ||
  (decide (a=i+1 ∧ b=j) && t)

def edge (i j : ℕ) (m : Marks) (e f g h t : Bool) (u v : Vertex) : Bool :=
  dir i j m e f g h t u v || dir i j m e f g h t v u

def degree (i j : ℕ) (m : Marks) (e f g h t : Bool) (u : Vertex) : ℕ :=
  (univ.filter fun v => edge i j m e f g h t u v=true).card

def d2Set (i j : ℕ) (m : Marks) (e f g h t : Bool) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j m e f g h t u v = true ∧
    ∃ w : Vertex, edge i j m e f g h t u w=true ∧ edge i j m e f g h t w v=true

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def exceptionMarks (k : Fin 12) : Fin 3 :=
  if k.val≤2 ∨ k.val=5 then 1 else if k.val=6 ∨ 9≤k.val then 2 else 0

def Exceptional (i j : ℕ) (m : Marks) (_e f g h t : Bool) : Prop :=
  i=4 ∧ j=8 ∧ m=exceptionMarks ∧ f=true ∧ g=false ∧ h=false ∧ t=true

def Spanning (i j : ℕ) (m : Marks) (e f g h t : Bool) : Prop :=
  ∃ l : List Vertex, l.Nodup ∧ (∀ k : Vertex,k∈l) ∧
    l.Chain' (fun u v => edge i j m e f g h t u v=true)

def pinExact (i j : ℕ) (m : Marks) (e f g h t : Bool) (hi : i<14) (hj : j<14) : Prop :=
  ∀ v : Vertex, v.val≤12 →
    (edge i j m e f g h t ⟨i,hi⟩ v=true ∨ edge i j m e f g h t ⟨j,hj⟩ v=true) →
    v.val=i ∨ v.val=j ∨ v.val=i-1 ∨ v.val=i+1 ∨ v.val=j-1 ∨ v.val=j+1

noncomputable instance (i j : ℕ) (m : Marks) (e f g h t : Bool) (hi : i<14) (hj : j<14) :
    Decidable (pinExact i j m e f g h t hi hj) := by
  unfold pinExact
  infer_instance

def hole (i j k : ℕ) : Prop :=
  k=i ∨ k+1=j ∨ (i≠1 ∧ k+1=i) ∨ (j≠11 ∧ k=j)

instance (i j k : ℕ) : Decidable (hole i j k) := by unfold hole; infer_instance

def sites (i j : ℕ) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => decide (k.val≠0 ∧ k.val≠11 ∧ ¬hole i j k.val))

def pick : List (Fin 12) → List (Fin 3) → Fin 12 → Fin 3
  | a::as,b::bs,k => if k=a then b else pick as bs k
  | _,_,_ => 0

theorem pick_map {m : Marks} {L : List (Fin 12)} {k : Fin 12} (H : k∈L) :
    pick L (L.map m) k = m k := by
  induction L with
  | nil => simp at H
  | cons a l ih =>
    by_cases eq : k=a
    · simp [pick,eq]
    · simp [pick,eq,ih ((List.mem_cons.mp H).resolve_left eq)]

def decode (i j : ℕ) (d : List (Fin 3)) (k : Fin 12) : Fin 3 :=
  if k.val=0 then 1 else if k.val=11 then 2
  else if hole i j k.val then 0 else pick (sites i j) d k

theorem decode_full (i j : ℕ) (m : Marks) (h0 : m 0=1) (h11 : m 11=2)
    (holes : ∀ k : Fin 12, hole i j k.val → m k=0) :
    decode i j ((sites i j).map m) = m := by
  funext k
  unfold decode
  split
  next H =>
    have eq : k=(0:Fin 12) := Fin.ext H
    simpa only [eq] using h0.symm
  next H =>
    split
    next J =>
      have eq : k=(11:Fin 12) := Fin.ext J
      simpa only [eq] using h11.symm
    next J =>
      split
      next K => exact (holes k K).symm
      next K =>
        apply pick_map
        have H' : k≠0 := fun e => H (congrArg Fin.val e)
        simp [sites,H,H',J,K]

structure Candidate where
  left : ℕ
  right : ℕ
  path : List Vertex

def pool : List Candidate := [
  ⟨1,6,[12,11,10,9,8,7,6,13,1,2,3,4,5,0]⟩,
  ⟨1,7,[13,7,8,9,10,11,12,5,6,1,2,3,4,0]⟩,
  ⟨1,10,[12,11,10,13,1,2,3,4,5,6,7,8,9,0]⟩,
  ⟨1,11,[13,11,10,9,8,7,6,5,4,12,3,2,1,0]⟩,
  ⟨2,5,[6,7,8,9,10,11,12,3,4,5,13,2,1,0]⟩,
  ⟨2,5,[13,5,6,7,8,9,10,11,12,3,4,2,1,0]⟩,
  ⟨2,5,[13,5,4,3,12,11,10,9,8,7,6,2,1,0]⟩,
  ⟨2,6,[13,6,7,8,9,10,11,12,3,4,5,2,1,0]⟩,
  ⟨2,10,[13,10,9,8,7,6,5,4,3,12,11,2,1,0]⟩,
  ⟨2,10,[13,10,11,12,3,4,5,6,7,8,9,2,1,0]⟩,
  ⟨2,10,[11,12,6,7,8,9,10,13,2,3,4,5,0,1]⟩,
  ⟨2,10,[13,10,11,12,6,7,8,9,2,3,4,5,0,1]⟩,
  ⟨3,6,[13,6,7,8,9,10,11,12,4,5,3,2,1,0]⟩,
  ⟨4,7,[13,7,8,9,10,11,12,5,6,4,3,2,1,0]⟩,
  ⟨4,7,[12,11,10,9,8,7,13,4,5,6,0,3,2,1]⟩]

def poolGood (l : List Vertex) : Bool :=
  decide l.Nodup && decide (∀ k : Vertex,k∈l)

theorem pool_valid : pool.all (fun c => poolGood c.path) = true := by decide +kernel

def hasPath (i j : ℕ) (m : Marks) (e f g h t : Bool) : Bool :=
  pool.any fun c => decide (i=c.left ∧ j=c.right) &&
    decide (c.path.Chain' (fun u v => edge i j m e f g h t u v=true))

theorem hasPath_sound {i j : ℕ} {m : Marks} {e f g h t : Bool}
    (ok : hasPath i j m e f g h t=true) : Spanning i j m e f g h t := by
  obtain ⟨c,cm,cc⟩ := List.any_eq_true.mp ok
  have gc := List.all_eq_true.mp pool_valid c cm
  simp only [poolGood,Bool.and_eq_true,decide_eq_true_eq] at gc cc
  exact ⟨c.path,gc.1,gc.2,cc.2⟩

def exceptionB (i j : ℕ) (m : Marks) (f g h t : Bool) : Bool :=
  decide (i=4 ∧ j=8) && f && !g && !h && t && decide (∀ k, m k=exceptionMarks k)

theorem exceptionB_sound {i j : ℕ} {m : Marks} {e f g h t : Bool}
    (ok : exceptionB i j m f g h t=true) : Exceptional i j m e f g h t := by
  simp [exceptionB,Bool.and_eq_true,and_assoc] at ok
  exact ⟨ok.1,ok.2.1,funext ok.2.2.2.2.2.2,ok.2.2.1,ok.2.2.2.1,ok.2.2.2.2.1,ok.2.2.2.2.2.1⟩

end FourOrder14One
