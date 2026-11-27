import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OffFour16Solo
open Finset

abbrev Marks := Fin 11 → Fin 3
abbrev Vertex := Fin 16

def dir (i j x y : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤11) ||
  decide (12≤a ∧ a<b) ||
  decide (a=i ∧ 12≤b ∧ b<12+x) ||
  decide (a=j ∧ 12+x≤b ∧ b<12+x+y) ||
  (if q : a=0 ∧ 1≤b ∧ b≤11 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=11 ∧ a<11 then decide (m ⟨a,q.2⟩=2) else false)

def edge (i j x y : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  dir i j x y m u v || dir i j x y m v u

def d2Set (i j x y : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j x y m u v=true ∧
    ∃ w : Vertex, edge i j x y m u w=true ∧ edge i j x y m w v=true


def edgeWitnesses (i j : ℕ) (v : Vertex) : List Vertex :=
  if v.val=0 ∨ v.val=11 then List.finRange 16
  else if v.val<11 then [Fin.ofNat' 16 (v.val-1), Fin.ofNat' 16 (v.val+1)]
  else [Fin.ofNat' 16 i, Fin.ofNat' 16 j]

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

def sites (s t : ℕ) : List (Fin 11) :=
  (List.finRange 11).filter (fun k => decide (k.val≠0 ∧ k.val≠10 ∧ ¬Hole k.val s t))

def pick : List (Fin 11) → List (Fin 3) → Fin 11 → Fin 3
  | a::as,b::bs,k => if k=a then b else pick as bs k
  | _,_,_ => 0

theorem pick_map {m : Marks} {L : List (Fin 11)} {k : Fin 11} (H : k∈L) :
    pick L (L.map m) k = m k := by
  induction L with
  | nil => simp at H
  | cons a l ih =>
    by_cases eq : k=a
    · simp [pick,eq]
    · simp [pick,eq,ih ((List.mem_cons.mp H).resolve_left eq)]

def decode (s t : ℕ) (d : List (Fin 3)) (k : Fin 11) : Fin 3 :=
  if k.val=0 then 1 else if k.val=10 then 2
  else if Hole k.val s t then 0 else pick (sites s t) d k

theorem decode_full (s t : ℕ) (m : Marks) (h0 : m 0=1) (h9 : m 10=2)
    (holes : ∀ k : Fin 11, Hole k.val s t → m k=0) :
    decode s t ((sites s t).map m) = m := by
  funext k
  unfold decode
  split
  next H =>
    have eq : k=(0:Fin 11) := Fin.ext H
    simpa only [eq] using h0.symm
  next H =>
    split
    next J =>
      have eq : k=(10:Fin 11) := Fin.ext J
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
  ⟨1,5,[0,1,12,13,15,14,5,4,3,2,11,10,9,8,7,6]⟩,
  ⟨1,5,[0,1,12,13,14,15,5,4,3,2,11,10,9,8,7,6]⟩,
  ⟨1,6,[0,5,4,3,2,1,12,13,15,14,6,7,8,9,10,11]⟩,
  ⟨1,6,[0,1,12,13,15,14,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨1,6,[0,5,4,3,2,1,11,10,9,8,7,6,13,12,14,15]⟩,
  ⟨1,6,[0,1,12,13,14,15,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨1,6,[0,5,4,3,2,1,12,13,14,15,6,7,8,9,10,11]⟩,
  ⟨1,7,[2,3,0,4,5,6,7,8,9,10,11,1,12,13,14,15]⟩,
  ⟨1,7,[0,6,5,4,3,2,1,11,10,9,8,7,13,12,14,15]⟩,
  ⟨1,7,[0,1,12,13,15,14,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨1,7,[0,4,3,2,1,12,13,15,14,7,6,5,11,8,9,10]⟩,
  ⟨1,7,[6,5,0,4,3,2,1,12,13,15,14,7,8,9,10,11]⟩,
  ⟨1,7,[0,6,5,4,3,2,1,12,13,15,14,7,8,9,10,11]⟩,
  ⟨1,7,[0,1,12,13,14,15,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨1,7,[0,4,3,2,1,12,13,14,15,7,6,5,11,8,9,10]⟩,
  ⟨1,7,[6,5,0,4,3,2,1,12,13,14,15,7,8,9,10,11]⟩,
  ⟨1,7,[0,6,5,4,3,2,1,12,13,14,15,7,8,9,10,11]⟩,
  ⟨1,8,[0,1,12,13,15,14,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨1,8,[0,4,3,2,1,12,13,15,14,8,7,6,5,11,9,10]⟩,
  ⟨1,8,[0,5,4,3,2,1,12,13,15,14,8,7,6,11,9,10]⟩,
  ⟨1,8,[0,1,12,13,14,15,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨1,8,[0,4,3,2,1,12,13,14,15,8,7,6,5,11,9,10]⟩,
  ⟨1,8,[0,5,4,3,2,1,12,13,14,15,8,7,6,11,9,10]⟩,
  ⟨1,9,[0,1,12,13,15,14,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨1,9,[0,4,3,2,1,12,13,15,14,9,8,7,6,5,11,10]⟩,
  ⟨1,9,[0,5,4,3,2,1,12,13,15,14,9,8,7,6,11,10]⟩,
  ⟨1,9,[0,1,12,13,14,15,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨1,9,[0,4,3,2,1,12,13,14,15,9,8,7,6,5,11,10]⟩,
  ⟨1,9,[0,5,4,3,2,1,12,13,14,15,9,8,7,6,11,10]⟩,
  ⟨1,10,[0,1,2,3,4,5,6,7,11,8,9,10,13,12,14,15]⟩,
  ⟨1,10,[0,1,2,3,4,5,6,7,11,8,9,10,14,12,13,15]⟩,
  ⟨2,6,[1,0,5,4,3,2,12,13,15,14,6,7,8,9,10,11]⟩,
  ⟨2,6,[1,0,5,4,3,2,12,13,14,15,6,7,8,9,10,11]⟩,
  ⟨2,7,[0,1,2,12,13,15,14,7,6,5,4,3,11,10,9,8]⟩,
  ⟨2,7,[1,0,6,5,4,3,2,11,10,9,8,7,13,12,14,15]⟩,
  ⟨2,7,[0,1,2,12,13,15,14,7,6,5,4,3,11,8,9,10]⟩,
  ⟨2,7,[1,0,4,3,2,12,13,15,14,7,6,5,11,8,9,10]⟩,
  ⟨2,7,[1,0,6,5,4,3,2,12,13,15,14,7,8,9,10,11]⟩,
  ⟨2,7,[0,1,2,12,13,14,15,7,6,5,4,3,11,10,9,8]⟩,
  ⟨2,7,[0,1,2,12,13,14,15,7,6,5,4,3,11,8,9,10]⟩,
  ⟨2,7,[1,0,4,3,2,12,13,14,15,7,6,5,11,8,9,10]⟩,
  ⟨2,7,[1,0,6,5,4,3,2,12,13,14,15,7,8,9,10,11]⟩,
  ⟨2,8,[0,1,2,12,13,15,14,8,7,6,5,4,3,11,9,10]⟩,
  ⟨2,8,[1,0,4,3,2,12,13,15,14,8,7,6,5,11,9,10]⟩,
  ⟨2,8,[1,0,5,4,3,2,12,13,15,14,8,7,6,11,9,10]⟩,
  ⟨2,8,[0,1,2,12,13,14,15,8,7,6,5,4,3,11,9,10]⟩,
  ⟨2,8,[1,0,4,3,2,12,13,14,15,8,7,6,5,11,9,10]⟩,
  ⟨2,8,[1,0,5,4,3,2,12,13,14,15,8,7,6,11,9,10]⟩,
  ⟨2,9,[0,1,2,12,13,15,14,9,8,7,6,5,4,3,11,10]⟩,
  ⟨2,9,[1,0,4,3,2,12,13,15,14,9,8,7,6,5,11,10]⟩,
  ⟨2,9,[1,0,5,4,3,2,12,13,15,14,9,8,7,6,11,10]⟩,
  ⟨2,9,[0,1,2,12,13,14,15,9,8,7,6,5,4,3,11,10]⟩,
  ⟨2,9,[1,0,4,3,2,12,13,14,15,9,8,7,6,5,11,10]⟩,
  ⟨2,9,[1,0,5,4,3,2,12,13,14,15,9,8,7,6,11,10]⟩,
  ⟨3,6,[1,2,0,5,4,3,12,13,15,14,6,7,8,9,10,11]⟩,
  ⟨3,6,[1,2,0,5,4,3,12,13,14,15,6,7,8,9,10,11]⟩,
  ⟨3,7,[1,2,0,6,5,4,3,11,10,9,8,7,13,12,14,15]⟩,
  ⟨3,7,[0,1,2,3,12,13,15,14,7,6,5,4,11,8,9,10]⟩,
  ⟨3,7,[1,2,0,6,5,4,3,12,13,15,14,7,8,9,10,11]⟩,
  ⟨3,7,[2,1,0,6,5,4,3,12,13,15,14,7,8,9,10,11]⟩,
  ⟨3,7,[0,1,2,3,12,13,14,15,7,6,5,4,11,8,9,10]⟩,
  ⟨3,7,[1,2,0,6,5,4,3,12,13,14,15,7,8,9,10,11]⟩,
  ⟨3,7,[2,1,0,6,5,4,3,12,13,14,15,7,8,9,10,11]⟩,
  ⟨3,8,[0,1,2,3,12,13,15,14,8,7,6,5,4,11,10,9]⟩,
  ⟨3,8,[0,1,2,3,12,13,15,14,8,7,6,5,4,11,9,10]⟩,
  ⟨3,8,[1,2,0,5,4,3,12,13,15,14,8,7,6,11,9,10]⟩,
  ⟨3,8,[0,1,2,3,12,13,14,15,8,7,6,5,4,11,10,9]⟩,
  ⟨3,8,[0,1,2,3,12,13,14,15,8,7,6,5,4,11,9,10]⟩,
  ⟨3,8,[1,2,0,5,4,3,12,13,14,15,8,7,6,11,9,10]⟩,
  ⟨3,8,[0,7,6,5,4,3,2,1,11,10,9,8,14,12,13,15]⟩,
  ⟨3,8,[0,7,6,5,4,3,2,1,11,10,9,8,15,12,13,14]⟩,
  ⟨4,7,[1,2,3,0,6,5,4,11,10,9,8,7,13,12,14,15]⟩,
  ⟨4,7,[0,1,2,3,4,12,13,15,14,7,6,5,11,8,9,10]⟩,
  ⟨4,7,[1,2,3,0,6,5,4,12,13,15,14,7,8,9,10,11]⟩,
  ⟨4,7,[3,2,1,0,6,5,4,12,13,15,14,7,8,9,10,11]⟩,
  ⟨4,7,[0,1,2,3,4,12,13,14,15,7,6,5,11,8,9,10]⟩,
  ⟨4,7,[1,2,3,0,6,5,4,12,13,14,15,7,8,9,10,11]⟩,
  ⟨4,7,[3,2,1,0,6,5,4,12,13,14,15,7,8,9,10,11]⟩,
  ⟨4,7,[0,1,2,3,4,12,13,15,14,7,6,5,11,10,9,8]⟩,
  ⟨4,7,[0,1,2,3,4,12,13,14,15,7,6,5,11,10,9,8]⟩]

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
  (List.finRange 11).all (fun k => decide
      (((k.val=i ∨ k.val=j) → m k≠1) ∧
       ((k.val+1=i ∨ k.val+1=j) → m k≠2)))


def validMarks (i j : ℕ) (m : Marks) : Bool :=
  decide (4≤markCount m 1 ∧ 4≤markCount m 2) && PinsAllowed i j m

def populations : List (ℕ×ℕ) := [(1,2),(2,1),(1,3),(2,2),(3,1)]

structure Exception where
  i : ℕ
  j : ℕ
  x : ℕ
  y : ℕ
  marks : List (Fin 3)

def exceptions : List Exception := [
  ⟨2,7,1,2,[1,1,0,1,1,0,0,2,2,2,2]⟩,
  ⟨2,7,1,3,[1,1,0,1,1,0,0,2,2,2,2]⟩,
  ⟨2,7,2,1,[1,1,0,1,1,0,0,2,2,2,2]⟩,
  ⟨2,7,2,2,[1,1,0,1,1,0,0,2,2,2,2]⟩,
  ⟨3,7,1,2,[1,1,1,0,1,2,0,0,2,2,2]⟩,
  ⟨3,7,1,2,[1,1,1,0,1,0,0,2,2,2,2]⟩,
  ⟨3,7,1,3,[1,1,1,0,1,2,0,0,2,2,2]⟩,
  ⟨3,7,1,3,[1,1,1,0,1,0,0,2,2,2,2]⟩,
  ⟨3,7,2,1,[1,1,1,0,1,0,0,2,2,2,2]⟩,
  ⟨3,7,2,2,[1,1,1,0,1,0,0,2,2,2,2]⟩,
  ⟨4,7,1,2,[1,1,1,1,0,0,0,2,2,2,2]⟩,
  ⟨4,7,1,3,[1,1,1,1,0,0,0,2,2,2,2]⟩,
  ⟨4,7,2,1,[1,1,1,1,0,0,0,2,2,2,2]⟩,
  ⟨4,7,2,2,[1,1,1,1,0,0,0,2,2,2,2]⟩,
  ⟨4,7,3,1,[1,1,1,1,0,0,0,2,2,2,2]⟩]

def exceptional (i j x y : ℕ) (m : Marks) : Bool :=
  exceptions.any (fun b => decide (b.i=i ∧ b.j=j ∧ b.x=x ∧ b.y=y ∧ b.marks=List.ofFn m))

def gate (i j x y : ℕ) (m : Marks) : Bool :=
  !(decide ((fastD2Set i j x y m 0).card≤4 ∧ (fastD2Set i j x y m 11).card≤4)) ||
    (hasPath i j x y m || exceptional i j x y m)

def sparse : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => ((sparse n).flatMap (fun l => [1::l,2::l])) ++
    ((bitlists n).map (fun l => 0::l))

theorem mem_sparse {l : List (Fin 3)} (h : l.count 0≤1) : l∈sparse l.length := by
  induction l with
  | nil => simp [sparse]
  | cons a l ih =>
    by_cases az : a=0
    · subst a
      have cc : l.count 0=0 := by simpa [List.count_cons] using h
      have no : ∀ x∈l,x≠0 := by
        intro x xm eq
        subst x
        exact (List.count_pos_iff.mpr xm).ne' cc
      apply List.mem_append.mpr
      exact .inr (List.mem_map.mpr ⟨l,mem_bitlists no,rfl⟩)
    have hc : l.count 0≤1 := by
      simpa [List.count_cons,az,Ne.symm az] using h
    apply List.mem_append.mpr
    apply Or.inl
    refine List.mem_flatMap.mpr ⟨l,ih hc,?_⟩
    fin_cases a <;> simp_all

def part (i j s t : ℕ) : Bool :=
  (sparse (sites s t).length).all (fun d =>
    let m := decode s t d
    !(decide (3≤d.count 1 ∧ 3≤d.count 2)) || (!validMarks i j m || populations.all (fun (x,y) => gate i j x y m)))

def fit (i j s t : ℕ) : Bool :=
  decide (1≤s ∧ s≤9 ∧ 1≤t ∧ t≤9 ∧ (s=i-1 ∨ s=j-1) ∧ (t=i ∨ t=j))

def row (i j : ℕ) : Bool :=
  [i-1,j-1].all fun s => [i,j].all fun t => !fit i j s t || part i j s t

end OffFour16Solo
