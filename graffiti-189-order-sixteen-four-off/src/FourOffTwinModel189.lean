
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffFour16Twin
open Finset
abbrev Marks := Fin 11→Fin 3
abbrev Vertex := Fin 16
abbrev Slots := Fin 4→Fin 4

def portAt (c : Slots) (b : ℕ) : Fin 4 :=
  if h : 12≤b ∧ b<16 then c ⟨b-12,by omega⟩ else 0

def dir (j : ℕ) (m : Marks) (c : Slots) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  let p := portAt c b
  decide (b=a+1 ∧ b≤11) ||
  decide (12≤a ∧ a<b) ||
  decide ((a=1 ∧ (p=1 ∨ p=3)) ∨ (a=j ∧ (p=2 ∨ p=3))) ||
  (if q : a=0 ∧ 1≤b ∧ b≤11 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=11 ∧ a<11 then decide (m ⟨a,q.2⟩=2) else false)

def edge (j : ℕ) (m : Marks) (c : Slots) (u v : Vertex) : Bool := dir j m c u v || dir j m c v u

def d2Set (j : ℕ) (m : Marks) (c : Slots) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge j m c u v=true ∧
    ∃ w : Vertex, edge j m c u w=true ∧ edge j m c w v=true

def witness (j : ℕ) (v : Vertex) : List Vertex :=
  if v.val=0 ∨ v.val=11 then List.finRange 16
  else if v.val<11 then [Fin.ofNat' 16 (v.val-1),Fin.ofNat' 16 (v.val+1)]
  else [1,Fin.ofNat' 16 j]

def fast (j : ℕ) (m : Marks) (c : Slots) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge j m c u v=true ∧
    (witness j v).any (fun w => edge j m c u w && edge j m c w v)=true

theorem fast_sub (j : ℕ) (m : Marks) (c : Slots) (u : Vertex) :
    fast j m c u⊆d2Set j m c u := by
  intro v vm
  obtain ⟨_,ne,no,mem⟩ := mem_filter.mp vm
  obtain ⟨w,_,wyes⟩ := List.any_eq_true.mp mem
  simp only [Bool.and_eq_true] at wyes
  exact mem_filter.mpr ⟨mem_univ _,ne,no,w,wyes.1,wyes.2⟩

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def Hole (_i j k : ℕ) : Prop := k=1 ∨ k=j-1 ∨ k=j

instance (i j k : ℕ) : Decidable (Hole i j k) := by unfold Hole; infer_instance

def sites (i j : ℕ) : List (Fin 11) :=
  (List.finRange 11).filter (fun k => decide (k.val≠0 ∧ k.val≠10 ∧ ¬Hole i j k.val))

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

def decode (i j : ℕ) (d : List (Fin 3)) (k : Fin 11) : Fin 3 :=
  if k.val=0 then 1 else if k.val=10 then 2
  else if Hole i j k.val then 0 else pick (sites i j) d k

theorem decode_full (i j : ℕ) (m : Marks) (h0 : m 0=1) (h10 : m 10=2)
    (holes : ∀ k : Fin 11, Hole i j k.val → m k=0) :
    decode i j ((sites i j).map m) = m := by
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
      simpa only [eq] using h10.symm
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
  j : ℕ
  path : List Vertex

def pool : List Candidate := [
  ⟨6,[0,1,12,13,14,15,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,1,12,13,15,14,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,1,12,14,13,15,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,1,12,14,15,13,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,1,12,15,13,14,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,1,12,15,14,13,6,5,4,3,2,11,10,9,8,7]⟩,
  ⟨6,[0,5,4,3,2,1,12,13,14,15,6,7,8,9,10,11]⟩,
  ⟨6,[0,5,4,3,2,1,12,13,15,14,6,7,8,9,10,11]⟩,
  ⟨6,[0,5,4,3,2,1,12,14,13,15,6,7,8,9,10,11]⟩,
  ⟨6,[0,5,4,3,2,1,12,14,15,13,6,7,8,9,10,11]⟩,
  ⟨6,[0,5,4,3,2,1,12,15,13,14,6,7,8,9,10,11]⟩,
  ⟨6,[0,5,4,3,2,1,12,15,14,13,6,7,8,9,10,11]⟩,
  ⟨7,[0,1,12,13,14,15,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,1,12,13,15,14,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,1,12,14,13,15,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,1,12,14,15,13,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,1,12,15,13,14,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,1,12,15,14,13,7,6,5,4,3,2,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,13,14,15,7,6,5,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,13,15,14,7,6,5,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,14,13,15,7,6,5,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,14,15,13,7,6,5,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,15,13,14,7,6,5,11,8,9,10]⟩,
  ⟨7,[0,4,3,2,1,12,15,14,13,7,6,5,11,8,9,10]⟩,
  ⟨8,[0,1,12,13,14,15,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,1,12,13,15,14,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,1,12,14,13,15,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,1,12,14,15,13,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,1,12,15,13,14,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,1,12,15,14,13,8,7,6,5,4,3,2,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,13,14,15,8,7,6,5,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,13,15,14,8,7,6,5,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,14,13,15,8,7,6,5,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,14,15,13,8,7,6,5,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,15,13,14,8,7,6,5,11,9,10]⟩,
  ⟨8,[0,4,3,2,1,12,15,14,13,8,7,6,5,11,9,10]⟩,
  ⟨9,[0,1,12,13,14,15,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,1,12,13,15,14,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,1,12,14,13,15,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,1,12,14,15,13,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,1,12,15,13,14,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,1,12,15,14,13,9,8,7,6,5,4,3,2,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,13,14,15,9,8,7,6,5,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,13,15,14,9,8,7,6,5,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,14,13,15,9,8,7,6,5,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,14,15,13,9,8,7,6,5,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,15,13,14,9,8,7,6,5,11,10]⟩,
  ⟨9,[0,4,3,2,1,12,15,14,13,9,8,7,6,5,11,10]⟩]

def Spanning (j : ℕ) (m : Marks) (c : Slots) : Prop :=
  ∃ l : List Vertex, l.Nodup ∧ (∀ k : Vertex,k∈l) ∧
    l.Chain' (fun u v => edge j m c u v=true)

def poolGood (l : List Vertex) : Bool :=
  decide l.Nodup && decide (∀ k : Vertex,k∈l)

theorem pool_valid : pool.all (fun c => poolGood c.path) = true := by decide +kernel

def hasPath (j : ℕ) (m : Marks) (c : Slots) : Bool :=
  pool.any fun b => decide (j=b.j) &&
    decide (b.path.Chain' (fun u v => edge j m c u v=true))

theorem hasPath_sound {j : ℕ} {m : Marks} {c : Slots}
    (ok : hasPath j m c=true) : Spanning j m c := by
  obtain ⟨b,bm,bc⟩ := List.any_eq_true.mp ok
  have gc := List.all_eq_true.mp pool_valid b bm
  simp only [poolGood,Bool.and_eq_true,decide_eq_true_eq] at gc bc
  exact ⟨b.path,gc.1,gc.2,bc.2⟩

def codes (x y z : Fin 4) (k : Fin 4) : Fin 4 :=
  if k=0 then 3 else if k=1 then x else if k=2 then y else z

theorem codes_ext (c : Slots) (h : c 0=3) : codes (c 1) (c 2) (c 3)=c := by
  funext u
  fin_cases u <;> simp [codes,h]

def acount (c : Slots) : ℕ := (univ.filter (fun k => c k≠0)).card
def lcount (c : Slots) : ℕ := (univ.filter (fun k => c k=1 ∨ c k=3)).card

def gate (j : ℕ) (m : Marks) (c : Slots) : Bool :=
  !(decide (3≤acount c ∧ lcount c≤2) &&
    decide ((fast j m c 0).card≤4 ∧ (fast j m c 11).card≤4)) ||
    hasPath j m c

def row (j : ℕ) : Bool :=
  (bitlists (sites 1 j).length).all (fun d =>
    let m := decode 1 j d
    !(decide (markCount m 1=4 ∧ markCount m 2=4)) ||
      (List.finRange 4).all (fun x => (List.finRange 4).all (fun y =>
        (List.finRange 4).all (fun z => gate j m (codes x y z)))))

theorem check_row {j : ℕ} {m : Marks} {c : Slots} (ok : row j=true)
    (h0 : m 0=1) (h10 : m 10=2)
    (holes : ∀ k : Fin 11,Hole 1 j k.val → m k=0)
    (med : ∀ k : Fin 11,¬Hole 1 j k.val → m k≠0)
    (ml : markCount m 1=4) (mr : markCount m 2=4)
    (c0 : c 0=3) (ac : 3≤acount c) (lc : lcount c≤2)
    (dleft : (d2Set j m c 0).card≤4)
    (dright : (d2Set j m c 11).card≤4) :
    Spanning j m c := by
  unfold row at ok
  let d := (sites 1 j).map m
  have dd : d∈bitlists (sites 1 j).length := by
    have a := mem_bitlists (l:=d) (by
      intro k hk
      obtain ⟨j,jm,rfl⟩ := List.mem_map.mp hk
      exact med j (of_decide_eq_true (List.mem_filter.mp jm).2).2.2)
    simpa [d] using a
  have cb := List.all_eq_true.mp ok d dd
  have eq : decode 1 j d=m := decode_full 1 j m h0 h10 holes
  simp only [eq,ml,mr,true_and,decide_true,Bool.not_true,Bool.false_or] at cb
  have A := List.all_eq_true.mp cb (c 1) (List.mem_finRange _)
  have B := List.all_eq_true.mp A (c 2) (List.mem_finRange _)
  have ee := List.all_eq_true.mp B (c 3) (List.mem_finRange _)
  have cc := codes_ext c c0
  have fl := (card_le_card (fast_sub j m c 0)).trans dleft
  have fr := (card_le_card (fast_sub j m c 11)).trans dright
  have hz : hasPath j m c=true := by simpa [gate,cc,ac,lc,fl,fr] using ee
  exact hasPath_sound hz

end OffFour16Twin
