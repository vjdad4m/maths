import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffThree16Interior
open Finset

abbrev Marks := Fin 12→Fin 3
abbrev Vertex := Fin 16

def dir (i j : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤12) ||
  decide (13≤a ∧ a<b) ||
  decide ((a=i ∨ a=j) ∧ (b=13 ∨ b=14)) ||
  (if q : a=0 ∧ 1≤b ∧ b≤12 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=12 ∧ a<12 then decide (m ⟨a,q.2⟩=2) else false)

def edge (i j : ℕ) (m : Marks) (u v : Vertex) : Bool :=
  dir i j m u v || dir i j m v u

def d2Set (i j : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j m u v=true ∧
    ∃ w : Vertex, edge i j m u w=true ∧ edge i j m w v=true

def witness (v : Vertex) : List Vertex :=
  if v.val=0 ∨ v.val=12 then List.finRange 16
  else if v.val<12 then [Fin.ofNat' 16 (v.val-1),Fin.ofNat' 16 (v.val+1)]
  else []

def fast (i j : ℕ) (m : Marks) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge i j m u v=true ∧
    (witness v).any (fun w => edge i j m u w && edge i j m w v)=true

theorem fast_sub (i j : ℕ) (m : Marks) (u : Vertex) :
    fast i j m u⊆d2Set i j m u := by
  intro v vm
  obtain ⟨_,ne,no,mem⟩ := mem_filter.mp vm
  obtain ⟨w,_,wyes⟩ := List.any_eq_true.mp mem
  simp only [Bool.and_eq_true] at wyes
  exact mem_filter.mpr ⟨mem_univ _,ne,no,w,wyes.1,wyes.2⟩

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def Hole (i j k : ℕ) : Prop := k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j

instance (i j k : ℕ) : Decidable (Hole i j k) := by unfold Hole; infer_instance

def sites (i j : ℕ) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => decide (k.val≠0 ∧ k.val≠11 ∧ ¬Hole i j k.val))

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
  else if Hole i j k.val then 0 else pick (sites i j) d k

theorem decode_full (i j : ℕ) (m : Marks) (h0 : m 0=1) (h11 : m 11=2)
    (holes : ∀ k : Fin 12, Hole i j k.val → m k=0) :
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
  ⟨2,5,[0,1,2,13,15,14,5,4,3,12,11,10,9,8,7,6]⟩,
  ⟨2,6,[0,1,2,13,15,14,6,5,4,3,12,11,10,9,8,7]⟩,
  ⟨2,7,[0,1,2,13,15,14,7,6,5,4,3,12,11,10,9,8]⟩,
  ⟨2,7,[1,0,6,5,4,3,2,13,15,14,7,8,9,10,11,12]⟩,
  ⟨2,8,[0,1,2,13,15,14,8,7,6,5,4,3,12,9,10,11]⟩,
  ⟨2,8,[1,0,5,4,3,2,13,15,14,8,7,6,12,9,10,11]⟩,
  ⟨2,9,[0,1,2,13,15,14,9,8,7,6,5,4,3,12,10,11]⟩,
  ⟨2,9,[1,0,5,4,3,2,13,15,14,9,8,7,6,12,10,11]⟩,
  ⟨2,10,[0,1,2,13,15,14,10,9,8,7,6,5,4,3,12,11]⟩,
  ⟨2,10,[1,0,5,4,3,2,13,15,14,10,9,8,7,6,12,11]⟩,
  ⟨3,6,[0,1,2,3,13,15,14,6,5,4,12,11,10,9,8,7]⟩,
  ⟨3,7,[0,1,2,3,13,15,14,7,6,5,4,12,11,10,9,8]⟩,
  ⟨3,7,[1,2,0,6,5,4,3,13,15,14,7,8,9,10,11,12]⟩,
  ⟨3,8,[0,1,2,3,13,15,14,8,7,6,5,4,12,11,10,9]⟩,
  ⟨3,8,[0,7,6,5,4,3,2,1,12,11,10,9,8,13,14,15]⟩,
  ⟨3,8,[0,1,2,3,13,15,14,8,7,6,5,4,12,9,10,11]⟩,
  ⟨3,8,[1,2,0,5,4,3,13,15,14,8,7,6,12,9,10,11]⟩,
  ⟨3,9,[0,1,2,3,13,15,14,9,8,7,6,5,4,12,10,11]⟩,
  ⟨3,9,[1,2,0,5,4,3,13,15,14,9,8,7,6,12,10,11]⟩,
  ⟨4,7,[0,1,2,3,4,13,15,14,7,6,5,12,11,10,9,8]⟩,
  ⟨4,7,[1,2,3,0,6,5,4,13,15,14,7,8,9,10,11,12]⟩,
  ⟨4,8,[0,1,2,3,4,13,15,14,8,7,6,5,12,11,10,9]⟩,
  ⟨4,8,[1,0,7,6,5,4,3,2,12,11,10,9,8,13,14,15]⟩,
  ⟨4,8,[0,1,2,3,4,13,15,14,8,7,6,5,12,9,10,11]⟩]

def Spanning (i j : ℕ) (m : Marks) : Prop :=
  ∃ l : List Vertex, l.Nodup ∧ (∀ k : Vertex,k∈l) ∧
    l.Chain' (fun u v => edge i j m u v=true)

def poolGood (l : List Vertex) : Bool :=
  decide l.Nodup && decide (∀ k : Vertex,k∈l)

theorem pool_valid : pool.all (fun c => poolGood c.path) = true := by decide +kernel

def hasPath (i j : ℕ) (m : Marks) : Bool :=
  pool.any fun c => decide (i=c.left ∧ j=c.right) &&
    decide (c.path.Chain' (fun u v => edge i j m u v=true))

theorem hasPath_sound {i j : ℕ} {m : Marks}
    (ok : hasPath i j m=true) : Spanning i j m := by
  obtain ⟨c,cm,cc⟩ := List.any_eq_true.mp ok
  have gc := List.all_eq_true.mp pool_valid c cm
  simp only [poolGood,Bool.and_eq_true,decide_eq_true_eq] at gc cc
  exact ⟨c.path,gc.1,gc.2,cc.2⟩

def eMarks (k : Fin 12) : Fin 3 :=
  if k.val≤2 ∨ k.val=5 then 1 else if k.val=6 ∨ 9≤k.val then 2 else 0

def exception (i j : ℕ) (m : Marks) : Bool :=
  decide (i=4 ∧ j=8) && decide (∀ k : Fin 12,m k=eMarks k)

def gate (i j : ℕ) (d : List (Fin 3)) : Bool :=
  let m := decode i j d
  !(decide (markCount m 1=4 ∧ markCount m 2=4) &&
    decide ((fast i j m 0).card≤4 ∧ (fast i j m 12).card≤4)) ||
    (hasPath i j m || exception i j m)

def row (i j : ℕ) : Bool := (bitlists (sites i j).length).all (gate i j)

theorem check_row {i j : ℕ} {m : Marks} (ok : row i j=true)
    (h0 : m 0=1) (h11 : m 11=2)
    (holes : ∀ k : Fin 12,Hole i j k.val → m k=0)
    (med : ∀ k : Fin 12,¬Hole i j k.val → m k≠0)
    (ml : markCount m 1=4) (mr : markCount m 2=4)
    (dleft : (d2Set i j m 0).card≤4)
    (dright : (d2Set i j m 12).card≤4) :
    Spanning i j m ∨ (i=4 ∧ j=8 ∧ m=eMarks) := by
  unfold row at ok
  let d := (sites i j).map m
  have dd : d∈bitlists (sites i j).length := by
    have a := mem_bitlists (l:=d) (by
      intro k hk
      obtain ⟨j,jm,rfl⟩ := List.mem_map.mp hk
      exact med j (of_decide_eq_true (List.mem_filter.mp jm).2).2.2)
    simpa [d] using a
  have cb := List.all_eq_true.mp ok d dd
  have eq : decode i j d=m := decode_full i j m h0 h11 holes
  have fl := (card_le_card (fast_sub i j m 0)).trans dleft
  have fr := (card_le_card (fast_sub i j m 12)).trans dright
  have hz : hasPath i j m=true ∨ exception i j m=true := by
    simpa [gate,eq,ml,mr,fl,fr,Bool.or_eq_true] using cb
  rcases hz with h|h
  · exact .inl (hasPath_sound h)
  · simp only [exception,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .inr ⟨h.1.1,h.1.2,funext h.2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_5 : row 2 5=true := by decide +kernel
#print axioms row_2_5

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_6 : row 2 6=true := by decide +kernel
#print axioms row_2_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_7 : row 2 7=true := by decide +kernel
#print axioms row_2_7

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_8 : row 2 8=true := by decide +kernel
#print axioms row_2_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_9 : row 2 9=true := by decide +kernel
#print axioms row_2_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_2_10 : row 2 10=true := by decide +kernel
#print axioms row_2_10

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_3_6 : row 3 6=true := by decide +kernel
#print axioms row_3_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_3_7 : row 3 7=true := by decide +kernel
#print axioms row_3_7

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_3_8 : row 3 8=true := by decide +kernel
#print axioms row_3_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_3_9 : row 3 9=true := by decide +kernel
#print axioms row_3_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_4_7 : row 4 7=true := by decide +kernel
#print axioms row_4_7

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem row_4_8 : row 4 8=true := by decide +kernel
#print axioms row_4_8

private theorem row_transport {i j a b : ℕ} (hi : i=a) (hj : j=b)
    (h : row a b=true) : row i j=true :=
  Eq.mpr (congrArg (fun q => q=true) (congrArg₂ row hi hj)) h

theorem all_rows (i j : ℕ) (ip : 1<i) (gap : i+3≤j) (oriented : i≤12-j) (jr : j≤10) :
    row i j=true := by
  have p : i=2 ∨ i=3 ∨ i=4 := by omega
  rcases p with a|a|a
  · have hj : j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
    rcases hj with b|b|b|b|b|b
    · exact @row_transport i j 2 5 a b row_2_5
    · exact @row_transport i j 2 6 a b row_2_6
    · exact @row_transport i j 2 7 a b row_2_7
    · exact @row_transport i j 2 8 a b row_2_8
    · exact @row_transport i j 2 9 a b row_2_9
    · exact @row_transport i j 2 10 a b row_2_10
  · have hj : j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b|b
    · exact @row_transport i j 3 6 a b row_3_6
    · exact @row_transport i j 3 7 a b row_3_7
    · exact @row_transport i j 3 8 a b row_3_8
    · exact @row_transport i j 3 9 a b row_3_9
  · have hj : j=7 ∨ j=8 := by omega
    rcases hj with b|b
    · exact @row_transport i j 4 7 a b row_4_7
    · exact @row_transport i j 4 8 a b row_4_8
#print axioms all_rows

end OffThree16Interior
