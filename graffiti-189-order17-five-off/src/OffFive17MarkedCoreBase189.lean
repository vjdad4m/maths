import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OffFive17MarkedCore

abbrev V := Fin 5
abbrev Color := ℕ

def pairs : List (ℕ×ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def bit (b : List Bool) (i j : ℕ) := b[(pairs.idxOf (i,j))]?.getD false

def edge (b : List Bool) (u v : V) : Bool :=
  if u.val<v.val then bit b u.val v.val else if v.val<u.val then bit b v.val u.val else false

def degree (b : List Bool) (u : V) : ℕ := ((List.finRange 5).filter (edge b u)).length

def color (m : List Color) (u : V) : Color := m[u.val]?.getD 0

def total (m : List Color) (b : List Bool) (u : V) : ℕ :=
  degree b u + if color m u=0 then 0 else 1

def unusualLeaf (m : List Color) (b : List Bool) (u v : V) : Prop :=
  color m u≠0 ∧ color m v≠0 ∧ color m u≠color m v ∧ edge b u v=true ∧ degree b u=1

instance (m : List Color) (b : List Bool) (u v : V) : Decidable (unusualLeaf m b u v) := by
  unfold unusualLeaf
  infer_instance

def noLeaf (m : List Color) (b : List Bool) : Bool :=
  (List.finRange 5).all fun u => (List.finRange 5).all fun v => !decide (unusualLeaf m b u v)

def guard (m : List Color) (b : List Bool) : Bool :=
  (List.finRange 5).all (fun u => decide (2 ≤ total m b u)) &&
  decide (((List.finRange 5).filter (fun u=>decide (total m b u<4))).length ≤ 1) &&
  noLeaf m b

def accepted (m : List Color) (b : List Bool) (l : List V) : Prop :=
  l.length=5 ∧ l.Nodup ∧
  color m (l.headD 0)=1 ∧ color m (l.getLastD 0)=2 ∧
  l.Chain' (fun i j=>edge b i j=true)

instance (m : List Color) (b : List Bool) (l : List V) : Decidable (accepted m b l) := by
  unfold accepted
  infer_instance

def candidates (m : List Color) : List (List V) :=
  if m=[0,0,0,1,2] then [[3,0,1,2,4],[3,1,2,0,4],[3,1,0,2,4]]
  else
  if m=[0,0,1,1,2] then [[2,0,1,3,4],[2,3,0,1,4],[3,0,1,2,4],[2,3,1,0,4]]
  else
  if m=[0,0,1,2,2] then [[2,0,1,3,4],[2,3,0,1,4],[2,1,0,4,3],[2,0,3,1,4]]
  else
  if m=[0,1,1,1,2] then [[1,0,2,3,4],[2,1,3,0,4],[3,0,1,2,4],[2,0,3,1,4],[1,3,2,0,4],[2,3,1,0,4]]
  else
  if m=[0,1,1,2,2] then [[1,0,2,3,4],[1,2,4,0,3],[2,0,3,1,4],[1,3,2,0,4],[1,0,3,2,4],[1,0,4,2,3]]
  else
  if m=[0,1,2,2,2] then [[1,0,2,3,4],[1,2,4,0,3],[1,4,3,0,2],[1,3,2,0,4],[1,0,3,2,4],[1,0,4,2,3]]
  else
  if m=[1,1,1,1,2] then [[0,1,2,3,4],[1,3,0,2,4],[0,2,3,1,4],[1,0,3,2,4],[1,2,0,3,4],[0,3,1,2,4],[2,0,1,3,4],[2,1,0,3,4],[2,3,0,1,4],[3,0,1,2,4],[3,1,0,2,4],[3,2,0,1,4]]
  else
  if m=[1,1,1,2,2] then [[0,1,2,3,4],[0,2,4,1,3],[2,1,3,0,4],[1,0,2,4,3],[1,4,0,2,3],[0,1,4,2,3],[1,2,0,3,4],[2,0,1,3,4]]
  else
  if m=[1,1,2,2,2] then [[0,1,2,3,4],[0,3,1,4,2],[1,3,4,0,2],[1,0,4,2,3],[1,0,2,4,3],[1,4,0,3,2],[0,3,1,2,4]]
  else
  if m=[1,2,2,2,2] then [[0,1,2,3,4],[0,2,4,1,3],[0,3,1,2,4],[0,2,1,4,3],[0,1,4,2,3],[0,2,3,1,4],[0,1,3,4,2],[0,1,4,3,2],[0,2,3,4,1],[0,2,4,3,1],[0,3,4,1,2],[0,3,4,2,1]]
  else
  []

def gate (m : List Color) (b : List Bool) : Bool :=
  !guard m b || (candidates m).any (fun l=>decide (accepted m b l))

def masks : ℕ→List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).flatMap (fun l=>[false::l,true::l])

theorem masks_mem (b : List Bool) : b∈masks b.length := by
  induction b with
  | nil => simp [masks]
  | cons a l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨l,ih,?_⟩
    cases a <;> simp

def row (m : List Color) : Bool := (masks 10).all (gate m)

theorem row_sound {m : List Color} {b : List Bool} (h : row m=true) (b10 : b.length=10)
    (ok : guard m b=true) : ∃ l : List V,accepted m b l := by
  have mb : b∈masks 10 := b10 ▸ masks_mem b
  have h := List.all_eq_true.mp h b mb
  have yes : (candidates m).any (fun l=>decide (accepted m b l))=true := by
    simpa [gate,ok] using h
  obtain ⟨l,_,hl⟩ := List.any_eq_true.mp yes
  exact ⟨l,of_decide_eq_true hl⟩

#print axioms row_sound
def tuplesRaw (S : List ℕ) : ℕ→List (List ℕ)
  | 0 => [[]]
  | n+1 => (0::S).flatMap fun c => (tuplesRaw S n).map (c::·)

theorem mem_tuplesRaw {S : List ℕ} {P : List ℕ}
    (ok : ∀ k∈P,k=0 ∨ k∈S) : P∈tuplesRaw S P.length := by
  induction P with
  | nil => simp [tuplesRaw]
  | cons k P ih =>
    apply List.mem_flatMap.mpr
    refine ⟨k,by simpa using ok k (by simp),?_⟩
    exact List.mem_map.mpr ⟨P,ih (fun e h => ok e (by simp [h])),rfl⟩

def tuples (S : List ℕ) : List (List ℕ) :=
  (tuplesRaw S 5).filter (fun P => decide (P.Pairwise (·≤·)) && S.all (fun k => decide (k∈P)))

theorem mem_tuples {S P : List ℕ}
    (len : P.length=5) (ok : ∀ k∈P,k=0 ∨ k∈S)
    (sorted : P.Pairwise (·≤·)) (full : ∀ k∈S,k∈P) :
    P∈tuples S := by
  have h : S.all (fun k => decide (k∈P))=true :=
    List.all_eq_true.mpr (fun k km => decide_eq_true (full k km))
  apply List.mem_filter.mpr
  refine ⟨?_,by simp [sorted,h]⟩
  rw [←len]
  exact mem_tuplesRaw ok


def colorTuples : List (List ℕ) := tuples [1,2]

#print axioms mem_tuples
end OffFive17MarkedCore
