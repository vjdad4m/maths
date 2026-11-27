import NoFiveHoles133

namespace Graffiti133C7Only
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def Profile (i j : Fin 7) : Prop := j=i ∨ j=i+3 ∨ j=i+4
instance : DecidableRel Profile := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def Mask (m : Fin 128) (i : Fin 7) : Prop := m.val.testBit i.val = true
instance : DecidableRel Mask := fun _ _ => inferInstanceAs (Decidable (_ = _))

private def profileMask (b : Fin 7 → Bool) : Fin 128 :=
  ⟨(if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) +
   (if b 3 then 8 else 0) + (if b 4 then 16 else 0) + (if b 5 then 32 else 0) +
   (if b 6 then 64 else 0), by
     have h0 : (if b 0 then 1 else 0) ≤ (1:ℕ) := by split <;> decide
     have h1 : (if b 1 then 2 else 0) ≤ (2:ℕ) := by split <;> decide
     have h2 : (if b 2 then 4 else 0) ≤ (4:ℕ) := by split <;> decide
     have h3 : (if b 3 then 8 else 0) ≤ (8:ℕ) := by split <;> decide
     have h4 : (if b 4 then 16 else 0) ≤ (16:ℕ) := by split <;> decide
     have h5 : (if b 5 then 32 else 0) ≤ (32:ℕ) := by split <;> decide
     have h6 : (if b 6 then 64 else 0) ≤ (64:ℕ) := by split <;> decide
     omega⟩

lemma mask_cover : ∀ b : Fin 7 → Bool, ∀ i, Mask (profileMask b) i ↔ b i = true := by decide

def Rel8 (m : Fin 128) (i j : Fin 8) : Prop :=
  if hi : i.val < 7 then
    if hj : j.val < 7 then Cyclic ⟨_,hi⟩ ⟨_,hj⟩ else Mask m ⟨_,hi⟩
  else if hj : j.val < 7 then Mask m ⟨_,hj⟩ else False
instance (m : Fin 128) : DecidableRel (Rel8 m) := by
  intro i j
  unfold Rel8
  split <;> split <;> infer_instance

def Rel9 (a b : Fin 7) (edge : Bool) (i j : Fin 9) : Prop :=
  if hi : i.val < 7 then
    if hj : j.val < 7 then Cyclic ⟨_,hi⟩ ⟨_,hj⟩ else Profile (if j=7 then a else b) ⟨_,hi⟩
  else if hj : j.val < 7 then Profile (if i=7 then a else b) ⟨_,hj⟩ else i ≠ j ∧ edge=true
noncomputable instance (a b : Fin 7) (e : Bool) : DecidableRel (Rel9 a b e) := by
  intro i j
  unfold Rel9
  split <;> split <;> infer_instance

inductive Cert (n : ℕ)
| pass
| four (i j a b : Fin n)
| path (p : Fin 7 → Fin n)
| hole (p : Fin 6 → Fin n)

def Cert.Valid {n : ℕ} (R : Fin n → Fin n → Prop) (s : Prop) : Cert n → Prop
| .pass => s
| .four i j a b => i≠j ∧ a≠b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i=p j → i=j) ∧ ∀ i j, i<j → (R (p i) (p j) ↔ i.val+1=j.val)
| .hole p => (∀ i j, p i=p j → i=j) ∧ ∀ i j, R (p i) (p j) ↔ Cyclic i j
instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (s : Prop) [Decidable s] :
    DecidablePred (Cert.Valid R s) := by
  intro c
  cases c <;> unfold Cert.Valid <;> infer_instance

private def table8 (m : Fin 128) : Cert 8 :=
  match m.val with
  | 1 => .path ![2,3,4,5,6,0,7]
  | 2 => .path ![3,4,5,6,0,1,7]
  | 3 => .path ![2,3,4,5,6,0,7]
  | 4 => .path ![0,6,5,4,3,2,7]
  | 5 => .four 0 2 1 7
  | 6 => .path ![0,6,5,4,3,2,7]
  | 7 => .four 0 2 1 7
  | 8 => .path ![1,0,6,5,4,3,7]
  | 9 => .hole ![0,6,5,4,3,7]
  | 10 => .four 1 3 2 7
  | 11 => .four 1 3 2 7
  | 12 => .path ![1,0,6,5,4,3,7]
  | 13 => .four 0 2 1 7
  | 14 => .four 1 3 2 7
  | 15 => .four 0 2 1 7
  | 16 => .path ![2,1,0,6,5,4,7]
  | 17 => .hole ![0,1,2,3,4,7]
  | 18 => .hole ![0,1,7,4,5,6]
  | 20 => .four 2 4 3 7
  | 21 => .four 0 2 1 7
  | 22 => .four 2 4 3 7
  | 23 => .four 0 2 1 7
  | 24 => .path ![2,1,0,6,5,4,7]
  | 26 => .four 1 3 2 7
  | 27 => .four 1 3 2 7
  | 28 => .four 2 4 3 7
  | 29 => .four 0 2 1 7
  | 30 => .four 1 3 2 7
  | 31 => .four 0 2 1 7
  | 32 => .path ![0,1,2,3,4,5,7]
  | 33 => .four 0 5 6 7
  | 34 => .hole ![1,2,3,4,5,7]
  | 35 => .four 0 5 6 7
  | 36 => .hole ![0,1,2,7,5,6]
  | 37 => .four 0 2 1 7
  | 39 => .four 0 2 1 7
  | 40 => .four 3 5 4 7
  | 41 => .four 0 5 6 7
  | 42 => .four 1 3 2 7
  | 43 => .four 0 5 6 7
  | 44 => .four 3 5 4 7
  | 45 => .four 0 2 1 7
  | 46 => .four 1 3 2 7
  | 47 => .four 0 2 1 7
  | 48 => .path ![3,2,1,0,6,5,7]
  | 49 => .four 0 5 6 7
  | 51 => .four 0 5 6 7
  | 52 => .four 2 4 3 7
  | 53 => .four 0 2 1 7
  | 54 => .four 2 4 3 7
  | 55 => .four 0 2 1 7
  | 56 => .four 3 5 4 7
  | 57 => .four 0 5 6 7
  | 58 => .four 1 3 2 7
  | 59 => .four 0 5 6 7
  | 60 => .four 2 4 3 7
  | 61 => .four 0 2 1 7
  | 62 => .four 1 3 2 7
  | 63 => .four 0 2 1 7
  | 64 => .path ![1,2,3,4,5,6,7]
  | 65 => .path ![1,2,3,4,5,6,7]
  | 66 => .four 0 7 1 6
  | 67 => .four 0 7 1 6
  | 68 => .hole ![2,3,4,5,6,7]
  | 69 => .four 0 2 1 7
  | 70 => .four 0 7 1 6
  | 71 => .four 0 2 1 7
  | 72 => .hole ![0,1,2,3,7,6]
  | 74 => .four 0 7 1 6
  | 75 => .four 0 7 1 6
  | 77 => .four 0 2 1 7
  | 78 => .four 0 7 1 6
  | 79 => .four 0 2 1 7
  | 80 => .four 4 6 5 7
  | 81 => .four 4 6 5 7
  | 82 => .four 0 7 1 6
  | 83 => .four 0 7 1 6
  | 84 => .four 2 4 3 7
  | 85 => .four 0 2 1 7
  | 86 => .four 0 7 1 6
  | 87 => .four 0 2 1 7
  | 88 => .four 4 6 5 7
  | 89 => .four 4 6 5 7
  | 90 => .four 0 7 1 6
  | 91 => .four 0 7 1 6
  | 92 => .four 2 4 3 7
  | 93 => .four 0 2 1 7
  | 94 => .four 0 7 1 6
  | 95 => .four 0 2 1 7
  | 96 => .path ![0,1,2,3,4,5,7]
  | 97 => .four 0 5 6 7
  | 98 => .four 0 7 1 6
  | 99 => .four 0 5 6 7
  | 101 => .four 0 2 1 7
  | 102 => .four 0 7 1 6
  | 103 => .four 0 2 1 7
  | 104 => .four 3 5 4 7
  | 105 => .four 0 5 6 7
  | 106 => .four 0 7 1 6
  | 107 => .four 0 5 6 7
  | 108 => .four 3 5 4 7
  | 109 => .four 0 2 1 7
  | 110 => .four 0 7 1 6
  | 111 => .four 0 2 1 7
  | 112 => .four 4 6 5 7
  | 113 => .four 0 5 6 7
  | 114 => .four 0 7 1 6
  | 115 => .four 0 5 6 7
  | 116 => .four 2 4 3 7
  | 117 => .four 0 2 1 7
  | 118 => .four 0 7 1 6
  | 119 => .four 0 2 1 7
  | 120 => .four 3 5 4 7
  | 121 => .four 0 5 6 7
  | 122 => .four 0 7 1 6
  | 123 => .four 0 5 6 7
  | 124 => .four 2 4 3 7
  | 125 => .four 0 2 1 7
  | 126 => .four 0 7 1 6
  | 127 => .four 0 2 1 7
  | _ => .pass
private def table9 (i j : Fin 7) (b : Bool) : Cert 9 :=
  match i.val,j.val,b with
  | 0, 0, false => .four 0 3 7 8
  | 0, 0, true => .four 0 3 7 8
  | 0, 1, false => .path ![2,3,7,0,6,5,8]
  | 0, 1, true => .four 0 8 1 7
  | 0, 2, false => .hole ![0,6,8,2,3,7]
  | 0, 2, true => .four 0 8 6 7
  | 0, 3, false => .four 0 3 7 8
  | 0, 3, true => .four 0 3 7 8
  | 0, 4, false => .four 0 4 7 8
  | 0, 4, true => .four 0 4 7 8
  | 0, 5, false => .hole ![0,1,8,5,4,7]
  | 0, 5, true => .four 0 8 1 7
  | 0, 6, false => .path ![1,2,8,6,5,4,7]
  | 0, 6, true => .four 0 8 6 7
  | 1, 0, false => .path ![2,3,8,0,6,5,7]
  | 1, 0, true => .four 0 7 1 8
  | 1, 1, false => .four 1 4 7 8
  | 1, 1, true => .four 1 4 7 8
  | 1, 2, false => .path ![0,6,8,2,3,4,7]
  | 1, 2, true => .four 1 8 2 7
  | 1, 3, false => .hole ![0,1,7,4,3,8]
  | 1, 3, true => .four 0 7 1 8
  | 1, 4, false => .four 1 4 7 8
  | 1, 4, true => .four 0 7 1 8
  | 1, 5, false => .four 1 5 7 8
  | 1, 5, true => .four 1 5 7 8
  | 1, 6, false => .hole ![1,2,8,6,5,7]
  | 1, 6, true => .four 1 8 2 7
  | 2, 0, false => .hole ![0,6,7,2,3,8]
  | 2, 0, true => .four 0 7 6 8
  | 2, 1, false => .path ![0,6,7,2,3,4,8]
  | 2, 1, true => .four 1 7 2 8
  | 2, 2, false => .four 2 5 7 8
  | 2, 2, true => .four 2 5 7 8
  | 2, 3, false => .path ![1,0,8,3,4,5,7]
  | 2, 3, true => .four 0 7 6 8
  | 2, 4, false => .hole ![1,2,7,5,4,8]
  | 2, 4, true => .four 0 7 6 8
  | 2, 5, false => .four 2 5 7 8
  | 2, 5, true => .four 1 7 2 8
  | 2, 6, false => .four 2 6 7 8
  | 2, 6, true => .four 2 6 7 8
  | 3, 0, false => .four 0 3 7 8
  | 3, 0, true => .four 0 3 7 8
  | 3, 1, false => .hole ![0,1,8,4,3,7]
  | 3, 1, true => .four 0 8 1 7
  | 3, 2, false => .path ![1,0,7,3,4,5,8]
  | 3, 2, true => .four 0 8 6 7
  | 3, 3, false => .four 0 3 7 8
  | 3, 3, true => .four 0 3 7 8
  | 3, 4, false => .path ![2,1,8,4,5,6,7]
  | 3, 4, true => .four 0 7 6 8
  | 3, 5, false => .hole ![2,3,7,6,5,8]
  | 3, 5, true => .four 0 8 1 7
  | 3, 6, false => .four 3 6 7 8
  | 3, 6, true => .four 0 8 6 7
  | 4, 0, false => .four 0 4 7 8
  | 4, 0, true => .four 0 4 7 8
  | 4, 1, false => .four 1 4 7 8
  | 4, 1, true => .four 0 8 1 7
  | 4, 2, false => .hole ![1,2,8,5,4,7]
  | 4, 2, true => .four 0 8 6 7
  | 4, 3, false => .path ![2,1,7,4,5,6,8]
  | 4, 3, true => .four 0 7 1 8
  | 4, 4, false => .four 0 1 7 8
  | 4, 4, true => .four 0 1 7 8
  | 4, 5, false => .path ![3,2,8,5,6,0,7]
  | 4, 5, true => .four 0 8 1 7
  | 4, 6, false => .hole ![0,6,8,3,4,7]
  | 4, 6, true => .four 0 8 6 7
  | 5, 0, false => .hole ![0,1,7,5,4,8]
  | 5, 0, true => .four 0 7 1 8
  | 5, 1, false => .four 1 5 7 8
  | 5, 1, true => .four 1 5 7 8
  | 5, 2, false => .four 2 5 7 8
  | 5, 2, true => .four 1 8 2 7
  | 5, 3, false => .hole ![2,3,8,6,5,7]
  | 5, 3, true => .four 0 7 1 8
  | 5, 4, false => .path ![3,2,7,5,6,0,8]
  | 5, 4, true => .four 0 7 1 8
  | 5, 5, false => .four 1 2 7 8
  | 5, 5, true => .four 1 2 7 8
  | 5, 6, false => .path ![0,1,7,5,4,3,8]
  | 5, 6, true => .four 1 8 2 7
  | 6, 0, false => .path ![1,2,7,6,5,4,8]
  | 6, 0, true => .four 0 7 6 8
  | 6, 1, false => .hole ![1,2,7,6,5,8]
  | 6, 1, true => .four 1 7 2 8
  | 6, 2, false => .four 2 6 7 8
  | 6, 2, true => .four 2 6 7 8
  | 6, 3, false => .four 3 6 7 8
  | 6, 3, true => .four 0 7 6 8
  | 6, 4, false => .hole ![0,6,7,3,4,8]
  | 6, 4, true => .four 0 7 6 8
  | 6, 5, false => .path ![0,1,8,5,4,3,7]
  | 6, 5, true => .four 1 7 2 8
  | 6, 6, false => .four 2 3 7 8
  | 6, 6, true => .four 2 3 7 8
  | _, _, _ => .pass
lemma check_single : ∀ m : Fin 128, (∃ i, Mask m i) →
    (table8 m).Valid (Rel8 m) (∃ i, ∀ j, Mask m j ↔ Profile i j) := by decide
lemma check_pair : ∀ i j b, (table9 i j b).Valid (Rel9 i j b) False := by decide
def RootPath (i : Fin 7) : Fin 4 → Fin 8 :=
  ![7,i.castSucc,(i+1).castSucc,(i+2).castSucc]

def Spoke (a : Fin 7) : Fin 7 → Bool := fun i => decide (Profile a i)
private lemma rooted_check : ∀ i : Fin 7,
  (∀ a b, RootPath i a = RootPath i b → a=b) ∧
  (∀ a b, a<b → (SpokeRel (Spoke i) (RootPath i a) (RootPath i b) ↔ a.val+1=b.val)) ∧
  (∀ a, 0 < a.val → (RootPath i a).val < 7) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private lemma sound {n} {R : Fin n → Fin n → Prop} {s : Prop}
    (g : Fin n → V) (gi : Function.Injective g)
    (gr : ∀ i j, G.Adj (g i) (g j) ↔ R i j)
    (c : Cert n) (ok : c.Valid R s)
    (h4 : FourCycleFree G) (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) : s := by
  cases c with
  | pass => exact ok
  | four i j x y =>
    obtain ⟨ij,xy,a,b,c,d⟩ := ok
    exact (xy (gi (h4 _ _ _ _ (fun e => ij (gi e)) ((gr ..).mpr a) ((gr ..).mpr b)
      ((gr ..).mpr c) ((gr ..).mpr d)))).elim
  | path p =>
    exact (h7 ⟨g ∘ p,gi.comp ok.1,fun i j h => (gr ..).trans (ok.2 i j h)⟩).elim
  | hole p =>
    exact (h6 ⟨⟨g ∘ p,gi.comp ok.1,fun i j => (gr ..).trans (ok.2 i j)⟩⟩).elim

def IsProfile (H : Hole G 7) (x : V) (i : Fin 7) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ Profile i j

def OnlyFar (H : Hole G 7) (x : V) : Prop :=
  Outside H.c x ∧ ∀ i, ¬G.Adj x (H.c i)

private theorem model8 (H : Hole G 7) {x : V} (hx : Outside H.c x)
    (m : Fin 128) (hm : ∀ j, G.Adj x (H.c j) ↔ Mask m j) :
    ∃ g : Fin 8 → V, Function.Injective g ∧ (∀ j : Fin 7, g j.castSucc = H.c j) ∧
      g 7=x ∧ ∀ i j, G.Adj (g i) (g j) ↔ Rel8 m i j := by
  let g (i : Fin 8) := if h : i.val < 7 then H.c ⟨i.val,h⟩ else x
  have cg (i : Fin 7) : g i.castSucc = H.c i := by simp [g,i.isLt]
  have gx : g 7 = x := rfl
  have cases8 (i : Fin 8) : (∃ j : Fin 7, i = j.castSucc) ∨ i=7 := by
    by_cases hi : i.val < 7
    · exact Or.inl ⟨⟨_,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by have := i.isLt; change i.val = 7; omega))
  refine ⟨g,?_,cg,gx,?_⟩
  · intro a b h
    rcases cases8 a with ⟨i,rfl⟩|rfl <;> rcases cases8 b with ⟨j,rfl⟩|rfl
    · rw [cg,cg] at h
      exact congrArg Fin.castSucc (H.inj h)
    · rw [cg,gx] at h
      exact (hx i h.symm).elim
    · rw [gx,cg] at h
      exact (hx j h).elim
    · rfl
  · intro a b
    rcases cases8 a with ⟨i,rfl⟩|rfl <;> rcases cases8 b with ⟨j,rfl⟩|rfl
    · simpa [cg,Rel8,i.isLt,j.isLt] using H.adj i j
    · rw [cg,gx,G.adj_comm]
      simpa [Rel8,i.isLt,show ¬(7 : Fin 8).val < 7 by decide] using hm i
    · rw [cg,gx]
      simpa [Rel8,j.isLt,show ¬(7 : Fin 8).val < 7 by decide] using hm j
    · rw [gx]
      change G.Adj x x ↔ False
      simp [G.loopless]

theorem classify (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p) (h6 : ¬Nonempty (Hole G 6))
    {x : V} (hx : Outside H.c x) (adj : ∃ i, G.Adj x (H.c i)) :
    ∃ i, IsProfile H x i := by
  classical
  let b (i : Fin 7) := decide (G.Adj x (H.c i))
  let m := profileMask b
  have hm (i : Fin 7) : G.Adj x (H.c i) ↔ Mask m i := by
    rw [mask_cover b]
    simp [b]
  obtain ⟨i,hi⟩ := adj
  obtain ⟨g,ginj,_,_,gr⟩ := model8 H hx m hm
  obtain ⟨j,hj⟩ := sound g ginj gr _ (check_single m ⟨i,(hm _).mp hi⟩) h4 h7 h6
  exact ⟨j,hx,fun k => (hm k).trans (hj k)⟩

theorem single_front (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p) (h6 : ¬Nonempty (Hole G 6))
    {x y : V} {i j : Fin 7} (hx : IsProfile H x i) (hy : IsProfile H y j) :
    x=y := by
  classical
  apply Classical.byContradiction
  intro hxy
  let b := decide (G.Adj x y)
  have hb : b=true ↔ G.Adj x y := by simp [b]
  let g (k : Fin 9) := if hk : k.val<7 then H.c ⟨k.val,hk⟩ else if k=7 then x else y
  have cg (r : Fin 7) : g (Fin.castLE (by decide : 7 ≤ 9) r) = H.c r := by simp [g,r.isLt]
  have gx : g 7=x := rfl
  have gy : g 8=y := rfl
  have cases9 (k : Fin 9) : (∃ r : Fin 7, k = Fin.castLE (by decide : 7 ≤ 9) r) ∨ k=7 ∨ k=8 := by
    by_cases hk : k.val<7
    · exact Or.inl ⟨⟨_,hk⟩,Fin.ext rfl⟩
    · have h := k.isLt
      by_cases e : k.val=7
      · exact Or.inr (Or.inl (Fin.ext e))
      · exact Or.inr (Or.inr (Fin.ext (by change k.val=8; omega)))
  have gi : Function.Injective g := by
    intro a b h
    rcases cases9 a with ⟨r,rfl⟩|rfl|rfl <;> rcases cases9 b with ⟨s,rfl⟩|rfl|rfl
    · rw [cg,cg] at h
      exact congrArg (Fin.castLE (by decide : 7 ≤ 9)) (H.inj h)
    all_goals
      first
      | rfl
      | exfalso
        simp only [cg,gx,gy] at h
        first
        | exact hx.1 _ h
        | exact hx.1 _ h.symm
        | exact hy.1 _ h
        | exact hy.1 _ h.symm
        | exact hxy h
        | exact hxy h.symm
  have gr (a c : Fin 9) : G.Adj (g a) (g c) ↔ Rel9 i j b a c := by
    rcases cases9 a with ⟨r,rfl⟩|rfl|rfl <;> rcases cases9 c with ⟨s,rfl⟩|rfl|rfl
    · simpa [cg,Rel9,r.isLt,s.isLt] using H.adj r s
    · rw [cg,gx,G.adj_comm]
      simpa [Rel9,r.isLt,show ¬(7 : Fin 9).val < 7 by decide] using hx.2 r
    · rw [cg,gy,G.adj_comm]
      simpa [Rel9,r.isLt,show ¬(8 : Fin 9).val < 7 by decide,show (8 : Fin 9) ≠ 7 by decide] using hy.2 r
    · rw [cg,gx]
      simpa [Rel9,s.isLt,show ¬(7 : Fin 9).val < 7 by decide] using hx.2 s
    · simp [gx,G.loopless,Rel9,show ¬(7 : Fin 9).val < 7 by decide]
    · rw [gx,gy]
      change G.Adj x y ↔ (7 : Fin 9) ≠ 8 ∧ b=true
      simpa [show (7 : Fin 9) ≠ 8 by decide] using hb.symm
    · rw [cg,gy]
      simpa [Rel9,s.isLt,show ¬(8 : Fin 9).val < 7 by decide,show (8 : Fin 9) ≠ 7 by decide] using hy.2 s
    · rw [gx,gy]
      change G.Adj y x ↔ (8 : Fin 9) ≠ 7 ∧ b=true
      rw [G.adj_comm]
      simpa [show (8 : Fin 9) ≠ 7 by decide] using hb.symm
    · simp [gy,G.loopless,Rel9,show ¬(8 : Fin 9).val < 7 by decide]
  exact sound g gi gr _ (check_pair i j b) h4 h7 h6

theorem rooted4 (H : Hole G 7) {x : V} {i : Fin 7} (hx : IsProfile H x i) :
    ∃ p : Fin 4 → V, InducedPath G p ∧ p 0=x ∧ ∀ j, 0<j.val → ∃ k, p j = H.c k := by
  let m := profileMask (Spoke i)
  have hm (j) : G.Adj x (H.c j) ↔ Mask m j := by
    rw [mask_cover (Spoke i)]
    simpa [Spoke] using hx.2 j
  obtain ⟨g,gi,cg,gx,gr⟩ := model8 H hx.1 m hm
  have er (a b : Fin 8) : Rel8 m a b ↔ SpokeRel (Spoke i) a b := by
    unfold Rel8 SpokeRel
    split <;> split <;> simp [m,mask_cover]
  obtain ⟨ri,rr,rt⟩ := rooted_check i
  refine ⟨g ∘ RootPath i,⟨gi.comp ri,fun a b h => (gr ..).trans ((er ..).trans (rr a b h))⟩,gx,?_⟩
  intro j hj
  let k : Fin 7 := ⟨_,rt j hj⟩
  exact ⟨k,(congrArg g (show RootPath i j=k.castSucc from Fin.ext rfl)).trans (cg k)⟩

#print axioms classify
#print axioms single_front
#print axioms rooted4

end Graffiti133C7Only
