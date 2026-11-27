import NoFiveHoles133

namespace Graffiti133P8Heawood
open Graffiti133NoFive
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def edgeRel {n : ℕ} (es : List (ℕ × ℕ)) (i j : Fin n) : Prop :=
  (i.val,j.val) ∈ es ∨ (j.val,i.val) ∈ es

instance {n : ℕ} (es : List (ℕ × ℕ)) : DecidableRel (edgeRel (n:=n) es) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def edgeAnchor : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,7),(4,7),(0,8),(6,8)]

def edgeCore : List (ℕ × ℕ) :=
  edgeAnchor ++ [(1,9),(5,9),(2,10),(6,10),(7,11),(3,12),(8,12),(10,11)]

def edgeHeawood : List (ℕ × ℕ) := edgeCore ++ [(9,13),(11,13),(12,13)]

def Anchor : Fin 9 → Fin 9 → Prop := edgeRel edgeAnchor
instance : DecidableRel Anchor := inferInstanceAs (DecidableRel (edgeRel edgeAnchor))

def Core : Fin 13 → Fin 13 → Prop := edgeRel edgeCore
instance : DecidableRel Core := inferInstanceAs (DecidableRel (edgeRel edgeCore))

def Heawood : Fin 14 → Fin 14 → Prop := edgeRel edgeHeawood
instance : DecidableRel Heawood := inferInstanceAs (DecidableRel (edgeRel edgeHeawood))

def Profile (t : Fin 4) (i : Fin 9) : Bool :=
  decide (if t.val=0 then i.val=1 ∨ i.val=5 else
    if t.val=1 then i.val=2 ∨ i.val=6 else
    if t.val=2 then i.val=7 else i.val=3 ∨ i.val=8)

def ext {n : ℕ} (R : Fin n → Fin n → Prop) (b : Fin n → Bool)
    (i j : Fin (n+1)) : Prop :=
  if hi : i.val < n then
    if hj : j.val < n then R ⟨i.val,hi⟩ ⟨j.val,hj⟩ else b ⟨i.val,hi⟩=true
  else if hj : j.val < n then b ⟨j.val,hj⟩=true else False

instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (b : Fin n → Bool) :
    DecidableRel (ext R b) := by
  intro i j
  unfold ext
  split <;> split <;> infer_instance

@[simp] theorem ext_old {n : ℕ} (R : Fin n → Fin n → Prop) (b : Fin n → Bool)
    (i j : Fin n) : ext R b i.castSucc j.castSucc ↔ R i j := by
  simp [ext,i.isLt,j.isLt]

@[simp] theorem ext_from_old {n : ℕ} (R : Fin n → Fin n → Prop) (b : Fin n → Bool)
    (i : Fin n) : ext R b i.castSucc (Fin.last n) ↔ b i=true := by
  simp [ext,i.isLt]

@[simp] theorem ext_to_old {n : ℕ} (R : Fin n → Fin n → Prop) (b : Fin n → Bool)
    (i : Fin n) : ext R b (Fin.last n) i.castSucc ↔ b i=true := by
  simp [ext,i.isLt]

@[simp] theorem ext_last {n : ℕ} (R : Fin n → Fin n → Prop) (b : Fin n → Bool) :
    ¬ext R b (Fin.last n) (Fin.last n) := by simp [ext]

def pairMask (j : Fin 4) (e : Bool) : Fin 10 → Bool := fun k =>
  if h : k.val < 9 then Profile j ⟨k.val,h⟩ else e

@[simp] theorem pairMask_old (j : Fin 4) (e : Bool) (k : Fin 9) :
    pairMask j e k.castSucc = Profile j k := by simp [pairMask,k.isLt]

@[simp] theorem pairMask_new (j : Fin 4) (e : Bool) : pairMask j e (Fin.last 9) = e := rfl

def AnchorPair (i j : Fin 4) (e : Bool) : Fin 11 → Fin 11 → Prop :=
  ext (ext Anchor (Profile i)) (pairMask j e)
instance (i j : Fin 4) (e : Bool) : DecidableRel (AnchorPair i j e) :=
  inferInstanceAs (DecidableRel (ext (ext Anchor (Profile i)) (pairMask j e)))

def AllowedPair (i j : Fin 4) (e : Bool) : Prop :=
  let a := min i.val j.val
  let b := max i.val j.val
  (a=0 ∧ 1≤b ∧ e=false) ∨
  (a=1 ∧ b=2 ∧ e=true) ∨
  (a=1 ∧ b=3 ∧ e=false) ∨
  (a=2 ∧ (b=2 ∨ b=3 ∧ e=false))
instance (i j : Fin 4) (e : Bool) : Decidable (AllowedPair i j e) :=
  inferInstanceAs (Decidable (_ ∨ _))

def CoreMask (b : Fin 4 → Bool) (i : Fin 13) : Bool :=
  if h : 9 ≤ i.val then b ⟨i.val-9,by have := i.isLt; omega⟩ else false

def FarProfile (i : Fin 4) : Bool := decide (i.val ≠ 1)

def InjectiveFin {n m : ℕ} (p : Fin n → Fin m) : Prop :=
  ∀ i j, p i = p j → i=j
instance {n m : ℕ} (p : Fin n → Fin m) : Decidable (InjectiveFin p) :=
  inferInstanceAs (Decidable (∀ i j, p i=p j → i=j))

structure Good {n : ℕ} (R : Fin n → Fin n → Prop) : Prop where
  h4 : ∀ i j a b, i≠j → a≠b → R i a → R j a → R i b → R j b → False
  h5 : ∀ p : Fin 5 → Fin n, InjectiveFin p → (∀ i, R (p i) (p (i+1))) → False
  h8 : ∀ p : Fin 8 → Fin n, InjectiveFin p →
    (∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)) → False

inductive Cert (n : ℕ)
| pass
| four (i j a b : Fin n)
| five (p : Fin 5 → Fin n)
| eight (p : Fin 8 → Fin n)

def Cert.Valid {n : ℕ} (R : Fin n → Fin n → Prop) (s : Prop) : Cert n → Prop
| .pass => s
| .four i j a b => i≠j ∧ a≠b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .five p => InjectiveFin p ∧ ∀ i, R (p i) (p (i+1))
| .eight p => InjectiveFin p ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)

instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (s : Prop) [Decidable s] :
    DecidablePred (Cert.Valid R s) := by
  intro c
  cases c <;> unfold Cert.Valid <;> infer_instance

theorem Cert.sound {n : ℕ} {R : Fin n → Fin n → Prop} {s : Prop}
    (c : Cert n) (ok : c.Valid R s) (h : Good R) : s := by
  cases c with
  | pass => exact ok
  | four i j a b =>
    obtain ⟨ij,ab,e1,e2,e3,e4⟩ := ok
    exact (h.h4 i j a b ij ab e1 e2 e3 e4).elim
  | five p => exact (h.h5 p ok.1 ok.2).elim
  | eight p => exact (h.h8 p ok.1 ok.2).elim

def Short {n : ℕ} (R : Fin n → Fin n → Prop) (i j : Fin n) : Prop :=
  (∃ k, R i k ∧ R k j) ∨
  ∃ k l, k≠l ∧ k≠j ∧ l≠i ∧ R i k ∧ R k l ∧ R l j

theorem no_short {n : ℕ} {R : Fin n → Fin n → Prop} {b : Fin n → Bool}
    (hg : Good (ext R b)) (symm : ∀ i j, R i j → R j i) (hs : ∀ i j, R i j → i≠j)
    {i j : Fin n} (hij : i≠j) (hi : b i=true) (hj : b j=true) :
    ¬ Short R i j := by
  intro e
  rcases e with ⟨k,e1,e2⟩ | ⟨k,l,kl,kj,li,e1,e2,e3⟩
  · exact hg.h4 i.castSucc j.castSucc k.castSucc (Fin.last n)
      (fun h => hij (Fin.castSucc_injective _ h)) (Fin.ne_of_lt (Fin.castSucc_lt_last k))
      ((ext_old ..).mpr e1) ((ext_old ..).mpr (symm _ _ e2)) ((ext_from_old ..).mpr hi) ((ext_from_old ..).mpr hj)
  · let p : Fin 5 → Fin (n+1) := ![i.castSucc,k.castSucc,l.castSucc,j.castSucc,Fin.last n]
    have N (a : Fin n) : a.castSucc ≠ Fin.last n := Fin.ne_of_lt (Fin.castSucc_lt_last a)
    have hn (a b : Fin n) (h : a≠b) : a.castSucc ≠ b.castSucc :=
      fun w => h (Fin.castSucc_injective _ w)
    have D : List.Nodup [i.castSucc,k.castSucc,l.castSucc,j.castSucc,Fin.last n] := by
      simp [N,hn _ _ (hs _ _ e1),hn _ _ li.symm,hn _ _ hij,hn _ _ kl,hn _ _ kj,hn _ _ (hs _ _ e3)]
    have hI : InjectiveFin p := by
      have hinj : Function.Injective p := List.nodup_ofFn.mp (by simpa [p,List.ofFn_succ] using D)
      exact fun _ _ h => hinj h
    apply hg.h5 p hI
    intro a
    fin_cases a
    · exact (ext_old ..).mpr e1
    · exact (ext_old ..).mpr e2
    · exact (ext_old ..).mpr e3
    · exact (ext_from_old ..).mpr hj
    · exact (ext_to_old ..).mpr hi

end Graffiti133P8Heawood
