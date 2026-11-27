import P8ModelLift133
import C9TokenData133

namespace Graffiti133CoreSeven
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133P8Heawood Graffiti133Eighth
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

def maskBit (m : Nat) (i : Fin 7) : Bool := m.testBit i.val
def encode : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n+1, b => 2 * encode n (fun j => b j.succ) + (b 0).toNat

theorem encode_bound (n : Nat) (b : Fin n → Bool) : encode n b < 2^n := by
  induction n with
  | zero => simp [encode]
  | succ n ih =>
    simp only [encode,Nat.pow_succ]
    have hh := ih (fun j => b j.succ)
    cases e : b 0 <;> simp [e] <;> omega

theorem encode_correct (n : Nat) (b : Fin n → Bool) (i : Fin n) :
    (encode n b).testBit i.val = b i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have h0 : (b 0).toNat < 2^1 := by cases e : b 0 <;> simp [e]
    have rec := Nat.testBit_two_pow_mul_add (encode n (fun j => b j.succ)) h0
    refine Fin.cases ?_ (fun j => ?_) i
    · change (2 * encode n (fun j => b j.succ) + (b 0).toNat).testBit 0 = b 0
      rw [rec]
      cases e : b 0 <;> simp [e]
    · change (2 * encode n (fun j => b j.succ) + (b 0).toNat).testBit (j.val+1) = b j.succ
      rw [rec]
      simpa using ih (fun j => b j.succ) j

def Single (m : Nat) : Fin 8 → Fin 8 → Prop := ext (@Cyclic 7) (maskBit m)
instance (m : Nat) : DecidableRel (Single m) := inferInstanceAs (DecidableRel (ext (@Cyclic 7) (maskBit m)))

def msecond (m : Nat) (e : Bool) (i : Fin 8) : Bool := if h : i.val<7 then maskBit m ⟨i.val,h⟩ else e

def Double (a b : Nat) (e : Bool) : Fin 9 → Fin 9 → Prop := ext (Single a) (msecond b e)
instance (a b : Nat) (e : Bool) : DecidableRel (Double a b e) :=
  inferInstanceAs (DecidableRel (ext (Single a) (msecond b e)))

structure Good7 {n : Nat} (R : Fin n → Fin n → Prop) : Prop where
  h4 : ∀ i j a b, i≠j → a≠b → R i a → R j a → R i b → R j b → False
  h7 : ∀ p : Fin 7 → Fin n, InjectiveFin p →
      (∀ i j, i<j → (R (p i) (p j) ↔ i.val+1=j.val)) → False

theorem modelGood7 {V : Type*} [Fintype V] {G : SimpleGraph V} {n : Nat}
    {R : Fin n → Fin n → Prop} (M : Model G R) (h4 : FourCycleFree G)
    (h7 : ¬∃ f : Fin 7 → V, InducedPath G f) : Good7 R where
  h4 := fun i j a b hij hab ha ha' hb hb' => hab (M.inj
    (h4 _ _ _ _ (M.inj.ne hij) ((M.adj _ _).mp ha) ((M.adj _ _).mp ha')
      ((M.adj _ _).mp hb) ((M.adj _ _).mp hb')))
  h7 := fun p hp edges => h7 ⟨M.f ∘ p, M.inj.comp (fun {_ _} => hp _ _),fun i j h =>
      (M.adj _ _).symm.trans (edges _ _ h)⟩

def digit (w i : Nat) := (w / 16^i) % 16

def decode {n : Nat} (w i : Nat) : Fin (n+1) :=
  ⟨digit w i % (n+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

def witnessOK {n : Nat} (R : Fin (n+1) → Fin (n+1) → Prop) [DecidableRel R]
    (pass : Bool) (w : Nat) : Bool :=
  if digit w 0 = 0 then pass else
  if digit w 0 = 1 then
    let a := decode (n:=n) w 1
    let b := decode (n:=n) w 2
    let c := decode (n:=n) w 3
    let d := decode (n:=n) w 4
    decide (a≠b ∧ c≠d ∧ R a c ∧ R b c ∧ R a d ∧ R b d)
  else
    let p := fun i : Fin 7 => decode (n:=n) w (i.val+1)
    decide (InjectiveFin p ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val + 1 = j.val))

theorem witnessOK_sound {n : Nat} (R : Fin (n+1) → Fin (n+1) → Prop) [DecidableRel R]
    (pass : Bool) (w : Nat) (hw : witnessOK R pass w = true) (hg : Good7 R) :
    pass = true := by
  unfold witnessOK at hw
  split at hw
  · exact hw
  · split at hw
    · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := of_decide_eq_true hw
      exact (hg.h4 _ _ _ _ h1 h2 h3 h4 h5 h6).elim
    · have h := of_decide_eq_true hw
      exact (hg.h7 _ h.1 h.2).elim

#print axioms witnessOK_sound
#print axioms encode_correct
end Graffiti133CoreSeven
namespace Graffiti133CoreSeven
open Graffiti133C9
def singleW : List Nat := [0, 1885684514, 1896240178, 1885684514, 1916032514, 463361, 1916032514, 463361, 1933926418, 0, 467729, 467729, 1933926418, 463361, 467729, 463361, 1951793442, 0, 0, 0, 472097, 463361, 472097, 463361, 1951793442, 0, 467729, 467729, 472097, 463361, 467729, 463361, 1967333634, 484609, 0, 484609, 0, 463361, 0, 463361, 476465, 484609, 467729, 484609, 476465, 463361, 467729, 463361, 1969230386, 484609, 0, 484609, 472097, 463361, 472097, 463361, 476465, 484609, 467729, 484609, 472097, 463361, 467729, 463361, 1985229330, 1985229330, 399105, 399105, 0, 463361, 399105, 463361, 0, 0, 399105, 399105, 0, 463361, 399105, 463361, 480833, 480833, 399105, 399105, 472097, 463361, 399105, 463361, 480833, 480833, 399105, 399105, 472097, 463361, 399105, 463361, 1967333634, 484609, 399105, 484609, 0, 463361, 399105, 463361, 476465, 484609, 399105, 484609, 476465, 463361, 399105, 463361, 480833, 484609, 399105, 484609, 472097, 463361, 399105, 463361, 476465, 484609, 399105, 484609, 472097, 463361, 399105, 463361]
def doubleW (e : Bool) : List (List Nat) := if e then
[[0, 477233, 464897, 464897, 538401, 485377, 485377, 464897, 553729, 553729, 464897, 464897, 485377, 485377], [542513, 0, 464897, 464897, 481345, 485377, 485377, 553985, 553985, 485377, 464897, 464897, 485377, 485377], [530177, 530177, 0, 481345, 469009, 469009, 542513, 530177, 530177, 530177, 469009, 554001, 469009, 469009], [530177, 530177, 546625, 0, 469009, 469009, 485457, 530177, 530177, 530177, 554257, 554257, 469009, 469009], [473121, 546625, 534289, 534289, 0, 485457, 473121, 534289, 473121, 473121, 534289, 534289, 473121, 554273], [550657, 550657, 534289, 534289, 550737, 0, 473121, 550657, 550657, 550657, 534289, 534289, 554529, 554529], [550657, 550657, 477233, 550737, 538401, 538401, 0, 550657, 550657, 550657, 538401, 477233, 538401, 538401], [530177, 553985, 464897, 464897, 469009, 485377, 485377, 0, 553985, 530177, 464897, 464897, 485377, 485377], [553729, 553985, 464897, 464897, 538401, 485377, 485377, 553985, 0, 553729, 464897, 464897, 485377, 485377], [553729, 550657, 464897, 464897, 538401, 485377, 485377, 550657, 553729, 0, 464897, 464897, 485377, 485377], [530177, 530177, 534289, 554257, 469009, 469009, 473121, 530177, 530177, 530177, 0, 554257, 469009, 469009], [530177, 530177, 554001, 554257, 469009, 469009, 542513, 530177, 530177, 530177, 554257, 0, 469009, 469009], [550657, 550657, 534289, 534289, 538401, 554529, 473121, 550657, 550657, 550657, 534289, 534289, 0, 554529], [550657, 550657, 534289, 534289, 554273, 554529, 473121, 550657, 550657, 550657, 534289, 534289, 554529, 0]]
else
[[0, 0, 0, 2237690658, 2235789330, 0, 0, 0, 553729, 553729, 0, 2237690658, 0, 2235789330], [0, 0, 0, 0, 1885700658, 1951826450, 0, 553985, 553985, 0, 1885700658, 0, 1951826450, 0], [0, 0, 0, 0, 0, 1949468162, 2253680930, 554001, 0, 2253680930, 0, 554001, 0, 1949468162], [1969259298, 0, 0, 0, 0, 0, 2202366210, 0, 1969259298, 0, 554257, 554257, 2202366210, 0], [1967357970, 2154132018, 0, 0, 0, 0, 0, 2154132018, 0, 1967357970, 554273, 0, 0, 554273], [0, 2220257810, 2217899522, 0, 0, 0, 0, 0, 2220257810, 0, 0, 2217899522, 554529, 554529], [0, 0, 1985249570, 1933934850, 0, 0, 0, 1985249570, 0, 554545, 1933934850, 0, 554545, 0], [0, 553985, 554001, 0, 1885700658, 0, 2253680930, 0, 553985, 2253680930, 1885700658, 554001, 0, 0], [553729, 553985, 0, 2237690658, 0, 1951826450, 0, 553985, 0, 553729, 0, 2237690658, 1951826450, 0], [553729, 0, 1985249570, 0, 2235789330, 0, 554545, 1985249570, 553729, 0, 0, 0, 554545, 2235789330], [0, 2154132018, 0, 554257, 554273, 0, 2202366210, 2154132018, 0, 0, 0, 554257, 2202366210, 554273], [1969259298, 0, 554001, 554257, 0, 1949468162, 0, 554001, 1969259298, 0, 554257, 0, 0, 1949468162], [0, 2220257810, 0, 1933934850, 0, 554529, 554545, 0, 2220257810, 554545, 1933934850, 0, 0, 554529], [1967357970, 0, 2217899522, 0, 554273, 554529, 0, 0, 0, 1967357970, 554273, 2217899522, 554529, 0]]
def profiles : List Nat := [9, 17, 18, 34, 36, 68, 72, 19, 25, 73, 38, 50, 76, 100]
def compatRows : List Nat := [5350, 10829, 5403, 8886, 6508, 1753, 10547, 12329, 9300, 3114, 805, 4690, 2197, 458]
def coreCert : Graffiti133C9.CliqueCert := .split 6 (.split 9 (.split 12 (.color [1, 2, 0, 1, 2, 0, 3, 2, 1, 3, 2, 0, 3, 0]) (.color [0, 2, 1, 2, 0, 2, 2, 1, 2, 2, 2, 1, 2, 2])) (.color [2, 0, 2, 1, 2, 0, 2, 2, 2, 2, 1, 1, 2, 2])) (.split 11 (.color [0, 1, 2, 2, 0, 1, 2, 2, 1, 2, 2, 2, 2, 0]) (.color [1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]))

def allowed (i j : Nat) : Bool := (compatRows.getD i 0).testBit j
def singleTest (m : Nat) : Bool :=
  witnessOK (Single m) (m==0 || profiles.contains m) (singleW.getD m 0)
def pairTest (i j : Nat) (e : Bool) : Bool :=
  witnessOK (Double (profiles.getD i 0) (profiles.getD j 0) e)
    ((i==j) || (allowed i j && !e))
    (((doubleW e).getD i []).getD j 0)
set_option maxRecDepth 80000
set_option maxHeartbeats 0
theorem singleTests : (List.range 128).all singleTest = true := by decide
theorem pairTests : (List.range 14).all (fun i =>
    (List.range 14).all fun j => pairTest i j false && pairTest i j true) = true := by decide

theorem validCoreCert : certOK allowed (List.range 14) 3 coreCert = true := by decide
theorem support_bound (T : Finset Nat) (ht : ∀ i∈T,i<14)
    (hedge : ∀ i∈T, ∀ j∈T, i≠j → allowed i j=true) : T.card ≤ 3 :=
  card_of_cliqueCert allowed coreCert (List.range 14) 3 validCoreCert T
    (fun i hi => List.mem_range.mpr (ht i hi)) hedge

#print axioms pairTests
#print axioms support_bound
end Graffiti133CoreSeven
namespace Graffiti133CoreSeven
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133P8Heawood Graffiti133Eighth
set_option linter.unusedSectionVars false

def profileMask (i : Fin 14) : Nat := profiles.getD i.val 0
def profileContacts (i : Fin 14) : Finset (Fin 7) :=
  Finset.univ.filter (fun k => maskBit (profileMask i) k = true)
def profileOK (i j : Fin 14) : Prop := allowed i.val j.val = true
instance : DecidableRel profileOK := fun _ _ => inferInstanceAs (Decidable (_=_))

theorem profile_at_least_two : ∀ i : Fin 14, 2 ≤ (profileContacts i).card := by decide
theorem profile_at_most_three : ∀ i : Fin 14, (profileContacts i).card ≤ 3 := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
def Matches (H : Hole G 7) (v : V) (i : Fin 14) : Prop :=
  ∀ k, G.Adj v (H.c k) ↔ k∈profileContacts i

private def modelOfHole (H : Hole G 7) : Model G (@Cyclic 7) := ⟨H.c,H.inj,fun i j => (H.adj i j).symm⟩

private theorem matches_mask {H : Hole G 7} {v : V} {i : Fin 14} (h : Matches H v i) :
    ∀ k, maskBit (profileMask i) k = true ↔ G.Adj v (H.c k) := by
  intro k
  simpa [profileContacts] using (h k).symm

theorem classify_profile (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ f : Fin 7 → V, InducedPath G f) (x : V) (hx : Outside H.c x)
    (n : ∃ k, G.Adj x (H.c k)) : ∃ i, Matches H x i := by
  classical
  let M := modelOfHole H
  let b := M.contacts x
  let m := encode 7 b
  have mz : m<128 := encode_bound 7 b
  have same : ∀ i, maskBit m i = true ↔ G.Adj x (M.f i) := by
    intro i
    exact (congrArg (· = true) (encode_correct 7 b i)).to_iff.trans (M.contacts_true x i)
  let N : Model G (Single m) := M.extend x hx same
  have ok := List.all_eq_true.mp singleTests m (List.mem_range.mpr mz)
  have Hmem := witnessOK_sound (Single m) (m==0 || profiles.contains m) (singleW.getD m 0)
      ok (modelGood7 N h4 h7)
  have non : m ≠ 0 := by
    intro e
    obtain ⟨i,hi⟩ := n
    have it := (same i).mpr hi
    simp [e,maskBit] at it
  have mem : m ∈ profiles := by simpa [non] using Hmem
  obtain ⟨p,hp,ep⟩ := List.getElem_of_mem mem
  have len : profiles.length = 14 := by decide
  let i : Fin 14 := ⟨p,len ▸ hp⟩
  have e : profileMask i = m := by simpa [profileMask,i,hp] using ep
  refine ⟨i,fun k => ?_⟩
  rw [profileContacts, Finset.mem_filter]
  simpa [e] using (same k).symm

theorem classify_pair (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    {x y : V} (freshX : Outside H.c x) (freshY : Outside H.c y) (xy : x ≠ y)
    {i j : Fin 14} (ij : i≠j) (hx : Matches H x i) (hy : Matches H y j) :
    profileOK i j ∧ ¬G.Adj x y := by
  classical
  let M := modelOfHole H
  let N : Model G (Single (profileMask i)) := M.extend x freshX (matches_mask hx)
  let e : Bool := decide (G.Adj y x)
  have lastEq : N.f (Fin.last 7) = x := Model.extend_f_new ..
  have fresh : N.Fresh y := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa only [lastEq] using xy.symm
    · simpa [N,M,modelOfHole] using freshY k
  have edges : ∀ k, msecond (profileMask j) e k = true ↔ G.Adj y (N.f k) := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [lastEq]
      have hlt : ¬ (Fin.last 7 : Fin 8).val < 7 := by decide
      simp only [msecond,dif_neg hlt,e,decide_eq_true_eq]
    · simpa [msecond,N,M,modelOfHole] using matches_mask hy k
  let Q : Model G (Double (profileMask i) (profileMask j) e) := N.extend y fresh edges
  have test : pairTest i.val j.val e = true := by
    have hi := List.all_eq_true.mp pairTests i.val (List.mem_range.mpr i.isLt)
    have hj := (Iff.of_eq (Bool.and_eq_true _ _)).mp (List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt))
    cases e
    · exact hj.1
    · exact hj.2
  have out := witnessOK_sound (Double (profileMask i) (profileMask j) e)
    ((i.val==j.val) || (allowed i.val j.val && !e))
    (((doubleW e).getD i.val []).getD j.val 0) test (modelGood7 Q h4 h7)
  have ne : i.val≠j.val := fun ee => ij (Fin.ext ee)
  have out' : allowed i.val j.val=true ∧ e=false := by
    simpa [ne] using out
  refine ⟨out'.1,fun h => ?_⟩
  have he : e=true := by simp [e,h.symm]
  simp [he] at out'

#print axioms classify_profile
#print axioms classify_pair
end Graffiti133CoreSeven
namespace Graffiti133CoreSeven
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem distinct_profile {H : Hole G 7} (h4 : FourCycleFree G) {x y : V}
    (ne : x≠y) {p : Fin 14} (hx : Matches H x p) (hy : Matches H y p) : False := by
  obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (profile_at_least_two p)
  exact ij (H.inj (h4 x y _ _ ne ((hx i).mpr hi) ((hy i).mpr hi)
    ((hx j).mpr hj) ((hy j).mpr hj)))

theorem outside_independent_and_core_order (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    (∀ x y, Outside H.c x → Outside H.c y → ¬ G.Adj x y) ∧ Fintype.card V≤10 := by
  classical
  have assign (x : V) (hx : Outside H.c x) := classify_profile H h4 h7 x hx (dom x hx)
  constructor
  · intro x y hx hy e
    obtain ⟨i,hi⟩ := assign x hx
    obtain ⟨j,hj⟩ := assign y hy
    have ne : i≠j := fun w => distinct_profile h4 e.ne hi (w.symm ▸ hj)
    exact (classify_pair H h4 h7 hx hy e.ne ne hi hj).2 e
  · let C := Finset.univ.image H.c
    let O := Finset.univ \ C
    let W := {x // x∈O}
    have out (x : W) : Outside H.c x.val := by
      intro i e
      have nx := (Finset.mem_sdiff.mp x.property).2
      exact nx (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    let p (x : W) : Fin 14 := Classical.choose (assign x.val (out x))
    have hit (x : W) : Matches H x.val (p x) := Classical.choose_spec (assign x.val (out x))
    have inj : Function.Injective p := by
      intro x y h
      by_contra! nxy
      exact distinct_profile h4 (fun q => nxy (Subtype.ext q)) (hit x) (h.symm ▸ hit y)
    let T := Finset.univ.image (fun x : W => (p x).val)
    have tcard : T.card=O.card := by
      have ii : Function.Injective (fun x : W => (p x).val) := Fin.val_injective.comp inj
      change (Finset.univ.image (fun x : W => (p x).val)).card=O.card
      rw [Finset.card_image_of_injective _ ii,Finset.card_univ,Fintype.card_coe]
    have cap := support_bound T (by
      intro i hi
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
      exact (p x).isLt) (by
      intro i hi j hj e
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hj
      exact (classify_pair H h4 h7 (out x) (out y) (fun w => e (congrArg (fun z : W => (p z).val) (Subtype.ext w)))
        (fun w => e (congrArg Fin.val w)) (hit x) (hit y)).1)
    have ccard : C.card = 7 := by
      rw [Finset.card_image_of_injective _ H.inj]
      simp
    have split : O.card+C.card=Fintype.card V := by
      rw [←Finset.card_univ (α:=V)]
      exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    omega

#print axioms outside_independent_and_core_order
end Graffiti133CoreSeven
namespace Graffiti133CoreSeven
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 150000

def touches (p : Fin 14) (i : Fin 7) := maskBit (profileMask p) i = true
instance (p : Fin 14) (i : Fin 7) : Decidable (touches p i) := inferInstanceAs (Decidable (_=_))

def toCore (p q r : Fin 14) (i j : Fin 7) : Prop :=
  i=j ∨ Cyclic i j ∨ (∃ k, Cyclic i k ∧ Cyclic k j) ∨
    (touches p i ∧ touches p j) ∨ (touches q i ∧ touches q j) ∨ (touches r i ∧ touches r j)
instance (p q r : Fin 14) (i j : Fin 7) : Decidable (toCore p q r i j) := by
  unfold toCore
  infer_instance

def toOutside (p : Fin 14) (i : Fin 7) : Prop :=
  touches p i ∨ ∃ k, Cyclic i k ∧ touches p k
instance (p : Fin 14) (i : Fin 7) : Decidable (toOutside p i) := by unfold toOutside; infer_instance

theorem triple_center : ∀ p q r : Fin 14, profileOK p q → profileOK p r → profileOK q r →
    ∃ i : Fin 7, (∀ j, toCore p q r i j) ∧ toOutside p i ∧ toOutside q i ∧ toOutside r i := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
private theorem radius_to (G : SimpleGraph V) (v : V) (k : ℕ) (h : ∀ w,G.dist v w≤k) :
    radius G ≤ k := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d ≤ Finset.univ.sup (G.dist v) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _ => h w))


private theorem dist2 (hc : G.Connected) {x y z : V} (e : G.Adj x y) (f : G.Adj y z) :
    G.dist x z ≤ 2 := by
  have h : G.dist x z ≤ G.dist x y + G.dist y z := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr e,dist_eq_one_iff_adj.mpr f] at h
  exact h

private theorem class_compatible {H : Hole G 7} (h4 : FourCycleFree G)
    (h7 : ¬∃ f : Fin 7 → V, InducedPath G f) {x y : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (ne : x≠y)
    {p q : Fin 14} (hp : Matches H x p) (hq : Matches H y q) : profileOK p q := by
  have pq : p≠q := fun w => distinct_profile h4 ne hp (w.symm ▸ hq)
  exact (classify_pair H h4 h7 hx hy ne pq hp hq).1

theorem order_le_nine_of_radius_three (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (h7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) (hr : 3≤radius G) :
    Fintype.card V≤9 := by
  classical
  by_contra! high
  have cap := (outside_independent_and_core_order H h4 h7 dom).2
  let C := Finset.univ.image H.c
  let O := Finset.univ \ C
  let W := {x // x∈O}
  have ccard : C.card = 7 := by rw [Finset.card_image_of_injective _ H.inj]; simp
  have split : O.card+C.card=Fintype.card V := by
    rw [←Finset.card_univ (α:=V)]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  have wcard : Fintype.card W=3 := by
    have e : Fintype.card W = O.card := Fintype.card_coe O
    omega
  let u : Fin 3 ≃ W := (Fintype.equivFinOfCardEq wcard).symm
  have out (j : Fin 3) : Outside H.c (u j).val := by
    intro i e
    have nx := (Finset.mem_sdiff.mp (u j).property).2
    exact nx (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  have ne (i j : Fin 3) (h : i≠j) : (u i).val≠(u j).val :=
    fun e => h (u.injective (Subtype.ext e))
  obtain ⟨p,hp⟩ := classify_profile H h4 h7 (u 0).val (out 0) (dom _ (out 0))
  obtain ⟨q,hq⟩ := classify_profile H h4 h7 (u 1).val (out 1) (dom _ (out 1))
  obtain ⟨r,hs⟩ := classify_profile H h4 h7 (u 2).val (out 2) (dom _ (out 2))
  obtain ⟨i,inne,pne,qne,rne⟩ := triple_center p q r
    (class_compatible h4 h7 (out 0) (out 1) (ne 0 1 (by decide)) hp hq)
    (class_compatible h4 h7 (out 0) (out 2) (ne 0 2 (by decide)) hp hs)
    (class_compatible h4 h7 (out 1) (out 2) (ne 1 2 (by decide)) hq hs)
  have old (j : Fin 7) : G.dist (H.c i) (H.c j)≤2 := by
    rcases inne j with e|e|⟨k,e,f⟩|e|e|e
    · subst j
      rw [dist_self]
      decide
    · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr e)]
      decide
    · exact dist2 hc ((H.adj i k).mpr e) ((H.adj k j).mpr f)
    · exact dist2 hc ((matches_mask hp i).mp e.1).symm ((matches_mask hp j).mp e.2)
    · exact dist2 hc ((matches_mask hq i).mp e.1).symm ((matches_mask hq j).mp e.2)
    · exact dist2 hc ((matches_mask hs i).mp e.1).symm ((matches_mask hs j).mp e.2)
  have new {a : Fin 14} {z : V} (h : Matches H z a) (t : toOutside a i) :
      G.dist (H.c i) z≤2 := by
    rcases t with t|⟨k,t,e⟩
    · rw [dist_eq_one_iff_adj.mpr ((matches_mask h i).mp t).symm]
      decide
    · exact dist2 hc ((H.adj i k).mpr t) ((matches_mask h k).mp e).symm
  have center : radius G≤2 := radius_to G (H.c i) _ (by
    intro z
    by_cases on : z∈C
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp on
      exact old j
    · have oz : z∈O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,on⟩
      obtain ⟨j,hj⟩ := u.surjective (⟨z,oz⟩ : W)
      rw [←show (u j).val=z from congrArg Subtype.val hj]
      fin_cases j
      · exact new hp pne
      · exact new hq qne
      · exact new hs rne)
  omega

#print axioms triple_center
#print axioms order_le_nine_of_radius_three
end Graffiti133CoreSeven
