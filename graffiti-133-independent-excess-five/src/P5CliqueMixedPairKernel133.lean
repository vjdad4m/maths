import P5CliqueOnePortAmbientBudget133
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxHeartbeats 6000000
set_option maxRecDepth 140000

abbrev Witness (n : Nat) := Sum (Fin 4→Fin n) (Fin 9→Fin n)
structure Row (n : Nat) where
  onMask : Nat
  offMask : Nat
  trace : Witness n

structure Model (n : Nat) where
  optional : List (Fin n×Fin n)
  forced : Fin n→Nat

def optionalCode {n : Nat} (S : Model n) (x y : Fin n) : Option Nat :=
  S.optional.findIdx? (fun z=>z.1==min x y && z.2==max x y)

def edge {n : Nat} (S : Model n) (m : Nat) (x y : Fin n) : Bool :=
  match optionalCode S x y with
  | some i=>m.testBit i
  | none=>(S.forced x).testBit y.val

def predicts {n : Nat} (S : Model n) (r : Row n) (x y : Fin n) (A : Bool) : Bool :=
  match optionalCode S x y with
  | some i=>if A then r.onMask.testBit i else r.offMask.testBit i
  | none=>(S.forced x).testBit y.val==A

def valid {n : Nat} (S : Model n) (r : Row n) : Prop :=
  match r.trace with
  | .inl f =>
    f 0≠f 2 ∧ f 1≠f 3 ∧
    predicts S r (f 0) (f 1) true=true ∧ predicts S r (f 1) (f 2) true=true ∧
    predicts S r (f 2) (f 3) true=true ∧ predicts S r (f 3) (f 0) true=true
  | .inr f =>
    (∀ i j,f i=f j→i=j) ∧ ∀ i j,i<j→predicts S r (f i) (f j) (decide (i.val+1=j.val))=true

instance {n : Nat} (S : Model n) (r : Row n) : Decidable (valid S r) := by
  unfold valid
  split <;> infer_instance

inductive Tree
  | leaf (i : Nat)
  | fork (i : Nat) (no yes : Tree)

private def dummy (n : Nat) (h : 0<n) : Row n :=
  ⟨0,0,.inl (fun _=>⟨0,h⟩)⟩

def treeChecked {n : Nat} (rs : List (Row n)) (hn : 0<n) (on off : Nat) : Tree→Bool
  | .leaf i =>
    let r := rs.getD i (dummy n hn)
    decide (i<rs.length) && ((on&&&r.onMask==r.onMask) && (off&&&r.offMask==r.offMask))
  | .fork i no yes =>
    treeChecked rs hn on (off ||| 2^i) no && treeChecked rs hn (on ||| 2^i) off yes

def hit {n : Nat} (m : Nat) (r : Row n) : Prop :=
  m&&&r.onMask=r.onMask ∧ m&&&r.offMask=0

private theorem hit_from_prefix {n : Nat} (r : Row n) (m on off : Nat)
    (O : ∀ i,on.testBit i=true→m.testBit i=true)
    (Z : ∀ i,off.testBit i=true→m.testBit i=false)
    (yes : on&&&r.onMask=r.onMask) (no : off&&&r.offMask=r.offMask) :
    hit m r := by
  constructor
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases b : r.onMask.testBit j with
    | false => simp [b]
    | true =>
      have e := congrArg (fun t : Nat=>t.testBit j) yes
      change (on&&&r.onMask).testBit j=r.onMask.testBit j at e
      rw [Nat.testBit_and,b,Bool.and_true] at e
      simp [O j e,b]
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and,Nat.zero_testBit]
    cases b : r.offMask.testBit j with
    | false => simp [b]
    | true =>
      have e := congrArg (fun t : Nat=>t.testBit j) no
      change (off&&&r.offMask).testBit j=r.offMask.testBit j at e
      rw [Nat.testBit_and,b,Bool.and_true] at e
      simp [Z j e,b]

theorem tree_sound {n : Nat} (rs : List (Row n)) (hn : 0<n) (m : Nat)
    (T : Tree) (on off : Nat)
    (O : ∀ i,on.testBit i=true→m.testBit i=true)
    (Z : ∀ i,off.testBit i=true→m.testBit i=false)
    (checked : treeChecked rs hn on off T=true) :
    ∃ r∈rs,hit m r := by
  induction T generalizing on off with
  | leaf i =>
    let r := rs.getD i (dummy n hn)
    have C : i<rs.length ∧ (on&&&r.onMask=r.onMask) ∧ (off&&&r.offMask=r.offMask) := by
      simpa [treeChecked,r] using checked
    have memb : r∈rs := by
      rw [show r=rs.getD i (dummy n hn) from rfl,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem C.1]
      exact List.getElem_mem C.1
    exact ⟨r,memb,hit_from_prefix r m on off O Z C.2.1 C.2.2⟩
  | fork j no yes ihN ihY =>
    have c : treeChecked rs hn on (off ||| 2^j) no=true ∧
        treeChecked rs hn (on ||| 2^j) off yes=true := by
      simpa [treeChecked] using checked
    cases chosen : m.testBit j with
    | false =>
      apply ihN on (off ||| 2^j) O _ c.1
      intro i proof
      have x : off.testBit i=true ∨ (2^j).testBit i=true := by simpa [Nat.testBit_or] using proof
      rcases x with p|p
      · exact Z i p
      · rw [Nat.testBit_two_pow,decide_eq_true_eq] at p
        exact p ▸ chosen
    | true =>
      apply ihY (on ||| 2^j) off _ Z c.2
      intro i proof
      have x : on.testBit i=true ∨ (2^j).testBit i=true := by simpa [Nat.testBit_or] using proof
      rcases x with p|p
      · exact O i p
      · rw [Nat.testBit_two_pow,decide_eq_true_eq] at p
        exact p ▸ chosen

private theorem prediction {n : Nat} (S : Model n) (r : Row n) (m : Nat) (h : hit m r)
    (x y : Fin n) (A : Bool) (p : predicts S r x y A=true) :
    edge S m x y=A := by
  unfold predicts at p
  unfold edge
  cases eq : optionalCode S x y with
  | some i =>
    rw [eq] at p
    cases A
    · have q := congrArg (fun v : Nat=>v.testBit i) h.2
      change (m&&&r.offMask).testBit i=(0:Nat).testBit i at q
      rw [Nat.testBit_and,Nat.zero_testBit] at q
      change r.offMask.testBit i=true at p
      simpa [p] using q
    · have q := congrArg (fun v : Nat=>v.testBit i) h.1
      change (m&&&r.onMask).testBit i=r.onMask.testBit i at q
      rw [Nat.testBit_and] at q
      change r.onMask.testBit i=true at p
      simpa [p] using q
  | none =>
    rw [eq] at p
    change ((S.forced x).testBit y.val==A)=true at p
    exact of_decide_eq_true p

theorem actual_model_forbidden {n : Nat} {V : Type*} {G : SimpleGraph V} (hn : 0<n)
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (S : Model n) (rs : List (Row n)) (T : Tree)
    (soundRows : rs.all (fun r=>decide (valid S r))=true)
    (soundTree : treeChecked rs hn 0 0 T=true)
    (m : Nat) (e : Fin n→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge S m x y=true) : False := by
  obtain ⟨r,rm,h⟩ := tree_sound rs hn m T 0 0 (by simp) (by simp) soundTree
  have vl := of_decide_eq_true (List.all_eq_true.mp soundRows r rm)
  have pred := prediction S r m h
  cases rw : r.trace with
  | inl f =>
    unfold valid at vl
    rw [rw] at vl
    obtain ⟨ne02,ne13,e01,e12,e23,e30⟩ := vl
    exact ne13 (eI (h4 (e (f 0)) (e (f 2)) (e (f 1)) (e (f 3))
      (fun e=>ne02 (eI e)) ((fit _ _).mpr (pred _ _ true e01))
      ((fit _ _).mpr (pred _ _ true e12)).symm
      ((fit _ _).mpr (pred _ _ true e30)).symm
      ((fit _ _).mpr (pred _ _ true e23))))
  | inr f =>
    unfold valid at vl
    rw [rw] at vl
    obtain ⟨fi,fe⟩ := vl
    apply h9
    refine ⟨e∘f,eI.comp fi,?_⟩
    intro i j ij
    change G.Adj (e (f i)) (e (f j))↔_
    rw [fit,pred _ _ _ (fe i j ij)]
    simp

#print axioms actual_model_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
