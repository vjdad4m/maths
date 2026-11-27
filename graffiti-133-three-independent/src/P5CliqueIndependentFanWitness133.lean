import P5CliqueIndependentFanFinite133

namespace Graffiti133P5CliqueArms.IndependentFanFinite
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
def rejectPairBits : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2),(1,3),(2,3),(4,5),(4,6),(5,6),(7,8),(7,9),(8,9),(1,4),(1,7),(4,7),(2,5),(2,8),(5,8),(3,6),(3,9),(6,9)]
def pairOK (m : Nat) : Bool :=
  rejectPairBits.all (fun ij=>!(m.testBit ij.1 && m.testBit ij.2))

theorem pair_ok_is_mask (m : Fin 1024) (h : pairOK m.val=true) :
    ∃ i : Fin 35,m.val=masks i := by
  have cert : ∀ x : Fin 1024,pairOK x.val=true→∃ i : Fin 35,x.val=masks i := by decide
  exact cert m h

def codeForward (x y : Nat) : Nat :=
  if x=y then 31 else
  if x<4 then (if 4≤y ∧ y%4=x then 30 else 31)
  else
    let a := (x-4)/4
    let b := (y-4)/4
    let i := x%4
    let j := y%4
    if a=b then (if (i==0) != (j==0) then 30 else 31)
    else if (i==0) != (j==0) then 31
    else
      let pos := if a=0 then b-1 else 2
      10*pos+(if i=0 then 0 else 1+3*(i-1)+(j-1))

def code (x y : Fin 16) : Nat := codeForward (min x.val y.val) (max x.val y.val)

def rawEdge (m : Nat) (x y : Fin 16) : Bool :=
  let c := code x y
  if c < 30 then m.testBit c else c==30

def predict (p n : Nat) (x y : Fin 16) (adj : Bool) : Bool :=
  let c := code x y
  if c<30 then (if adj then n.testBit c else p.testBit c) else (c==30)==adj

abbrev Witness := Sum (Fin 4→Fin 16) (Fin 9→Fin 16)

def witnesses : Fin 50→Witness := ![Sum.inl ![0,4,12,8],Sum.inl ![3,11,5,15],Sum.inl ![3,11,6,15],Sum.inl ![3,7,9,15],Sum.inl ![3,7,10,15],Sum.inl ![3,7,13,11],Sum.inl ![3,7,14,11],Sum.inl ![3,7,11,15],Sum.inl ![3,11,7,15],Sum.inl ![3,7,15,11],Sum.inr ![1,5,4,6,2,10,8,11,3],Sum.inr ![1,5,4,6,2,14,12,15,3],Sum.inr ![1,9,8,10,2,6,4,7,3],Sum.inr ![1,9,8,11,3,7,4,6,2],Sum.inr ![1,13,12,14,2,6,4,7,3],Sum.inr ![1,13,12,14,2,10,8,11,3],Sum.inr ![1,13,12,15,3,7,4,6,2],Sum.inr ![1,13,12,15,3,11,8,10,2],Sum.inr ![2,6,4,5,1,9,8,11,3],Sum.inr ![2,6,4,5,1,13,12,15,3],Sum.inr ![2,10,8,9,1,13,12,15,3],Sum.inr ![5,1,9,8,0,12,15,3,7],Sum.inr ![5,1,13,12,0,8,11,3,7],Sum.inr ![6,2,14,12,0,8,11,3,7],Sum.inr ![8,10,2,6,4,7,3,15,12],Sum.inr ![9,1,5,4,0,12,14,2,10],Sum.inr ![9,1,13,12,0,4,6,2,10],Sum.inr ![9,1,13,12,0,4,7,3,11],Sum.inr ![10,2,6,4,0,12,15,3,11],Sum.inr ![10,2,14,12,0,4,7,3,11],Sum.inr ![13,1,5,4,0,8,10,2,14],Sum.inr ![13,1,5,4,0,8,11,3,15],Sum.inr ![13,1,9,8,0,4,6,2,14],Sum.inr ![13,1,9,8,0,4,7,3,15],Sum.inr ![14,2,6,4,0,8,11,3,15],Sum.inr ![14,2,10,8,0,4,7,3,15],Sum.inr ![1,9,6,4,0,12,15,3,11],Sum.inr ![1,5,10,8,0,12,15,3,7],Sum.inr ![1,9,7,4,0,12,14,2,10],Sum.inr ![1,5,11,8,0,12,14,2,6],Sum.inr ![1,5,14,12,0,8,11,3,7],Sum.inr ![1,5,15,12,0,8,10,2,6],Sum.inr ![10,13,1,5,4,6,15,3,11],Sum.inr ![10,2,14,7,4,5,1,13,11],Sum.inr ![1,9,6,4,0,12,14,11,3],Sum.inr ![1,5,10,8,0,12,14,7,3],Sum.inr ![14,9,1,5,4,6,11,3,15],Sum.inr ![14,2,6,11,8,9,1,5,15],Sum.inr ![14,2,10,7,4,5,1,9,15],Sum.inr ![14,5,1,9,8,10,7,3,15]]
def lits (i : Fin 50) : Nat×Nat := clauses.getD i.val (0,0)

def validSymbolic (w : Witness) (p n : Nat) : Prop :=
  match w with
  | Sum.inl f =>
      f 0≠f 2 ∧ f 1≠f 3 ∧
      predict p n (f 0) (f 1) true=true ∧ predict p n (f 1) (f 2) true=true ∧
      predict p n (f 2) (f 3) true=true ∧ predict p n (f 3) (f 0) true=true
  | Sum.inr f =>
      (∀ i j,f i=f j→i=j) ∧
      ∀ i j,i<j→predict p n (f i) (f j) (decide (i.val+1=j.val))=true

instance (w : Witness) (p n : Nat) : Decidable (validSymbolic w p n) := by
  cases w <;> unfold validSymbolic <;> infer_instance

theorem symbolic_cert (i : Fin 50) :
    validSymbolic (witnesses i) (lits i).1 (lits i).2 := by
  have checked : ∀ i : Fin 50,validSymbolic (witnesses i) (lits i).1 (lits i).2 := by decide
  exact checked i

private theorem predicts_correct (m p n : Nat) (z : m &&& p=0) (o : m &&& n=n)
    (x y : Fin 16) (adj : Bool) (h : predict p n x y adj=true) :
    rawEdge m x y=adj := by
  unfold predict at h
  unfold rawEdge
  by_cases var : code x y<30
  · rw [if_pos var] at h ⊢
    cases adj with
    | false =>
      have bit := congrArg (fun r : Nat=>r.testBit (code x y)) z
      simp only [Nat.testBit_and,Nat.zero_testBit] at bit
      change p.testBit (code x y)=true at h
      simpa only [h,Bool.and_true] using bit
    | true =>
      have bit := congrArg (fun r : Nat=>r.testBit (code x y)) o
      simp only [Nat.testBit_and] at bit
      change n.testBit (code x y)=true at h
      simpa only [h,Bool.and_true] using bit
  · rw [if_neg var] at h ⊢
    exact of_decide_eq_true h

theorem actual_graph_passes {V : Type*} {G : SimpleGraph V} (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (e : Fin 16→V) (eI : Function.Injective e) (m : Nat)
    (fit : ∀ x y,G.Adj (e x) (e y) ↔ rawEdge m x y=true) : clauses.all (pass m)=true := by
  apply List.all_eq_true.mpr
  intro c cm
  obtain ⟨k,kk,cEq⟩ := List.getElem_of_mem cm
  have len : clauses.length=50 := by decide
  let i : Fin 50 := ⟨k,by omega⟩
  have il : lits i=c := by
    change clauses.getD k (0,0)=c
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem kk]
    change clauses[k]=c
    exact cEq
  have valid := symbolic_cert i
  rw [il] at valid
  cases b : pass m c with
  | true => rfl
  | false =>
    exfalso
    unfold pass at b
    have eq : m &&& c.1=0 ∧ m &&& c.2=c.2 := by simpa using b
    have pc := predicts_correct m c.1 c.2 eq.1 eq.2
    cases w : witnesses i with
    | inl f =>
      rw [w] at valid
      change _ at valid
      obtain ⟨v02,v13,e01,e12,e23,e30⟩ := valid
      have a01 := (fit _ _).mpr (pc _ _ true e01)
      have a12 := (fit _ _).mpr (pc _ _ true e12)
      have a23 := (fit _ _).mpr (pc _ _ true e23)
      have a30 := (fit _ _).mpr (pc _ _ true e30)
      exact v13 (eI (h4 (e (f 0)) (e (f 2)) (e (f 1)) (e (f 3))
        (fun eq=>v02 (eI eq)) a01 a12.symm a30.symm a23))
    | inr f =>
      rw [w] at valid
      obtain ⟨fi,fw⟩ := valid
      apply h9
      refine ⟨e∘f,eI.comp fi,?_⟩
      intro a b ab
      change G.Adj (e (f a)) (e (f b)) ↔ _
      rw [fit,pc _ _ _ (fw a b ab)]
      simp

#print axioms pair_ok_is_mask
#print axioms symbolic_cert
#print axioms actual_graph_passes
end Graffiti133P5CliqueArms.IndependentFanFinite
