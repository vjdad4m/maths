import BicycleTripleNetwork133
import BicycleShapeCheck133
import BicycleKeys133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def sizeVec (a b c : Nat) (i : Fin 3) : Nat :=
  if i.val=0 then a else if i.val=1 then b else c

def numberedRoute (a b c : Nat) (i : Fin (2+a+b+c)) : RouteIndex (sizeVec a b c) :=
  if h0 : i.val=0 then .inl false else
  if h1 : i.val=1 then .inl true else
  if h : i.val<2+a then .inr ⟨0,⟨i.val-2,by change i.val-2<a; omega⟩⟩ else
  if h : i.val<2+a+b then .inr ⟨1,⟨i.val-(2+a),by change i.val-(2+a)<b; omega⟩⟩ else
  .inr ⟨2,⟨i.val-(2+a+b),by change i.val-(2+a+b)<c; omega⟩⟩

def thetaLayout (a b c : Nat) : Prop :=
  let route := numberedRoute (a-1) (b-1) (c-1)
  let sz := sizeVec (a-1) (b-1) (c-1)
  (∀ i j, route i=route j → i=j) ∧ ∀ i j,
    routeAdj sz (fun _=>false) (fun _=>true) (∃ k,sz k=0) (route i) (route j) ↔
    thetaRelation a b c i.val j.val=true

instance (a b c : Nat) : Decidable (thetaLayout a b c) := by unfold thetaLayout; infer_instance

theorem thetaLayout_of_key (a b c : Nat) (h : (a,b,c)∈thetaKeys) :
    thetaLayout a b c := by
  simp only [thetaKeys,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> decide

def numberedDumb551 (i : Fin 10) : RouteIndex (sizeVec 4 0 4) :=
  if i.val=0 then .inl false else
  if h : i.val<5 then .inr ⟨0,⟨i.val-1,by change i.val-1<4; omega⟩⟩ else
  if i.val=5 then .inl true else .inr ⟨2,⟨i.val-6,by change i.val-6<4; omega⟩⟩

theorem dumbLayout551 :
    let sz := sizeVec 4 0 4
    let f := numberedDumb551
    (∀ i j,f i=f j → i=j) ∧ ∀ i j,
      routeAdj sz dumbStart dumbEnd (sz 1=0) (f i) (f j) ↔ dumbRelation 5 5 1 i.val j.val=true := by decide

#print axioms thetaLayout_of_key
#print axioms dumbLayout551
end Graffiti133Bicycle
