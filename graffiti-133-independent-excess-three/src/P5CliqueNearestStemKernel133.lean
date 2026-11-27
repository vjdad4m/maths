import P5CliqueIndependentFanWitness133

namespace Graffiti133P5CliqueArms.IndependentFanFinite
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 10000000

structure NearestStemSpec where
  start : Fin 4
  finish : Fin 4
  internals : Nat
  extraTail : Nat

structure NearestStemRow where
  onMask : Nat
  offMask : Nat
  path : Fin 9→Fin 16

def nearestStemFixed (S : NearestStemSpec) (x y : Fin 16) : Bool :=
    let a := min x.val y.val
    let b := max x.val y.val
    decide ((a=S.start.val ∧ b=12) ∨
          (a<4 ∧ (a=S.finish.val ∨ S.extraTail.testBit a=true) ∧ b=11+S.internals) ∨
          (12≤a ∧ b<12+S.internals ∧ a+1=b))

def nearestStemEdge (S : NearestStemSpec) (m : Nat) (x y : Fin 16) : Bool :=
  if x.val<12 ∧ y.val<12 then rawEdge m x y else nearestStemFixed S x y

def nearestStemPredicts (S : NearestStemSpec) (r : NearestStemRow)
    (x y : Fin 16) (adj : Bool) : Bool :=
  if x.val<12 ∧ y.val<12 then predict r.offMask r.onMask x y adj
  else nearestStemFixed S x y==adj

def nearestStemWitnessValid (S : NearestStemSpec) (r : NearestStemRow) : Prop :=
  (∀ i,(r.path i).val < 12+S.internals) ∧
  (∀ i j,r.path i=r.path j→i=j) ∧
  ∀ i j,i<j→nearestStemPredicts S r (r.path i) (r.path j) (decide (i.val+1=j.val))=true

instance (S : NearestStemSpec) (r : NearestStemRow) :
    Decidable (nearestStemWitnessValid S r) := by unfold nearestStemWitnessValid; infer_instance

def nearestStemCovered (m : Nat) (r : NearestStemRow) : Bool :=
  (m&&&r.onMask==r.onMask) && (m&&&r.offMask==0)

structure NearestStemCapsule where
  spec : NearestStemSpec
  survivors : List Nat
  rows : List NearestStemRow

def nearestStemCapsuleChecked (C : NearestStemCapsule) : Prop :=
  (C.rows.all (fun r=>decide (nearestStemWitnessValid C.spec r)))=true ∧
  ∀ m : Fin 35,(C.survivors.contains (masks m) || C.rows.any (nearestStemCovered (masks m)))=true

instance (C : NearestStemCapsule) : Decidable (nearestStemCapsuleChecked C) := by
  unfold nearestStemCapsuleChecked
  infer_instance

private theorem nearest_predictions_correct (S : NearestStemSpec) (r : NearestStemRow)
    (m : Nat) (selected : nearestStemCovered m r=true)
    (x y : Fin 16) (A : Bool) (yes : nearestStemPredicts S r x y A=true) :
    nearestStemEdge S m x y=A := by
  have so : m &&& r.onMask=r.onMask ∧ m &&& r.offMask=0 := by simpa [nearestStemCovered] using selected
  unfold nearestStemPredicts at yes
  unfold nearestStemEdge
  by_cases core : x.val<12 ∧ y.val<12
  · rw [if_pos core] at yes ⊢
    unfold predict at yes
    unfold rawEdge
    by_cases var : code x y<30
    · rw [if_pos var] at yes ⊢
      cases A with
      | false =>
        have b := congrArg (fun t : Nat=>t.testBit (code x y)) so.2
        simp only [Nat.testBit_and,Nat.zero_testBit] at b
        change r.offMask.testBit (code x y)=true at yes
        simpa only [yes,Bool.and_true] using b
      | true =>
        have b := congrArg (fun t : Nat=>t.testBit (code x y)) so.1
        simp only [Nat.testBit_and] at b
        change r.onMask.testBit (code x y)=true at yes
        simpa only [yes,Bool.and_true] using b
    · rw [if_neg var] at yes ⊢
      exact of_decide_eq_true yes
  · rw [if_neg core] at yes ⊢
    exact of_decide_eq_true yes

theorem nearest_stem_report_of_no_p9 {V : Type*} {G : SimpleGraph V}
    (h9 : NoPath G 9) (C : NearestStemCapsule) (cert : nearestStemCapsuleChecked C)
    (m : Fin 35) (e : Fin 16→V)
    (inj : ∀ x y, x.val<12+C.spec.internals → y.val<12+C.spec.internals →
      e x=e y → x=y)
    (fit : ∀ x y, x.val<12+C.spec.internals → y.val<12+C.spec.internals →
      (G.Adj (e x) (e y) ↔ nearestStemEdge C.spec (masks m) x y=true)) :
    masks m∈C.survivors := by
  have checked := cert.2 m
  cases keep : C.survivors.contains (masks m) with
  | true => simpa using keep
  | false =>
    simp only [keep,Bool.false_or] at checked
    obtain ⟨r,rm,p⟩ := List.any_eq_true.mp checked
    have good := of_decide_eq_true (List.all_eq_true.mp cert.1 r rm)
    obtain ⟨live,fi,fw⟩ := good
    exfalso
    apply h9
    refine ⟨e∘r.path,fun i j eq=>fi i j (inj _ _ (live i) (live j) eq),?_⟩
    intro i j ij
    rw [Function.comp_apply,Function.comp_apply,fit _ _ (live i) (live j)]
    rw [nearest_predictions_correct C.spec r (masks m) p _ _ _ (fw i j ij)]
    simp

#print axioms nearest_stem_report_of_no_p9
end Graffiti133P5CliqueArms.IndependentFanFinite
