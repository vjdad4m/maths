import P5CliqueNearestStemKernel133
import P5CliqueIndependentTwoFan133

namespace Graffiti133P5CliqueArms.TwoFan
open SimpleGraph Graffiti133 Graffiti133Camby IndependentFanFinite
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {V : Type*} {G : SimpleGraph V}

private theorem stem_edge_symm (S : NearestStemSpec) (m : Nat) (x y : Fin 16) :
    nearestStemEdge S m x y=nearestStemEdge S m y x := by
  simp [nearestStemEdge,nearestStemFixed,rawEdge,code,Nat.min_comm,Nat.max_comm,and_comm]

/-- Lift the normalized nearest-stem certificate to an actual induced core
stem. All extra contacts from other ports are represented by the tail mask. -/
theorem nearest_stem_mask_survives
    (h9 : NoPath G 9) (D : Finset V) (p : Fin 4→V) (C : NearestStemCapsule)
    (cert : nearestStemCapsuleChecked C) (m : Fin 35) (F : Fin 12→V)
    (fi : Function.Injective F)
    (ports : ∀ i : Fin 4,F ⟨i.val,by omega⟩=p i)
    (outside : ∀ x : Fin 12,4≤x.val→F x∉D)
    (pure : ∀ x : Fin 12,4≤x.val→∀ y∈D,G.Adj (F x) y ↔ y=p ⟨x.val%4,by omega⟩)
    (fit : ∀ x y : Fin 12,G.Adj (F x) (F y)↔rawEdge (masks m) (castBase x) (castBase y)=true)
    (fst : C.spec.start≠C.spec.finish)
    (lo : 1≤C.spec.internals) (hi : C.spec.internals≤4)
    (noseed : C.spec.extraTail.testBit C.spec.start.val=false)
    (w : Fin (C.spec.internals+2)→V) (wp : InducedPath G w)
    (wo : ∀ a,w a∈D) (w0 : w 0=p C.spec.start)
    (we : w (Fin.last (C.spec.internals+1))=p C.spec.finish)
    (middle : ∀ a : Fin (C.spec.internals+2),0<a.val→a.val<C.spec.internals+1→∀ i,w a≠p i)
    (near : ∀ a : Fin (C.spec.internals+2),a.val<C.spec.internals+1→
      ∀ i≠C.spec.start,G.Adj (w a) (p i)→C.spec.internals+1≤a.val+1)
    (tails : ∀ i : Fin 4,i≠C.spec.start→i≠C.spec.finish→
      (G.Adj (p i) (w ⟨C.spec.internals,by omega⟩)↔C.spec.extraTail.testBit i.val=true)) :
    masks m∈C.survivors := by
  classical
  let n := C.spec.internals
  have nl : 1≤n := lo
  have nh : n≤4 := hi
  let I (x : Fin 16) (xl : 12≤x.val) (xh : x.val<12+n) : Fin (n+2) :=
    ⟨x.val-11,by omega⟩
  let L (x : Fin 16) (h : x.val<12) : Fin 12 := ⟨x.val,h⟩
  let e (x : Fin 16) :=
    if l : x.val<12 then F (L x l)
    else if h : x.val<12+n then w (I x (by omega) h)
    else p 0
  have eb (x : Fin 16) (xl : x.val<12) : e x=F (L x xl) := dif_pos xl
  have ei (x : Fin 16) (xl : 12≤x.val) (xh : x.val<12+n) : e x=w (I x xl xh) := by
    simp only [e,dif_neg (by omega : ¬x.val<12),dif_pos xh]
  have ep (x : Fin 16) (xp : x.val<4) : e x=p ⟨x.val,xp⟩ := by
    rw [eb x (by omega)]
    exact ports ⟨x.val,xp⟩
  have en (x : Fin 16) (xo : 4≤x.val) (xb : x.val<12) : e x∉D := by
    rw [eb x xb]
    exact outside _ xo
  have ed (x : Fin 16) (xl : 12≤x.val) (xh : x.val<12+n) : e x∈D := by
    rw [ei x xl xh]
    exact wo _
  have eNot (x : Fin 16) (xl : 12≤x.val) (xh : x.val<12+n) (j : Fin 4) : e x≠p j := by
    rw [ei x xl xh]
    have eq : (I x xl xh).val=x.val-11 := rfl
    exact middle _ (by omega) (by omega) j
  have bi (x y : Fin 16) (xb : x.val<12) (yl : 12≤y.val) (yh : y.val<12+n) : e x≠e y := by
    by_cases xp : x.val<4
    · rw [ep x xp]
      exact (eNot y yl yh ⟨x.val,xp⟩).symm
    intro eq
    exact en x (by omega) xb (eq.symm ▸ ed y yl yh)
  have eI (x y : Fin 16) (xh : x.val<12+n) (yh : y.val<12+n) (eq : e x=e y) : x=y := by
    by_cases xb : x.val<12
    · by_cases yb : y.val<12
      · rw [eb x xb,eb y yb] at eq
        exact Fin.ext (congrArg (fun t : Fin 12=>t.val) (fi eq))
      exact (bi x y xb (by omega) yh eq).elim
    by_cases yb : y.val<12
    · exact (bi y x yb (by omega) xh eq.symm).elim
    rw [ei x (by omega) xh,ei y (by omega) yh] at eq
    have v := congrArg (fun t : Fin (n+2)=>t.val) (wp.1 eq)
    change x.val-11=y.val-11 at v
    apply Fin.ext
    omega
  have up (x y : Fin 16) (xy : x.val≤y.val) (xh : x.val<12+n) (yh : y.val<12+n) :
      G.Adj (e x) (e y)↔nearestStemEdge C.spec (masks m) x y=true := by
    by_cases yb : y.val<12
    · have xb : x.val<12 := by omega
      rw [eb x xb,eb y yb,fit]
      rw [nearestStemEdge,if_pos ⟨xb,yb⟩]
      rfl
    have yl : 12≤y.val := by omega
    rw [nearestStemEdge,if_neg (fun bad=>yb bad.2)]
    unfold nearestStemFixed
    rw [Nat.min_eq_left xy,Nat.max_eq_right xy,decide_eq_true_eq]
    by_cases xb : x.val<12
    · have z : ¬(12≤x.val ∧ y.val<12+n ∧ x.val+1=y.val) := by omega
      change G.Adj (e x) (e y)↔
        (x.val=C.spec.start.val ∧ y.val=12) ∨
        (x.val<4 ∧ (x.val=C.spec.finish.val ∨ C.spec.extraTail.testBit x.val=true) ∧ y.val=11+n) ∨
        (12≤x.val ∧ y.val<12+n ∧ x.val+1=y.val)
      rw [or_iff_left z]
      by_cases xp : x.val<4
      · let i : Fin 4 := ⟨x.val,xp⟩
        rw [ep x xp,ei y yl yh]
        change G.Adj (p i) (w (I y yl yh))↔_
        by_cases si : i=C.spec.start
        · have se := congrArg (fun z : Fin 4=>z.val) si
          change x.val=C.spec.start.val at se
          have ne : x.val≠C.spec.finish.val := fun e=>fst (si.symm.trans (Fin.ext e))
          have nost : C.spec.extraTail.testBit x.val=false := se.symm ▸ noseed
          rw [si,←w0,wp.2 _ _ (by change 0<y.val-11; omega)]
          have diff : C.spec.start.val≠C.spec.finish.val := fun eq=>fst (Fin.ext eq)
          simp only [se,diff,noseed,Bool.false_eq_true,or_self,false_and,and_false,or_false,true_and]
          change 0+1=y.val-11 ↔ y.val=12
          omega
        by_cases ti : i=C.spec.finish
        · have te := congrArg (fun z : Fin 4=>z.val) ti
          change x.val=C.spec.finish.val at te
          have ne : x.val≠C.spec.start.val := fun e=>si (Fin.ext e)
          rw [ti,←we,SimpleGraph.adj_comm,wp.2 _ _ (by change y.val-11<n+1; omega)]
          have diff : C.spec.finish.val≠C.spec.start.val := fun eq=>fst (Fin.ext eq).symm
          have fld := C.spec.finish.isLt
          simp only [te,diff,fld,true_or,true_and,false_and,false_or]
          change y.val-11+1=n+1 ↔ y.val=11+n
          omega
        have nS : x.val≠C.spec.start.val := fun h=>si (Fin.ext h)
        have nT : x.val≠C.spec.finish.val := fun h=>ti (Fin.ext h)
        simp only [nS,nT,xp,false_and,false_or,true_and]
        by_cases atTail : y.val=11+n
        · have ie : I y yl yh=⟨n,by omega⟩ := Fin.ext (by change y.val-11=n; omega)
          rw [ie,tails i si ti]
          exact ⟨fun h=>⟨h,atTail⟩,fun h=>h.1⟩
        constructor
        · intro bad
          have h := near (I y yl yh) (by change y.val-11<n+1; omega) i si bad.symm
          change n+1≤y.val-11+1 at h
          exact (atTail (by omega)).elim
        · exact fun h=>(atTail h.2).elim
      have nStart : x.val≠C.spec.start.val := by have h:=C.spec.start.isLt; omega
      have no : ¬G.Adj (e x) (e y) := by
        rw [eb x xb,ei y yl yh]
        intro bad
        have hx : 4≤(L x xb).val := by change 4≤x.val; omega
        have p := (pure _ hx _ (wo _)).mp bad
        exact middle _ (by change 0<y.val-11; omega) (by change y.val-11<n+1; omega) _ p
      simp [nStart,xp,no]
    have xl : 12≤x.val := by omega
    rw [ei x xl xh,ei y yl yh]
    have nStart : x.val≠C.spec.start.val := by have q:=C.spec.start.isLt; omega
    have nPort : ¬x.val<4 := by omega
    change G.Adj (w (I x xl xh)) (w (I y yl yh))↔
      (x.val=C.spec.start.val ∧ y.val=12) ∨
      (x.val<4 ∧ (x.val=C.spec.finish.val ∨ C.spec.extraTail.testBit x.val=true) ∧ y.val=11+n) ∨
      (12≤x.val ∧ y.val<12+n ∧ x.val+1=y.val)
    simp only [nStart,nPort,false_and,false_or,xl,yh,true_and]
    by_cases equ : x=y
    · subst y
      simp
    have lt : x.val<y.val := lt_of_le_of_ne xy (fun h=>equ (Fin.ext h))
    rw [wp.2 _ _ (by change x.val-11<y.val-11; omega)]
    change x.val-11+1=y.val-11 ↔ x.val+1=y.val
    omega
  have all (x y : Fin 16) (xh : x.val<12+n) (yh : y.val<12+n) :
      G.Adj (e x) (e y)↔nearestStemEdge C.spec (masks m) x y=true := by
    by_cases xy : x.val≤y.val
    · exact up x y xy xh yh
    rw [SimpleGraph.adj_comm,stem_edge_symm]
    exact up y x (by omega) yh xh
  exact nearest_stem_report_of_no_p9 h9 C cert m e eI all

#print axioms nearest_stem_mask_survives
end Graffiti133P5CliqueArms.TwoFan
