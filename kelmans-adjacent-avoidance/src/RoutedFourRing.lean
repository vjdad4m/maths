import FourRingCyclicEquivalence

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget ThreePort
noncomputable section
variable {U J : Type*} {A : SimpleGraph U} {r : Bool→U}

def swapSlot (reverse : Bool) (s : Slot) : Slot :=
  (if reverse then !s.1 else s.1,s.2)

@[simp] theorem swapSlot_twice (reverse : Bool) (s : Slot) :
    swapSlot reverse (swapSlot reverse s)=s := by
  rcases s with ⟨d,k⟩
  cases reverse <;> cases d <;> rfl

theorem swapSlot_inj (reverse : Bool) : Function.Injective (swapSlot reverse) := by
  intro x y e
  simpa only [swapSlot_twice] using congrArg (swapSlot reverse) e

def swapAt (rev : J→Bool) (s : J×Slot) : J×Slot :=
  (s.1,swapSlot (rev s.1) s.2)

@[simp] theorem swapAt_twice (rev : J→Bool) (s : J×Slot) :
    swapAt rev (swapAt rev s)=s := by cases s; simp [swapAt]

def routedMate (next : Equiv.Perm J) (rev : J→Bool) (s : J×Slot) : J×Slot :=
  swapAt rev (mate next (swapAt rev s))

@[simp] theorem routedMate_twice (next : Equiv.Perm J) (rev : J→Bool) (s : J×Slot) :
    routedMate next rev (routedMate next rev s)=s := by
  simp only [routedMate,swapAt_twice]
  rw [mate_sq next (swapAt rev s),swapAt_twice]

variable (L : Layout A r) (next : Equiv.Perm J) (rev : J→Bool)

def routedQ (i : J) (s : Slot) : Host J r :=
  L.p (routedMate next rev (i,s)).1 (routedMate next rev (i,s)).2

theorem routedQ_not_cell (fixed : ∀i,next i≠i) (i : J) (s : Slot) :
    (L.routedQ next rev i s).1≠i := by
  change (mate next (i,swapSlot (rev i) s)).1≠i
  obtain ⟨b,c⟩ := swapSlot (rev i) s
  cases b
  · intro eq
    have e : next.symm i=i := eq
    have cancel := congrArg next e
    exact fixed i (by simpa using cancel.symm)
  · exact fixed i

/-- The same ring after each individual cell independently chooses
which of its two cap roots faces downstream. -/
def routedGraph (fixed : ∀i,next i≠i) : SimpleGraph (Host J r) where
  Adj x y := (x.1=y.1 ∧ A.Adj x.2.val y.2.val) ∨
    ∃ s : J×Slot,L.p s.1 s.2=x ∧ L.routedQ next rev s.1 s.2=y
  symm := by
    rintro x y (⟨e,adj⟩|⟨s,a,b⟩)
    · exact Or.inl ⟨e.symm,adj.symm⟩
    · exact Or.inr ⟨routedMate next rev s,b,by simpa only [routedQ,Prod.eta,routedMate_twice] using a⟩
  loopless := by
    rintro x (⟨_,adj⟩|⟨s,a,b⟩)
    · exact A.loopless _ adj
    · exact L.routedQ_not_cell next rev fixed s.1 s.2 (congrArg Prod.fst (b.trans a.symm))

instance (fixed : ∀i,next i≠i) : DecidableRel (L.routedGraph next rev fixed).Adj := Classical.decRel _

theorem routedInternal {fixed : ∀i,next i≠i} {x y : Host J r} (same : x.1=y.1) :
    (L.routedGraph next rev fixed).Adj x y ↔ A.Adj x.2.val y.2.val := by
  constructor
  · rintro (⟨_,a⟩|⟨s,ex,ey⟩)
    · exact a
    · exact (L.routedQ_not_cell next rev fixed s.1 s.2
        ((congrArg Prod.fst ey).trans (same.symm.trans (congrArg Prod.fst ex).symm))).elim
  · exact fun a=>Or.inl ⟨same,a⟩

theorem routedGraphCross {fixed : ∀i,next i≠i} {x y : Host J r} (different : x.1≠y.1) :
    (L.routedGraph next rev fixed).Adj x y ↔
      ∃ s : J×Slot,L.p s.1 s.2=x ∧ L.routedQ next rev s.1 s.2=y :=
  or_iff_right (fun h=>different h.1)

def routedStart (s : J×Bool) : Host J r := L.p s.1 (swapSlot (rev s.1) (true,s.2))
def routedEnd (s : J×Bool) : Host J r := L.p (next s.1) (swapSlot (rev (next s.1)) (false,s.2))

theorem routedQ_start (i : J) (lane : Bool) :
    L.routedQ next rev i (swapSlot (rev i) (true,lane))=L.routedEnd next rev (i,lane) := by
  simp [routedQ,routedMate,swapAt,routedEnd,mate]

theorem routedSeam_edge {fixed : ∀i,next i≠i} (i : J) (lane : Bool) :
    (L.routedGraph next rev fixed).Adj (L.routedStart rev (i,lane)) (L.routedEnd next rev (i,lane)) :=
  Or.inr ⟨(i,swapSlot (rev i) (true,lane)),rfl,L.routedQ_start next rev i lane⟩

variable [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

theorem routedCellSeam (fixed : ∀i,next i≠i) (i : J) :
    Seam (G:=L.routedGraph next rev fixed) (cell i) (L.p i) (L.routedQ next rev i) := by
  refine ⟨fun _=>mem_cell.mpr rfl,fun s h=>L.routedQ_not_cell next rev fixed i s (mem_cell.mp h),
    ?_,?_,?_⟩
  · intro a b e
    have t : (i,a)=(i,b) := L.port_inj_on_host e
    exact congrArg (fun t : J×Slot=>t.2) t
  · intro a b e
    have t := L.port_inj_on_host e
    have eq : routedMate next rev (i,a)=routedMate next rev (i,b) := t
    have orig : (i,a)=(i,b) := by simpa only [routedMate_twice] using congrArg (routedMate next rev) eq
    exact congrArg (fun t : J×Slot=>t.2) orig
  · intro x xi y yOut
    have xx := mem_cell.mp xi
    have diff : x.1≠y.1 := fun eq=>yOut (mem_cell.mpr (eq.symm.trans xx))
    rw [L.routedGraphCross next rev diff]
    constructor
    · rintro ⟨⟨k,s⟩,a,b⟩
      have eq : k=i := (congrArg Prod.fst a).trans xx
      exact ⟨s,eq ▸ a,eq ▸ b⟩
    · rintro ⟨s,a,b⟩
      exact ⟨(i,s),a,b⟩

#print axioms routedCellSeam
end
end KelmansCactus.FourRingReplica.Layout
