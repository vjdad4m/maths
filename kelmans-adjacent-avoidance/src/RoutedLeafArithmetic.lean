import RoutedFourRing

open scoped BigOperators
namespace KelmansCactus.AtomicBridge
open FourRingBudget ThreePort FourRingReplica.Layout FourRingPropagation
noncomputable section

abbrev sixNext := spin 6

/-- Even numbered cells face the false-root side downstream. Thus
seams 0→1 and 2→3 each meet the false-root side on both ends. -/
def leafReverse (i : Fin 6) : Bool := decide (i.val%2=0)

private theorem port_pair_sum (w : Slot→ℕ) : left w+right w=(∑ s : Slot,w s) :=
  (FourRingCap.profile_sum w).symm

/-- Numerical core of prescribed-leaf forcing. Delete one and the same
lane at seams 0→1 and 2→3. Since their phase indices differ, some adjacent
balanced cell has width zero on the corresponding false-root slot. -/
theorem forced_balanced_leaf
    (w : Fin 6→Slot→ℕ) (blocked : Bool)
    (bound : ∀i s,w i s≤2)
    (localResidue : ∀i,(∑ s : Slot,w i s)%3=1)
    (compatible : ∀ i k, Opposite (w i (true,k)) (w (sixNext i) (false,k)))
    (mark0 : w 0 (true,blocked)=0) (mark2 : w 2 (true,blocked)=0) :
    ∃ i : Fin 6,left (w i)=2 ∧ right (w i)=2 ∧
      w i (swapSlot (leafReverse i) (false,blocked))=0 := by
  let l := fun (i : Fin 6)=>left (w i)
  let r := fun (i : Fin 6)=>right (w i)
  have lb (i : Fin 6) : l i≤4 := by
    have a := bound i (false,false)
    have b := bound i (false,true)
    change w i (false,false)+w i (false,true)≤4
    omega
  have rb (i : Fin 6) : r i≤4 := by
    have a := bound i (true,false)
    have b := bound i (true,true)
    change w i (true,false)+w i (true,true)≤4
    omega
  have cell (i : Fin 6) : (l i+r i)%3=1 := by
    change (left (w i)+right (w i))%3=1
    rw [port_pair_sum]
    exact localResidue i
  have seam (i : Fin 6) : (r i+l (sixNext i))%3=0 := by
    have opposite (k : Bool) : w i (true,k)+w (sixNext i) (false,k)=0 ∨
        w i (true,k)+w (sixNext i) (false,k)=3 := by
      rcases compatible i k with h|h
      · exact Or.inl (by omega)
      · exact Or.inr h.2.2.2.2
    change (w i (true,false)+w i (true,true)+
      (w (sixNext i) (false,false)+w (sixNext i) (false,true)))%3=0
    rcases opposite false with a|a <;> rcases opposite true with b|b <;> omega
  have step (i : Fin 6) : (r (sixNext i))%3=(r i+1)%3 := by
    have h := seam i
    have g := cell (sixNext i)
    omega
  have n01 : sixNext 0=1 := by decide
  have n12 : sixNext 1=2 := by decide
  have n23 : sixNext 2=3 := by decide
  have low (i : Fin 6) (z : w i (true,blocked)=0) : r i≤2 := by
    have a := bound i (true,false)
    have b := bound i (true,true)
    change w i (true,false)+w i (true,true)≤2
    cases blocked <;> omega
  have one_mark : r (0 : Fin 6)≠0 ∨ r (2 : Fin 6)≠0 := by
    have a := step (0:Fin 6)
    have b := step (1:Fin 6)
    rw [n01] at a
    rw [n12] at b
    omega
  have sends_zero (i : Fin 6) (z : w i (true,blocked)=0) : w (sixNext i) (false,blocked)=0 := by
    rcases compatible i blocked with a|a
    · exact a.2
    · exact (by omega : False).elim
  have left_balanced (i : Fin 6) (eq : r i=2) : l i=2 := by
    have c := cell i
    have b := lb i
    omega
  have next_balanced (i : Fin 6) (eq : r i=1) : l (sixNext i)=2 ∧ r (sixNext i)=2 := by
    have e := seam i
    have c := cell (sixNext i)
    have a := lb (sixNext i)
    have b := rb (sixNext i)
    omega
  rcases one_mark with at0|at2
  · have nn := low 0 mark0
    by_cases here : r 0=2
    · exact ⟨0,left_balanced 0 here,here,by simpa [leafReverse,swapSlot] using mark0⟩
    · obtain ⟨a,b⟩ := next_balanced 0 (by omega)
      have z := sends_zero 0 mark0
      rw [n01] at a b z
      exact ⟨1,a,b,by simpa [leafReverse,swapSlot] using z⟩
  · have nn := low 2 mark2
    by_cases here : r 2=2
    · exact ⟨2,left_balanced 2 here,here,by simpa [leafReverse,swapSlot] using mark2⟩
    · obtain ⟨a,b⟩ := next_balanced 2 (by omega)
      have z := sends_zero 2 mark2
      rw [n23] at a b z
      exact ⟨3,a,b,by simpa [leafReverse,swapSlot] using z⟩

#print axioms forced_balanced_leaf
end
end KelmansCactus.AtomicBridge
