import CambyPathEnds133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} {a b : Nat}

theorem concat_induced_paths {F : Fin a→V} {J : Fin b→V}
    (hf : InducedPath G F) (hj : InducedPath G J)
    (apart : ∀ i j,F i≠J j)
    (joint : ∀ i j,G.Adj (F i) (J j) ↔ i.val+1=a ∧ j.val=0) :
    InducedPath G (Fin.addCases F J) := by
  constructor
  · intro i j
    revert j
    refine Fin.addCases ?_ ?_ i
    · intro x j
      refine Fin.addCases ?_ ?_ j
      · intro y e
        simp only [Fin.addCases_left] at e
        exact congrArg (Fin.castAdd b) (hf.1 e)
      · intro y e
        simp only [Fin.addCases_left,Fin.addCases_right] at e
        exact (apart x y e).elim
    · intro x j
      refine Fin.addCases ?_ ?_ j
      · intro y e
        simp only [Fin.addCases_left,Fin.addCases_right] at e
        exact (apart y x e.symm).elim
      · intro y e
        simp only [Fin.addCases_right] at e
        exact congrArg (Fin.natAdd a) (hj.1 e)
  · intro i j
    revert j
    refine Fin.addCases ?_ ?_ i
    · intro x j
      refine Fin.addCases ?_ ?_ j
      · intro y lt
        simp only [Fin.addCases_left]
        exact hf.2 x y lt
      · intro y _
        simp only [Fin.addCases_left,Fin.addCases_right]
        rw [joint]
        change (x.val+1=a ∧ y.val=0) ↔ x.val+1=a+y.val
        have xb := x.isLt
        omega
    · intro x j
      refine Fin.addCases ?_ ?_ j
      · intro y lt
        have xlt : a+x.val<y.val := lt
        have yb := y.isLt
        omega
      · intro y lt
        simp only [Fin.addCases_right]
        have xl : a+x.val<a+y.val := lt
        have xy : x<y := by change x.val<y.val; omega
        rw [hj.2 x y xy]
        change x.val+1=y.val ↔ a+x.val+1=a+y.val
        omega

#print axioms concat_induced_paths
end Graffiti133Bicycle
