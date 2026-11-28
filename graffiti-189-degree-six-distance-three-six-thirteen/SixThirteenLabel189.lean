import SixTwelveLabel189
import SixThirteenFromGraph189
import Mathlib.Logic.Equiv.Fin.Basic

namespace Graffiti189LongestPath.SixThirteenSat
open Finset SimpleGraph
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000

theorem role_preserving_equiv_with_exception {Y I : Type*} [Fintype Y]
    [DecidableEq I] (f : V→I) (g : Y→I) (high : Y→Prop)
    (low : Option V)
    (cards : ∀ i,Fintype.card {x : V // f x=i}=Fintype.card {y : Y // g y=i})
    (unique : ∀ y z,¬high y → ¬high z → y=z)
    (distinguished : ∀ y,¬high y → ∃ i,low=some i ∧ f i=g y) :
    ∃ e : V ≃ Y,(∀ i,g (e i)=f i) ∧ ∀ i,low≠some i → high (e i) := by
  classical
  obtain ⟨e,roles⟩ := SixTwelveSat.role_preserving_equiv f g cards
  by_cases single : ∃ y,¬high y
  · obtain ⟨y,ylo⟩ := single
    obtain ⟨j,jlow,jr⟩ := distinguished y ylo
    let k := e.symm y
    have ek : e k=y := e.apply_symm_apply y
    have fkj : f k=f j := (roles k).symm.trans (ek.symm ▸ jr.symm)
    let e' := (Equiv.swap j k).trans e
    have fs (i : V) : f (Equiv.swap j k i)=f i := by
      by_cases ij : i=j
      · subst i
        simpa only [Equiv.swap_apply_left] using fkj
      by_cases ik : i=k
      · subst i
        simpa only [Equiv.swap_apply_right] using fkj.symm
      rw [Equiv.swap_apply_of_ne_of_ne ij ik]
    have ej : e' j=y := by simpa [e',Equiv.trans_apply] using ek
    refine ⟨e',fun i=>(roles _).trans (fs i),?_⟩
    intro i hi
    by_contra ilo
    have eq := unique (e' i) y ilo ylo
    have ij := e'.injective (eq.trans ej.symm)
    exact hi (ij.symm ▸ jlow)
  · push_neg at single
    exact ⟨e,roles,fun i _=>single (e i)⟩

#print axioms role_preserving_equiv_with_exception
end Graffiti189LongestPath.SixThirteenSat
