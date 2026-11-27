import MinimalShore

open Finset
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Every inclusion-minimal nontrivial three-shore lies wholly on
one side of every other nontrivial three-cut, not just of a
prespecified minimal-shore pair. -/
theorem minimal_wholly_on_one_side (min : MinBoundaryThree G)
    {a s : Finset V} (A : MinimalShore G a) (S : ShoreThree G s) :
    a⊆s ∨ a⊆sᶜ := by
  classical
  refine Classical.byContradiction ?_
  intro no
  have ex (u v : Finset V) (h : ¬u⊆v) : ∃ z,z∈u∧z∉v := by
    by_contra! none
    exact h (fun z hz=>none z hz)
  obtain ⟨i,ai,si⟩ := ex a s (fun h=>no (Or.inl h))
  obtain ⟨j,aj,sj⟩ := ex a sᶜ (fun h=>no (Or.inr h))
  have inS : j∈s := by simpa using sj
  have sa : ¬s⊆a := by
    intro h
    have e := A.2 s S h
    exact si (e.symm ▸ ai)
  have ca : ¬sᶜ⊆a := by
    intro h
    have e := A.2 sᶜ (shore_compl G S) h
    exact sj (e.symm ▸ aj)
  obtain ⟨u,us,ua⟩ := ex s a sa
  obtain ⟨v,vc,va⟩ := ex sᶜ a ca
  apply no_crossing_minimum_three_cuts G min (colourOf a) (colourOf s) A.1.1 S.1
  intro p q
  cases p <;> cases q
  · exact ⟨v,colour_false.mpr va,colour_false.mpr (mem_compl.mp vc)⟩
  · exact ⟨u,colour_false.mpr ua,colour_true.mpr us⟩
  · exact ⟨i,colour_true.mpr ai,colour_false.mpr si⟩
  · exact ⟨j,colour_true.mpr aj,colour_true.mpr inS⟩

#print axioms minimal_wholly_on_one_side
end
end KelmansCactus.AtomicBridge.OddUncross
