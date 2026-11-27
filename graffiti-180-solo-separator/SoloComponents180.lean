import SoloCut180
import ComponentBalance180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A balanced component detached from the unprotected tip already
settles the single-protected branch. The argument also works without
balance and for any nonempty union of remainder components. -/
theorem solo_components_touch (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (ar : a≠r)
    (C : Finset V) (sub : C⊆univ\{a,b}) (nz : C.Nonempty) (cl : ClosedIn G (univ\{a,b}) C) :
    ∃ x∈C,G.Adj b x := by
  classical
  by_contra! none
  have ac : a∉C := fun xm => (mem_sdiff.mp (sub xm)).2 (mem_insert_self ..)
  have bc : b∉C := fun xm => (mem_sdiff.mp (sub xm)).2 (mem_insert_of_mem (mem_singleton_self _))
  have stay (x : V) (xm : x∈C) (y : V) (ed : G.Adj x y) : y=a ∨ y∈C := by
    by_cases ya : y=a
    · exact Or.inl ya
    have yb : y≠b := fun eq => none x xm (eq ▸ ed.symm)
    have ys : y∈univ\({a,b}:Finset V) := by simp [ya,yb]
    exact Or.inr ((cl x (sub xm) y ys ed).mp xm)
  let S := insert a C
  let T := univ\C
  have split : Split G a S T := by
    constructor
    · ext x;simp [S,T]
    · ext x;by_cases xa : x=a <;> simp [S,T,xa,ac]
    · intro x y ed
      by_cases xc : x∈C
      · exact Or.inl ⟨mem_insert_of_mem xc,mem_insert.mpr (stay x xc y ed)⟩
      by_cases yc : y∈C
      · exact Or.inl ⟨mem_insert.mpr (stay y yc x ed.symm),mem_insert_of_mem yc⟩
      exact Or.inr ⟨mem_sdiff.mpr ⟨mem_univ _,xc⟩,mem_sdiff.mpr ⟨mem_univ _,yc⟩⟩
    · rw [←card_univ]
      apply card_lt_card (ssubset_univ_iff.mpr ?_)
      intro full
      have h : b∈S := full ▸ mem_univ _
      exact (not_or.mpr ⟨ab.symm,bc⟩) (mem_insert.mp h)
    · rw [←card_univ]
      apply card_lt_card (ssubset_univ_iff.mpr ?_)
      obtain ⟨x,xm⟩ := nz
      intro full
      exact (mem_sdiff.mp (show x∈T from full ▸ mem_univ _)).2 xm
  exact bad (solo_cut_protected G gc hn r p A ai a b ab bi ak bk ar S T split)

#print axioms solo_components_touch
end Minimal180.PairRepair
