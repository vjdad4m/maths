import NestedCorePrivateAdjacentSatSpec133
import NestedCorePrivateWeightedFitHelpers133
import NestedCorePrivateExpandedRealLift133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133PrivateCross Graffiti133ExpandedPrivate
open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V}

def satLabel (f : Fin 18→V) (x : V) (z : Fin 3→V) (a : Fin 22) : V :=
  if h : a.val<18 then f ⟨a.val,h⟩
  else if he : a.val=18 then x else z ⟨a.val-19,by have := a.isLt; omega⟩

theorem sat_sites_inj (i : Fin 7) : Function.Injective (satSite i) := by
  have result : ∀ j : Fin 7,∀ a b : Fin 3,satSite j a=satSite j b→a=b := by decide
  exact result i

theorem adjacent_sat_fit (m : Bool) (i : Fin 7) (mask : Fin 8)
    (f : Fin 18→V) (x : V) (z : Fin 3→V)
    (hk : CoreKnown G m f)
    (xa : ∀ j : Fin 7,G.Adj (f (Fin.castLE (by decide) j)) x↔j=i ∨ j=i+1)
    (za : ∀ d (j : Fin 7),G.Adj (f (Fin.castLE (by decide) j)) (z d)↔j=satSite i d)
    (xz : ∀ d,G.Adj x (z d))
    (aliases : ∀ d,satAlias mask d=true → z d=f ⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩) :
    Fit G (satLabel f x z) (satSpec m i mask) := by
  apply nested_fit_sorted
  · intro a b
    simp [satSpec,min_comm,max_comm]
  intro a b t ab h
  simp only [satSpec,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<18
  · rw [dif_pos lo] at h
    rw [satLabel,dif_pos (lt_of_le_of_lt ab lo),satLabel,dif_pos lo]
    exact nested_base_fragment_sound hk h
  rw [dif_neg lo] at h
  by_cases exact18 : b.val=18
  · rw [if_pos exact18] at h
    by_cases close : a.val<7
    · rw [if_pos close,Option.some.injEq] at h
      rw [←h,satLabel,dif_pos (by omega : a.val<18),satLabel,dif_neg lo,dif_pos exact18]
      exact (xa ⟨a.val,close⟩).trans ⟨fun e=>decide_eq_true (e.imp (congrArg Fin.val) (congrArg Fin.val)),
        fun e=>(of_decide_eq_true e).imp Fin.ext Fin.ext⟩
    rw [if_neg close] at h
    by_cases rel : ∃ d : Fin 3,satAlias mask d=true ∧ a.val=9+(satSite i d).val
    · rw [if_pos rel,Option.some.injEq] at h
      subst t
      obtain ⟨d,dm,ad⟩ := rel
      have al : a.val<18 := by have := (satSite i d).isLt; omega
      rw [satLabel,dif_pos al,satLabel,dif_neg lo,dif_pos exact18]
      have e : (⟨a.val,al⟩ : Fin 18)=⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := Fin.ext ad
      rw [e,←aliases d dm]
      exact iff_of_true (xz d).symm rfl
    · rw [if_neg rel] at h
      contradiction
  rw [if_neg exact18] at h
  have bd : b.val-19<3 := by have := b.isLt; omega
  rw [dif_pos bd] at h
  let d : Fin 3 := ⟨b.val-19,bd⟩
  change (if satAlias mask d = true then none else
    if a.val<7 then some (decide (a.val=(satSite i d).val))
    else if a.val=18 then some true else none)=some t at h
  by_cases al : satAlias mask d=true
  · rw [if_pos al] at h
    contradiction
  rw [if_neg al] at h
  by_cases close : a.val<7
  · rw [if_pos close,Option.some.injEq] at h
    rw [←h,satLabel,dif_pos (by omega : a.val<18),satLabel,dif_neg lo,dif_neg exact18]
    exact (za d ⟨a.val,close⟩).trans ⟨fun e=>decide_eq_true (congrArg Fin.val e),
      fun e=>Fin.ext (of_decide_eq_true e)⟩
  rw [if_neg close] at h
  by_cases a18 : a.val=18
  · rw [if_pos a18,Option.some.injEq] at h
    subst t
    rw [satLabel,dif_neg (by omega : ¬a.val<18),dif_pos a18,satLabel,dif_neg lo,dif_neg exact18]
    exact iff_of_true (xz d) rfl
  · rw [if_neg a18] at h
    contradiction

theorem adjacent_sat_alias_exists (i : Fin 7) (f : Fin 18→V) (z : Fin 3→V) :
    ∃ mask : Fin 8,∀ d : Fin 3,satAlias mask d=true ↔
      z d=f ⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := by
  classical
  let P (d : Fin 3) : Prop := z d=f ⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩
  change ∃ mask : Fin 8,∀ d : Fin 3,satAlias mask d=true↔P d
  by_cases p0 : P 0 <;> by_cases p1 : P 1 <;> by_cases p2 : P 2
  · exact ⟨7,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide⟩
  · exact ⟨3,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨5,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨1,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨6,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨2,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨4,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩
  · exact ⟨0,by intro d; fin_cases d <;> simp_all [satAlias] <;> decide <;> decide⟩


theorem adjacent_sat_partial_inj (i : Fin 7) (mask : Fin 8)
    (f : Fin 18→V) (x : V) (z : Fin 3→V)
    (fi : Function.Injective f) (zi : Function.Injective z)
    (xf : ∀ a,x≠f a) (xz : ∀ d,x≠z d)
    (only : ∀ d a,z d=f a → a.val=9+(satSite i d).val)
    (aliases : ∀ d,satAlias mask d=true ↔ z d=f ⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩) :
    ∀ a b,satActive mask a=true → satActive mask b=true → satLabel f x z a=satLabel f x z b → a=b := by
  have act (a : Fin 22) (al : 19≤a.val) (h : satActive mask a=true) :
      satAlias mask ⟨a.val-19,by have := a.isLt; omega⟩≠true := by
    simpa [satAlias,satActive,show ¬a.val<19 by omega] using h
  have disj (d : Fin 3) (no : satAlias mask d≠true) (a : Fin 18) : z d≠f a := by
    intro eq
    apply no
    apply (aliases d).mpr
    have e : a=⟨9+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := Fin.ext (only d a eq)
    rwa [←e]
  intro a b ha hb eq
  by_cases al : a.val<18 <;> by_cases bl : b.val<18
  · rw [satLabel,dif_pos al,satLabel,dif_pos bl] at eq
    exact Fin.ext (congrArg (fun j : Fin 18=>j.val) (fi eq))
  · rw [satLabel,dif_pos al,satLabel,dif_neg bl] at eq
    by_cases b18 : b.val=18
    · rw [dif_pos b18] at eq
      exact (xf _ eq.symm).elim
    · rw [dif_neg b18] at eq
      exact (disj _ (act b (by omega) hb) _ eq.symm).elim
  · rw [satLabel,dif_neg al,satLabel,dif_pos bl] at eq
    by_cases a18 : a.val=18
    · rw [dif_pos a18] at eq
      exact (xf _ eq).elim
    · rw [dif_neg a18] at eq
      exact (disj _ (act a (by omega) ha) _ eq).elim
  · rw [satLabel,dif_neg al,satLabel,dif_neg bl] at eq
    by_cases a18 : a.val=18 <;> by_cases b18 : b.val=18
    · exact Fin.ext (a18.trans b18.symm)
    · rw [dif_pos a18,dif_neg b18] at eq
      exact (xz _ eq).elim
    · rw [dif_neg a18,dif_pos b18] at eq
      exact (xz _ eq.symm).elim
    · rw [dif_neg a18,dif_neg b18] at eq
      have sub : a.val-19=b.val-19 := congrArg Fin.val (zi eq)
      exact Fin.ext (by omega)

#print axioms adjacent_sat_partial_inj
#print axioms adjacent_sat_fit
#print axioms adjacent_sat_alias_exists
end Graffiti133NestedWeightedCore
