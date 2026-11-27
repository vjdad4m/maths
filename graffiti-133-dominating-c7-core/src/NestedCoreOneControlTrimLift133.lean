import NestedCoreOneControlModel133
import NestedCorePrivateExpandedFit133

namespace Graffiti133NestedOneControl
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133ExpandedPrivate Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V}

theorem trim_single_fit (i : Fin 7) (f : Fin 16→V)
    (known : CoreKnown G f)
    (hit : G.Adj (f (embedPrivate (csite i))) (f 15)) :
    Fit G f (forcedTrimSpec i false) := by
  apply nested_fit_sorted
  · intro a b
    simp [forcedTrimSpec,trimSpec,min_comm,max_comm]
  intro a b t ab eq
  simp only [forcedTrimSpec,trimSpec,Bool.false_eq_true,if_false,
    Nat.min_eq_left ab,Nat.max_eq_right ab] at eq
  by_cases yes : a.val=i.val+8 ∧ b.val=15
  · rw [if_pos yes,Option.some.injEq] at eq
    subst t
    have ea : a=embedPrivate (csite i) := Fin.ext yes.1
    have eb : b=15 := Fin.ext yes.2
    rw [ea,eb]
    exact iff_of_true hit rfl
  rw [if_neg yes] at eq
  rw [if_pos b.isLt] at eq
  by_cases low : a.val<8
  · rw [if_pos low,Option.some.injEq] at eq
    rw [←eq]
    simpa only [Nat.min_eq_left ab,Nat.max_eq_right ab] using known a b (Or.inl low)
  · rw [if_neg low] at eq
    contradiction

theorem trim_wide_fit (i : Fin 7) (f : Fin 16→V) (z : V)
    (known : CoreKnown G f)
    (site : ∀ a : Fin 8,G.Adj (f (embedCore a)) z ↔ a.val=i.val ∨ a.val=(i+1).val)
    (hit : G.Adj (f 15) z) :
    Fit G (push f z) (forcedTrimSpec i true) := by
  apply nested_fit_sorted
  · intro a b
    simp [forcedTrimSpec,trimSpec,min_comm,max_comm]
  intro a b t ab eq
  simp only [forcedTrimSpec,trimSpec,if_true,Nat.min_eq_left ab,Nat.max_eq_right ab] at eq
  by_cases lo : b.val<16
  · rw [if_pos lo] at eq
    by_cases low : a.val<8
    · rw [if_pos low,Option.some.injEq] at eq
      rw [←eq,push,dif_pos (lt_of_le_of_lt ab lo),push,dif_pos lo]
      simpa only [Nat.min_eq_left ab,Nat.max_eq_right ab] using
        known ⟨a.val,lt_of_le_of_lt ab lo⟩ ⟨b.val,lo⟩ (Or.inl low)
    · rw [if_neg low] at eq
      contradiction
  rw [if_neg lo,if_pos (show b.val=16 by have := b.isLt; omega)] at eq
  by_cases low : a.val<8
  · rw [if_pos low,Option.some.injEq] at eq
    rw [←eq,push,dif_pos (by omega : a.val<16),push,dif_neg lo]
    exact (site ⟨a.val,low⟩).trans ⟨decide_eq_true,of_decide_eq_true⟩
  rw [if_neg low] at eq
  by_cases yes : a.val=15
  · rw [if_pos yes,Option.some.injEq] at eq
    subst t
    rw [push,dif_pos (by omega : a.val<16),push,dif_neg lo]
    have ea : (⟨a.val,by omega⟩ : Fin 16)=15 := Fin.ext yes
    rw [ea]
    exact iff_of_true hit rfl
  · rw [if_neg yes] at eq
    contradiction

theorem no_unpaid_short_crossing
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (cert : ∀ (i : Fin 7) (wide : Bool),∃ t,checked (forcedTrimSpec i wide) [] t=true)
    (c : Fin 8→V) (ci : Function.Injective c) (known : CoreFits G c)
    (has : ∀ j : Fin 8,∃ w,PrivateFor G c j w)
    (i : Fin 7) (wide : Bool) (r z : V) (rp : PrivateFor G c 7 r)
    (zo : ∀ a : Fin 8,z≠c a)
    (zs : ∀ a : Fin 8,G.Adj z (c a) ↔ a.val=i.val ∨ (wide=true ∧ a.val=(i+1).val)) :
    ¬G.Adj r z := by
  classical
  intro ed
  choose p pp using has
  have distinct : csite i≠7 := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val=7 at h
    exact (Nat.ne_of_lt i.isLt) h
  cases wide
  · have zp : PrivateFor G c (csite i) z := ⟨zo,fun a=>by
      exact (zs a).trans ⟨fun h=>Fin.ext ((h.resolve_right (fun q=>Bool.noConfusion q.1)).symm),
        fun h=>Or.inl (congrArg (fun q : Fin 8=>q.val) h.symm)⟩⟩
    let q (j : Fin 8) := if j=7 then r else if j=csite i then z else p j
    have qq (a : Fin 8) : PrivateFor G c a (q a) := by
      by_cases a7 : a=7
      · subst a
        simpa [q] using rp
      · by_cases ai : a=csite i
        · subst a
          simpa [q,distinct] using zp
        · simpa [q,a7,ai] using pp a
    let f := stitch c q
    have fi := stitch_injective ci (fun j=>(qq j).1) (fun j=>(qq j).2)
    have k : CoreKnown G f := stitch_known known (fun j=>(qq j).2)
    have forced : G.Adj (f (embedPrivate (csite i))) (f 15) := by
      change G.Adj (stitch c q (embedPrivate (csite i))) (stitch c q (embedPrivate 7))
      rw [stitch_at_private,stitch_at_private]
      simpa [q,distinct] using ed.symm
    obtain ⟨t,rt⟩ := cert i false
    exact checked_sound h4 h9 fi _ (trim_single_fit i f k forced) t [] (by intro a no; cases no) rt
  · let q (j : Fin 8) := if j=7 then r else p j
    have qq (a : Fin 8) : PrivateFor G c a (q a) := by
      by_cases a7 : a=7
      · subst a
        simpa [q] using rp
      · simpa [q,a7] using pp a
    let f := stitch c q
    have fi := stitch_injective ci (fun j=>(qq j).1) (fun j=>(qq j).2)
    have k : CoreKnown G f := stitch_known known (fun j=>(qq j).2)
    have fresh (a : Fin 16) : z≠f a := by
      by_cases lo : a.val<8
      · simpa [f,stitch,lo] using zo ⟨a.val,lo⟩
      · dsimp only [f]
        rw [stitch,dif_neg lo]
        intro eq
        let b : Fin 8 := ⟨a.val-8,by have := a.isLt; omega⟩
        have h : PrivateFor G c b z := eq.symm ▸ qq b
        have h0 := (h.2 (csite i)).1 ((zs _).2 (Or.inl rfl))
        have h1 := (h.2 (csite (i+1))).1 ((zs _).2 (Or.inr ⟨rfl,rfl⟩))
        have neq : ∀ i : Fin 7,i≠i+1 := by decide
        exact neq i (Fin.ext (congrArg (fun a : Fin 8=>a.val) (h0.symm.trans h1)))
    have site (a : Fin 8) : G.Adj (f (embedCore a)) z ↔ a.val=i.val ∨ a.val=(i+1).val := by
      change G.Adj (stitch c q (embedCore a)) z ↔ _
      rw [stitch_at_core,G.adj_comm]
      simpa only [true_and] using zs a
    have force : G.Adj (f 15) z := by
      change G.Adj (stitch c q (embedPrivate 7)) z
      rw [stitch_at_private]
      simpa [q] using ed
    obtain ⟨t,rt⟩ := cert i true
    exact checked_sound h4 h9 (push_injective fi fresh) _ (trim_wide_fit i f z k site force)
      t [] (by intro a no; cases no) rt

#print axioms no_unpaid_short_crossing
end Graffiti133NestedOneControl
