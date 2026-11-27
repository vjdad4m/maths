import NestedCorePrivateExpandedResult133

namespace Graffiti133ExpandedPrivate
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric
open scoped Classical
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

def push {n : Nat} (f : Fin n→V) (z : V) (a : Fin (n+1)) : V :=
  if h : (a.val < n) then f ⟨a.val,h⟩ else z

theorem push_injective {n : Nat} {f : Fin n→V} {z : V}
    (inj : Function.Injective f) (fresh : ∀ a,z≠f a) : Function.Injective (push f z) := by
  intro a b e
  by_cases ha : (a.val < n) <;> by_cases hb : (b.val < n)
  · rw [push,dif_pos ha,push,dif_pos hb] at e
    exact Fin.ext (congrArg (fun i : Fin n=>i.val) (inj e))
  · rw [push,dif_pos ha,push,dif_neg hb] at e
    exact (fresh _ e.symm).elim
  · rw [push,dif_neg ha,push,dif_pos hb] at e
    exact (fresh _ e).elim
  · have aa := a.isLt
    have bb := b.isLt
    exact Fin.ext (by omega)

private theorem fit_sorted {n : Nat} {f : Fin n→V} (spec : Fin n→Fin n→Option Bool)
    (sym : ∀ a b,spec a b=spec b a)
    (prove : ∀ a b t,a.val≤b.val → spec a b=some t → (G.Adj (f a) (f b)↔t=true)) :
    Fit G f spec := by
  intro a b t h
  by_cases ab : a.val≤b.val
  · exact prove a b t ab h
  · have ba : b.val≤a.val := by omega
    rw [sym] at h
    exact (G.adj_comm _ _).trans (prove b a t ba h)

def CoreKnown (G : SimpleGraph V) (m : Bool) (f : Fin 18→V) : Prop :=
  ∀ a b : Fin 18,a.val<9 ∨ b.val<9 → (G.Adj (f a) (f b)↔Graffiti133PrivateCross.base m a b=true)

private theorem base_fragment_sound {m : Bool} {f : Fin 18→V} (core : CoreKnown G m f)
    {x y : Nat} {hy : y<18} {xy : x≤y} {t : Bool}
    (cert : baseFragment m x y hy xy=some t) :
    G.Adj (f ⟨x,lt_of_le_of_lt xy hy⟩) (f ⟨y,hy⟩)↔t=true := by
  unfold baseFragment at cert
  by_cases x9 : x<9
  · rw [if_pos x9,Option.some.injEq] at cert
    rw [←cert]
    exact core _ _ (Or.inl x9)
  · rw [if_neg x9] at cert
    contradiction

theorem singleCase_fits
    (m : Bool) (c : Fin 2) (i : Fin 7) (wide opp : Bool) (f : Fin 18→V) (z : V)
    (core : CoreKnown G m f)
    (s : ∀ a : Fin 9,G.Adj (f (Fin.castLE (by decide) a)) z↔
      a.val=i.val ∨ (wide=true ∧ a.val=(i+1).val) ∨ (opp=true ∧ a.val=8-c.val))
    (forced : G.Adj (f (Graffiti133PrivateCross.forcedControl c)) z) :
    Fit G (push f z) (singleCase m c i wide opp) := by
  apply fit_sorted
  · intro a b
    simp [singleCase,min_comm,max_comm]
  intro a b t ab h
  simp only [singleCase,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<18
  · rw [dif_pos lo] at h
    rw [push,dif_pos (lt_of_le_of_lt ab lo),push,dif_pos lo]
    exact base_fragment_sound core h
  · rw [dif_neg lo] at h
    by_cases close : a.val<9
    · rw [if_pos close,Option.some.injEq] at h
      rw [←h,push,dif_pos (by omega : a.val<18),push,dif_neg lo]
      exact (s ⟨a.val,close⟩).trans ⟨decide_eq_true,of_decide_eq_true⟩
    · rw [if_neg close] at h
      by_cases eq : a.val=c.val+16
      · rw [if_pos eq,Option.some.injEq] at h
        subst t
        rw [push,dif_pos (by have := c.isLt; omega : a.val<18),push,dif_neg lo]
        have r : (⟨a.val,by have := c.isLt; omega⟩ : Fin 18)=Graffiti133PrivateCross.forcedControl c :=
          Fin.ext eq
        rw [r]
        exact iff_of_true forced rfl
      · rw [if_neg eq] at h
        contradiction

theorem dualSingleCase_fits
    (m : Bool) (i : Fin 7) (f : Fin 18→V) (z : V)
    (core : CoreKnown G m f)
    (s : ∀ a : Fin 9,G.Adj (f (Fin.castLE (by decide) a)) z↔ a.val=7 ∨ a.val=8)
    (forced : G.Adj (f (Graffiti133PrivateCross.forcedSite i)) z) :
    Fit G (push f z) (dualSingleCase m i) := by
  apply fit_sorted
  · intro a b
    simp [dualSingleCase,min_comm,max_comm]
  intro a b t ab h
  simp only [dualSingleCase,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<18
  · rw [dif_pos lo] at h
    rw [push,dif_pos (lt_of_le_of_lt ab lo),push,dif_pos lo]
    exact base_fragment_sound core h
  · rw [dif_neg lo] at h
    by_cases close : a.val<9
    · rw [if_pos close,Option.some.injEq] at h
      rw [←h,push,dif_pos (by omega : a.val<18),push,dif_neg lo]
      exact (s ⟨a.val,close⟩).trans ⟨decide_eq_true,of_decide_eq_true⟩
    · rw [if_neg close] at h
      by_cases eq : a.val=i.val+9
      · rw [if_pos eq,Option.some.injEq] at h
        subst t
        rw [push,dif_pos (by have := i.isLt; omega : a.val<18),push,dif_neg lo]
        have r : (⟨a.val,by have := i.isLt; omega⟩ : Fin 18)=Graffiti133PrivateCross.forcedSite i :=
          Fin.ext eq
        rw [r]
        exact iff_of_true forced rfl
      · rw [if_neg eq] at h
        contradiction

theorem dualAdjacentCase_fits
    (m : Bool) (i : Fin 7) (f : Fin 18→V) (r z : V)
    (core : CoreKnown G m f)
    (sr : ∀ a : Fin 9,G.Adj (f (Fin.castLE (by decide) a)) r↔ a.val=7 ∨ a.val=8)
    (sz : ∀ a : Fin 9,G.Adj (f (Fin.castLE (by decide) a)) z↔a.val=i.val ∨ a.val=(i+1).val)
    (forced : G.Adj r z) :
    Fit G (push (push f r) z) (dualAdjacentCase m i) := by
  apply fit_sorted
  · intro a b
    simp [dualAdjacentCase,min_comm,max_comm]
  intro a b t ab h
  simp only [dualAdjacentCase,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<18
  · rw [dif_pos lo] at h
    have al : a.val<18 := lt_of_le_of_lt ab lo
    rw [push,dif_pos (by omega : a.val<19),push,dif_pos al,
      push,dif_pos (by omega : b.val<19),push,dif_pos lo]
    exact base_fragment_sound core h
  · rw [dif_neg lo] at h
    by_cases exact18 : b.val=18
    · rw [if_pos exact18] at h
      by_cases close : a.val<9
      · rw [if_pos close,Option.some.injEq] at h
        rw [←h,push,dif_pos (by omega : a.val<19),push,dif_pos (by omega : a.val<18),
          push,dif_pos (by omega : b.val<19),push,dif_neg lo]
        exact (sr ⟨a.val,close⟩).trans ⟨decide_eq_true,of_decide_eq_true⟩
      · rw [if_neg close] at h
        contradiction
    · rw [if_neg exact18] at h
      by_cases close : a.val<9
      · rw [if_pos close,Option.some.injEq] at h
        rw [←h,push,dif_pos (by omega : a.val<19),push,dif_pos (by omega : a.val<18),
          push,dif_neg (by omega : ¬b.val<19)]
        exact (sz ⟨a.val,close⟩).trans ⟨decide_eq_true,of_decide_eq_true⟩
      · rw [if_neg close] at h
        by_cases a18 : a.val=18
        · rw [if_pos a18,Option.some.injEq] at h
          subst t
          rw [push,dif_pos (by omega : a.val<19),push,dif_neg (by omega : ¬a.val<18),
            push,dif_neg (by omega : ¬b.val<19)]
          exact iff_of_true forced rfl
        · rw [if_neg a18] at h
          contradiction

#print axioms singleCase_fits
#print axioms dualSingleCase_fits
#print axioms dualAdjacentCase_fits
end Graffiti133ExpandedPrivate
