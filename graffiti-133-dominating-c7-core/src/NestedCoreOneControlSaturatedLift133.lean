import NestedCoreOneControlModel133

namespace Graffiti133NestedOneControl
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V}

def satLabel (f : Fin 16→V) (x : V) (z : Fin 3→V) (a : Fin 20) : V :=
  if h : a.val<16 then f ⟨a.val,h⟩
  else if he : a.val=16 then x else z ⟨a.val-17,by have := a.isLt; omega⟩

theorem sat_sites_inj (i : Fin 7) : Function.Injective (satSite i) := by
  have result : ∀ j : Fin 7,∀ a b : Fin 3,satSite j a=satSite j b→a=b := by decide
  exact result i

theorem adjacent_sat_fit (i : Fin 7) (mask : Fin 8)
    (f : Fin 16→V) (x : V) (z : Fin 3→V)
    (hk : CoreKnown G f)
    (xa : ∀ j : Fin 7,G.Adj (f (Fin.castLE (by decide) j)) x↔j=i ∨ j=i+1)
    (za : ∀ d (j : Fin 7),G.Adj (f (Fin.castLE (by decide) j)) (z d)↔j=satSite i d)
    (xz : ∀ d,G.Adj x (z d))
    (aliases : ∀ d,satAlias mask d=true → z d=f ⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩) :
    Fit G (satLabel f x z) (satSpec i mask) := by
  apply nested_fit_sorted
  · intro a b
    simp [satSpec,min_comm,max_comm]
  intro a b t ab h
  simp only [satSpec,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<16
  · rw [if_pos lo] at h
    rw [satLabel,dif_pos (lt_of_le_of_lt ab lo),satLabel,dif_pos lo]
    by_cases hi : a.val<8
    · rw [if_pos hi,Option.some.injEq] at h
      rw [←h]
      simpa only [Nat.min_eq_left ab,Nat.max_eq_right ab] using
        hk ⟨a.val,lt_of_le_of_lt ab lo⟩ ⟨b.val,lo⟩ (Or.inl hi)
    · rw [if_neg hi] at h
      contradiction
  rw [if_neg lo] at h
  by_cases exact18 : b.val=16
  · rw [if_pos exact18] at h
    by_cases close : a.val<7
    · rw [if_pos close,Option.some.injEq] at h
      rw [←h,satLabel,dif_pos (by omega : a.val<16),satLabel,dif_neg lo,dif_pos exact18]
      exact (xa ⟨a.val,close⟩).trans ⟨fun e=>decide_eq_true (e.imp (congrArg Fin.val) (congrArg Fin.val)),
        fun e=>(of_decide_eq_true e).imp Fin.ext Fin.ext⟩
    rw [if_neg close] at h
    by_cases rel : ∃ d : Fin 3,satAlias mask d=true ∧ a.val=8+(satSite i d).val
    · rw [if_pos rel,Option.some.injEq] at h
      subst t
      obtain ⟨d,dm,ad⟩ := rel
      have al : a.val<16 := by have := (satSite i d).isLt; omega
      rw [satLabel,dif_pos al,satLabel,dif_neg lo,dif_pos exact18]
      have e : (⟨a.val,al⟩ : Fin 16)=⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := Fin.ext ad
      rw [e,←aliases d dm]
      exact iff_of_true (xz d).symm rfl
    · rw [if_neg rel] at h
      contradiction
  rw [if_neg exact18] at h
  have bd : b.val-17<3 := by have := b.isLt; omega
  rw [dif_pos bd] at h
  let d : Fin 3 := ⟨b.val-17,bd⟩
  change (if satAlias mask d = true then none else
    if a.val<7 then some (decide (a.val=(satSite i d).val))
    else if a.val=16 then some true else none)=some t at h
  by_cases al : satAlias mask d=true
  · rw [if_pos al] at h
    contradiction
  rw [if_neg al] at h
  by_cases close : a.val<7
  · rw [if_pos close,Option.some.injEq] at h
    rw [←h,satLabel,dif_pos (by omega : a.val<16),satLabel,dif_neg lo,dif_neg exact18]
    exact (za d ⟨a.val,close⟩).trans ⟨fun e=>decide_eq_true (congrArg Fin.val e),
      fun e=>Fin.ext (of_decide_eq_true e)⟩
  rw [if_neg close] at h
  by_cases a18 : a.val=16
  · rw [if_pos a18,Option.some.injEq] at h
    subst t
    rw [satLabel,dif_neg (by omega : ¬a.val<16),dif_pos a18,satLabel,dif_neg lo,dif_neg exact18]
    exact iff_of_true (xz d) rfl
  · rw [if_neg a18] at h
    contradiction

theorem adjacent_sat_alias_exists (i : Fin 7) (f : Fin 16→V) (z : Fin 3→V) :
    ∃ mask : Fin 8,∀ d : Fin 3,satAlias mask d=true ↔
      z d=f ⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := by
  classical
  let P (d : Fin 3) : Prop := z d=f ⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩
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
    (f : Fin 16→V) (x : V) (z : Fin 3→V)
    (fi : Function.Injective f) (zi : Function.Injective z)
    (xf : ∀ a,x≠f a) (xz : ∀ d,x≠z d)
    (only : ∀ d a,z d=f a → a.val=8+(satSite i d).val)
    (aliases : ∀ d,satAlias mask d=true ↔ z d=f ⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩) :
    ∀ a b,satActive mask a=true → satActive mask b=true → satLabel f x z a=satLabel f x z b → a=b := by
  have act (a : Fin 20) (al : 17≤a.val) (h : satActive mask a=true) :
      satAlias mask ⟨a.val-17,by have := a.isLt; omega⟩≠true := by
    simpa [satAlias,satActive,show ¬a.val<17 by omega] using h
  have disj (d : Fin 3) (no : satAlias mask d≠true) (a : Fin 16) : z d≠f a := by
    intro eq
    apply no
    apply (aliases d).mpr
    have e : a=⟨8+(satSite i d).val,by have := (satSite i d).isLt; omega⟩ := Fin.ext (only d a eq)
    rwa [←e]
  intro a b ha hb eq
  by_cases al : a.val<16 <;> by_cases bl : b.val<16
  · rw [satLabel,dif_pos al,satLabel,dif_pos bl] at eq
    exact Fin.ext (congrArg (fun j : Fin 16=>j.val) (fi eq))
  · rw [satLabel,dif_pos al,satLabel,dif_neg bl] at eq
    by_cases b18 : b.val=16
    · rw [dif_pos b18] at eq
      exact (xf _ eq.symm).elim
    · rw [dif_neg b18] at eq
      exact (disj _ (act b (by omega) hb) _ eq.symm).elim
  · rw [satLabel,dif_neg al,satLabel,dif_pos bl] at eq
    by_cases a18 : a.val=16
    · rw [dif_pos a18] at eq
      exact (xf _ eq).elim
    · rw [dif_neg a18] at eq
      exact (disj _ (act a (by omega) ha) _ eq).elim
  · rw [satLabel,dif_neg al,satLabel,dif_neg bl] at eq
    by_cases a18 : a.val=16 <;> by_cases b18 : b.val=16
    · exact Fin.ext (a18.trans b18.symm)
    · rw [dif_pos a18,dif_neg b18] at eq
      exact (xz _ eq).elim
    · rw [dif_neg a18,dif_pos b18] at eq
      exact (xz _ eq.symm).elim
    · rw [dif_neg a18,dif_neg b18] at eq
      have sub : a.val-17=b.val-17 := congrArg Fin.val (zi eq)
      exact Fin.ext (by omega)

#print axioms adjacent_sat_partial_inj
#print axioms adjacent_sat_fit
#print axioms adjacent_sat_alias_exists
end Graffiti133NestedOneControl


namespace Graffiti133NestedOneControl
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133NestedActive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V}

theorem private_adjacent_multi_not_saturated
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (i : Fin 7)
    (cert : ∀ mask : Fin 8,∃ t,checked (satSpec i mask) [] t=true ∧ usesOnly (satActive mask) t=true)
    (core : Fin 8→V) (ic : Function.Injective core)
    (known : CoreFits G core)
    (has : ∀ a : Fin 8,∃ z,PrivateFor G core a z)
    (x : V) (out : ∀ a,x≠core a)
    (xa : ∀ j : Fin 7,G.Adj x (core (csite j))↔j=i ∨ j=i+1)
    (z : Fin 3→V) (zo : ∀ d a,z d≠core a)
    (za : ∀ d (j : Fin 7),G.Adj (z d) (core (csite j))↔j=satSite i d)
    (xz : ∀ d,G.Adj x (z d)) : False := by
  classical
  choose priv pp using has
  let f := stitch core priv
  have pf : Function.Injective f := stitch_injective ic (fun j=>(pp j).1) (fun j=>(pp j).2)
  have hk : CoreKnown G f := stitch_known known (fun j=>(pp j).2)
  have site (j : Fin 7) : f (Fin.castLE (by decide) j)=core (csite j) := by
    have lt : (Fin.castLE (by decide : 7≤16) j).val<8 := lt_trans j.isLt (by decide)
    have j9 : j.val<8 := lt_trans j.isLt (by decide)
    simp [f,stitch,j9,csite]
    rfl
  have xf (a : Fin 16) : x≠f a := by
    by_cases ab : a.val<8
    · simpa [f,stitch,ab] using out ⟨a.val,ab⟩
    · dsimp only [f]
      rw [stitch,dif_neg ab]
      intro eq
      let k : Fin 8 := ⟨a.val-8,by have := a.isLt; omega⟩
      have p : PrivateFor G core k x := eq.symm ▸ pp k
      have lhs := (p.2 (csite i)).mp ((xa i).mpr (Or.inl rfl))
      have rhs := (p.2 (csite (i+1))).mp ((xa (i+1)).mpr (Or.inr rfl))
      have notEq : ∀ j : Fin 7,j≠j+1 := by decide
      exact notEq i (Fin.ext (congrArg (fun j : Fin 8=>j.val) (lhs.symm.trans rhs)))
  have zi : Function.Injective z := by
    intro d e eq
    apply sat_sites_inj i
    exact ((za e _).mp (eq ▸ (za d _).mpr rfl))
  have only (d : Fin 3) (a : Fin 16) (eq : z d=f a) : a.val=8+(satSite i d).val := by
    by_cases ab : a.val<8
    · have bad := zo d ⟨a.val,ab⟩
      exact (bad (by simpa [f,stitch,ab] using eq)).elim
    · dsimp only [f] at eq
      rw [stitch,dif_neg ab] at eq
      let k : Fin 8 := ⟨a.val-8,by have := a.isLt; omega⟩
      have p : PrivateFor G core k (z d) := eq.symm ▸ pp k
      have hx := congrArg Fin.val ((p.2 (csite (satSite i d))).mp ((za d _).mpr rfl))
      change a.val-8=(satSite i d).val at hx
      omega
  obtain ⟨mask,aliases⟩ := adjacent_sat_alias_exists i f z
  have fit : Fit G (satLabel f x z) (satSpec i mask) :=
    adjacent_sat_fit i mask f x z hk
      (by intro j; rw [site,G.adj_comm]; exact xa j)
      (by intro d j; rw [site,G.adj_comm]; exact za d j) xz (fun d=>(aliases d).mp)
  have inj := adjacent_sat_partial_inj i mask f x z pf zi xf (fun d=>(xz d).ne) only aliases
  obtain ⟨t,ct,atc⟩ := cert mask
  exact checked_active_sound h4 h9 (satActive mask) inj _ fit t [] (by intro q qm; cases qm) ct atc

#print axioms private_adjacent_multi_not_saturated
end Graffiti133NestedOneControl
