import NestedCorePrivateAdjacentSatFit133
import NestedCorePrivateActiveKernel133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133PrivateCross Graffiti133ExpandedPrivate Graffiti133NestedActive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V}

theorem private_adjacent_multi_not_saturated
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (i : Fin 7)
    (cert : ∀ mask : Fin 8,∃ t,checked (satSpec m i mask) [] t=true ∧ usesOnly (satActive mask) t=true)
    (core : Fin 9→V) (ic : Function.Injective core)
    (known : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ a : Fin 9,∃ z,PrivateFor G core a z)
    (x : V) (out : ∀ a,x≠core a)
    (xa : ∀ j : Fin 7,G.Adj x (core (sIndex j))↔j=i ∨ j=i+1)
    (z : Fin 3→V) (zo : ∀ d a,z d≠core a)
    (za : ∀ d (j : Fin 7),G.Adj (z d) (core (sIndex j))↔j=satSite i d)
    (xz : ∀ d,G.Adj x (z d)) : False := by
  classical
  choose priv pp using has
  let f := stitch core priv
  have pf : Function.Injective f := stitch_injective ic (fun j=>(pp j).1) (fun j=>(pp j).2)
  have hk : CoreKnown G m f := stitch_known_core_pairs m known (fun j=>(pp j).2)
  have site (j : Fin 7) : f (Fin.castLE (by decide) j)=core (sIndex j) := by
    have lt : (Fin.castLE (by decide : 7≤18) j).val<9 := lt_trans j.isLt (by decide)
    have j9 : j.val<9 := lt_trans j.isLt (by decide)
    simp [f,stitch,j9,sIndex]
    rfl
  have xf (a : Fin 18) : x≠f a := by
    by_cases ab : a.val<9
    · simpa [f,stitch,ab] using out ⟨a.val,ab⟩
    · dsimp only [f]
      rw [stitch,dif_neg ab]
      intro eq
      let k : Fin 9 := ⟨a.val-9,by have := a.isLt; omega⟩
      have p : PrivateFor G core k x := eq.symm ▸ pp k
      have lhs := (p.2 (sIndex i)).mp ((xa i).mpr (Or.inl rfl))
      have rhs := (p.2 (sIndex (i+1))).mp ((xa (i+1)).mpr (Or.inr rfl))
      have notEq : ∀ j : Fin 7,j≠j+1 := by decide
      exact notEq i (Fin.ext (congrArg (fun j : Fin 9=>j.val) (lhs.symm.trans rhs)))
  have zi : Function.Injective z := by
    intro d e eq
    apply sat_sites_inj i
    exact ((za e _).mp (eq ▸ (za d _).mpr rfl))
  have only (d : Fin 3) (a : Fin 18) (eq : z d=f a) : a.val=9+(satSite i d).val := by
    by_cases ab : a.val<9
    · have bad := zo d ⟨a.val,ab⟩
      exact (bad (by simpa [f,stitch,ab] using eq)).elim
    · dsimp only [f] at eq
      rw [stitch,dif_neg ab] at eq
      let k : Fin 9 := ⟨a.val-9,by have := a.isLt; omega⟩
      have p : PrivateFor G core k (z d) := eq.symm ▸ pp k
      have hx := congrArg Fin.val ((p.2 (sIndex (satSite i d))).mp ((za d _).mpr rfl))
      change a.val-9=(satSite i d).val at hx
      omega
  obtain ⟨mask,aliases⟩ := adjacent_sat_alias_exists i f z
  have fit : Fit G (satLabel f x z) (satSpec m i mask) :=
    adjacent_sat_fit m i mask f x z hk
      (by intro j; rw [site,G.adj_comm]; exact xa j)
      (by intro d j; rw [site,G.adj_comm]; exact za d j) xz (fun d=>(aliases d).mp)
  have inj := adjacent_sat_partial_inj i mask f x z pf zi xf (fun d=>(xz d).ne) only aliases
  obtain ⟨t,ct,atc⟩ := cert mask
  exact checked_active_sound h4 h9 (satActive mask) inj _ fit t [] (by intro q qm; cases qm) ct atc

#print axioms private_adjacent_multi_not_saturated
end Graffiti133NestedWeightedCore
