import NestedCorePrivateExpandedFit133
import NestedCorePrivateCrossLift133

namespace Graffiti133ExpandedPrivate
open SimpleGraph Graffiti133 Graffiti133PrivateCross
open scoped Classical
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

def cIndex (c : Fin 2) : Fin 9 := ⟨c.val+7,by have := c.isLt; omega⟩
def sIndex (i : Fin 7) : Fin 9 := Fin.castLE (by decide) i

private theorem stitch_core (core priv : Fin 9→V) (a : Fin 9) :
    stitch core priv (Fin.castLE (by decide) a)=core a := by simp [stitch,a.isLt]

private theorem stitched_site (core priv : Fin 9→V) (i : Fin 7) :
    stitch core priv (forcedSite i)=priv (sIndex i) := by
  have hn : ¬(forcedSite i).val < 9 := by simp [forcedSite]
  rw [stitch,dif_neg hn]
  congr 1

private theorem stitched_control (core priv : Fin 9→V) (c : Fin 2) :
    stitch core priv (forcedControl c)=priv (cIndex c) := by
  have hn : ¬(forcedControl c).val < 9 := by simp [forcedControl]
  rw [stitch,dif_neg hn]
  congr 1

private theorem multi_contact_fresh (core priv : Fin 9→V) {z : V}
    (out : ∀ a,z≠core a) (p : ∀ a,PrivateFor G core a (priv a))
    {a b : Fin 9} (ab : a≠b) (za : G.Adj z (core a)) (zb : G.Adj z (core b)) :
    ∀ j,z≠stitch core priv j := by
  intro j h
  by_cases j9 : j.val<9
  · rw [stitch,dif_pos j9] at h
    exact out _ h
  · rw [stitch,dif_neg j9] at h
    let i : Fin 9 := ⟨j.val-9,by have := j.isLt; omega⟩
    have e : z=priv i := h
    exact ab ((((p i).2 a).mp (e ▸ za)).symm.trans (((p i).2 b).mp (e ▸ zb)))

theorem choose_private_with_reserved (core : Fin 9→V)
    (has : ∀ i,∃ z,PrivateFor G core i z) (i : Fin 9) (z : V) (zp : PrivateFor G core i z) :
    ∃ priv : Fin 9→V, (∀ a,PrivateFor G core a (priv a)) ∧ priv i=z := by
  classical
  choose p pp using has
  refine ⟨fun j=>if j=i then z else p j,?_,by simp⟩
  intro j
  by_cases e : j=i
  · subst j
    simpa using zp
  · simpa only [if_neg e] using pp j

private theorem successor_site_distinct : ∀ i : Fin 7, i≠i+1 := by decide

theorem nonprivate_near_crossing_forbidden_for_single_control
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (core : Fin 9→V) (ci : Function.Injective core)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ i,∃ w,PrivateFor G core i w)
    (c : Fin 2) (i : Fin 7) (wide opp : Bool) (nonprivate : wide=true ∨ opp=true)
    (r z : V) (rp : PrivateFor G core (cIndex c) r) (zo : ∀ a,z≠core a)
    (zSite : ∀ a : Fin 9,G.Adj z (core a)↔
      a.val=i.val ∨ (wide=true ∧ a.val=(i+1).val) ∨ (opp=true ∧ a.val=8-c.val)) :
    ¬G.Adj r z := by
  intro crossing
  obtain ⟨priv,p,pr⟩ := choose_private_with_reserved core has (cIndex c) r rp
  let f := stitch core priv
  have fi : Function.Injective f := stitch_injective ci (fun j=>(p j).1) (fun j=>(p j).2)
  have known : CoreKnown G m f := stitch_known_core_pairs m fit (fun j=>(p j).2)
  have first : G.Adj z (core (sIndex i)) := (zSite _).mpr (Or.inl rfl)
  have zf : ∀ a,z≠f a := by
    rcases nonprivate with w|o
    · have adj : G.Adj z (core (sIndex (i+1))) := (zSite _).mpr (Or.inr (Or.inl ⟨w,rfl⟩))
      have distinct : sIndex i≠sIndex (i+1) := by
        intro e
        exact successor_site_distinct i (Fin.ext (congrArg (fun k : Fin 9=>k.val) e))
      exact multi_contact_fresh core priv zo p distinct first adj
    · let j : Fin 9 := ⟨8-c.val,by omega⟩
      have adj : G.Adj z (core j) := (zSite _).mpr (Or.inr (Or.inr ⟨o,rfl⟩))
      have distinct : sIndex i≠j := by
        intro e
        have h := congrArg Fin.val e
        have a := c.isLt
        have b := i.isLt
        change i.val=8-c.val at h
        omega
      exact multi_contact_fresh core priv zo p distinct first adj
  have fs : ∀ a : Fin 9,G.Adj (f (Fin.castLE (by decide) a)) z↔
      a.val=i.val ∨ (wide=true ∧ a.val=(i+1).val) ∨ (opp=true ∧ a.val=8-c.val) := by
    intro a
    change G.Adj (stitch core priv (Fin.castLE (by decide) a)) z↔_
    rw [stitch_core,G.adj_comm]
    exact zSite a
  have fr : G.Adj (f (forcedControl c)) z := by
    change G.Adj (stitch core priv (forcedControl c)) z
    rw [stitched_control,pr]
    exact crossing
  exact no_single_case_model m c i wide opp nonprivate (push f z) (push_injective fi zf) h4 h9
    (singleCase_fits m c i wide opp f z known fs fr)

theorem single_site_crossing_forbidden_for_dual_control
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (core : Fin 9→V) (ci : Function.Injective core)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ i,∃ w,PrivateFor G core i w)
    (i : Fin 7) (r z : V) (zp : PrivateFor G core (sIndex i) z)
    (ro : ∀ a,r≠core a) (rSite : ∀ a : Fin 9,G.Adj r (core a)↔a.val=7 ∨ a.val=8) :
    ¬G.Adj r z := by
  intro crossing
  obtain ⟨priv,p,pz⟩ := choose_private_with_reserved core has (sIndex i) z zp
  let f := stitch core priv
  have fi : Function.Injective f := stitch_injective ci (fun j=>(p j).1) (fun j=>(p j).2)
  have known : CoreKnown G m f := stitch_known_core_pairs m fit (fun j=>(p j).2)
  have rf : ∀ a,r≠f a := multi_contact_fresh core priv ro p (by decide : (7:Fin 9)≠8)
    ((rSite 7).mpr (Or.inl rfl)) ((rSite 8).mpr (Or.inr rfl))
  have fs (a : Fin 9) : G.Adj (f (Fin.castLE (by decide) a)) r↔a.val=7∨a.val=8 := by
    change G.Adj (stitch core priv (Fin.castLE (by decide) a)) r↔_
    rw [stitch_core,G.adj_comm]
    exact rSite a
  have fr : G.Adj (f (forcedSite i)) r := by
    change G.Adj (stitch core priv (forcedSite i)) r
    rw [stitched_site,pz]
    exact crossing.symm
  exact no_dual_single_case_model m i (push f r) (push_injective fi rf) h4 h9
    (dualSingleCase_fits m i f r known fs fr)

theorem adjacent_site_crossing_forbidden_for_dual_control
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (core : Fin 9→V) (ci : Function.Injective core)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ i,∃ w,PrivateFor G core i w)
    (i : Fin 7) (r z : V) (ro : ∀ a,r≠core a) (zo : ∀ a,z≠core a)
    (rSite : ∀ a : Fin 9,G.Adj r (core a)↔a.val=7 ∨ a.val=8)
    (zSite : ∀ a : Fin 9,G.Adj z (core a)↔a.val=i.val ∨ a.val=(i+1).val) :
    ¬G.Adj r z := by
  intro crossing
  classical
  choose priv p using has
  let f := stitch core priv
  have fi : Function.Injective f := stitch_injective ci (fun j=>(p j).1) (fun j=>(p j).2)
  have known : CoreKnown G m f := stitch_known_core_pairs m fit (fun j=>(p j).2)
  have rf : ∀ a,r≠f a := multi_contact_fresh core priv ro p (by decide : (7:Fin 9)≠8)
    ((rSite 7).mpr (Or.inl rfl)) ((rSite 8).mpr (Or.inr rfl))
  have distinct : sIndex i≠sIndex (i+1) := by
    intro e
    exact successor_site_distinct i (Fin.ext (congrArg (fun k : Fin 9=>k.val) e))
  have zf : ∀ a,z≠f a := multi_contact_fresh core priv zo p distinct
    ((zSite (sIndex i)).mpr (Or.inl rfl)) ((zSite (sIndex (i+1))).mpr (Or.inr rfl))
  have zpush : ∀ a,z≠push f r a := by
    intro a e
    by_cases a18 : (a.val < 18)
    · rw [push,dif_pos a18] at e
      exact zf _ e
    · rw [push,dif_neg a18] at e
      exact crossing.ne e.symm
  have rs (a : Fin 9) : G.Adj (f (Fin.castLE (by decide) a)) r↔a.val=7∨a.val=8 := by
    change G.Adj (stitch core priv (Fin.castLE (by decide) a)) r↔_
    rw [stitch_core,G.adj_comm]
    exact rSite a
  have zs (a : Fin 9) : G.Adj (f (Fin.castLE (by decide) a)) z↔a.val=i.val∨a.val=(i+1).val := by
    change G.Adj (stitch core priv (Fin.castLE (by decide) a)) z↔_
    rw [stitch_core,G.adj_comm]
    exact zSite a
  exact no_dual_adjacent_case_model m i (push (push f r) z)
    (push_injective (push_injective fi rf) zpush) h4 h9 (dualAdjacentCase_fits m i f r z known rs zs crossing)

#print axioms nonprivate_near_crossing_forbidden_for_single_control
#print axioms single_site_crossing_forbidden_for_dual_control
#print axioms adjacent_site_crossing_forbidden_for_dual_control
end Graffiti133ExpandedPrivate
