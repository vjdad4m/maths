import NestedCorePrivateWeightedFitHelpers133
import NestedCorePrivateExpandedRealLift133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133PrivateCross Graffiti133ExpandedPrivate
open scoped Classical
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

def farNeighborSite (c : Fin 2) : Fin 7 := if c=0 then 5 else 6

def farSpec (m : Bool) (c : Fin 2) (a b : Fin 19) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if hy : y < 18 then baseFragment m x y hy (min_le_max ..)
  else if x < 7 then some (decide (x=(farNeighborSite c).val))
  else if x=c.val+7 then some true else none

private def farTree00 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 8 18 (.split 13 14 (.split 13 18 (.split 13 17 (.split 14 15 (.split 15 18 (.split 17 18 (.path ![6,5,18,7,3,2,1,8,17]) (.split 14 17 (.split 16 17 (.split 15 17 (.path ![3,2,1,8,17,18,5,6,15]) (.path ![0,1,2,3,4,5,18,17,15])) (.four 7 17 16 18)) (.four 5 17 14 18))) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 4 18 5 8)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
private theorem farTree00_ok : checked (farSpec false 0) [] farTree00=true := by decide

private def farTree01 : Tree 19 := (.split 9 10 (.split 7 18 (.split 9 15 (.split 9 18 (.split 9 16 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 14 18 (.split 16 18 (.path ![5,6,18,8,1,2,3,7,16]) (.split 15 16 (.split 16 17 (.split 14 16 (.path ![1,2,3,7,16,18,6,5,14]) (.path ![0,1,2,3,4,5,14,16,18])) (.four 8 16 17 18)) (.four 6 16 15 18))) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 18 6 7)) (.four 0 10 1 9))
private theorem farTree01_ok : checked (farSpec false 1) [] farTree01=true := by decide

private def farTree10 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 18 (.split 14 15 (.split 15 18 (.split 14 17 (.split 17 18 (.split 8 18 (.split 10 18 (.split 10 15 (.path ![10,1,2,3,7,18,5,6,15]) (.split 11 18 (.split 14 16 (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.split 10 16 (.split 15 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 12 15 (.split 15 17 (.split 12 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 11 15 (.path ![0,6,15,10,12,17,8,2,11]) (.split 16 17 (.path ![0,7,16,15,10,12,17,8,2]) (.path ![0,6,15,16,17,8,2,3,4])))) (.split 12 17 (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 16 17 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.path ![0,1,10,12,3,4,13,17,16])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15))) (.four 10 17 12 15))) (.path ![0,1,8,5,4,3,12,15,16]))) (.path ![0,6,5,8,2,3,12,10,16]))) (.split 16 18 (.split 14 18 (.split 15 16 (.split 10 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.path ![0,6,5,8,2,3,12,10,16]))) (.split 10 14 (.split 12 15 (.split 10 12 (.path ![1,10,15,6,5,18,7,3,12]) (.split 10 16 (.split 15 17 (.split 12 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 11 15 (.path ![0,6,15,10,12,17,8,2,11]) (.split 11 14 (.split 16 17 (.path ![0,7,16,15,10,12,17,8,2]) (.path ![0,6,15,16,17,8,2,3,4])) (.four 11 16 14 15)))) (.split 12 17 (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 16 17 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.path ![0,1,10,12,3,4,13,17,16])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15))) (.four 10 17 12 15))) (.path ![0,6,5,8,2,3,12,10,16]))) (.path ![0,1,8,5,4,3,12,15,16])) (.four 10 16 14 15))) (.four 7 14 16 18)) (.four 5 16 14 18))) (.split 11 14 (.split 11 16 (.split 9 11 (.split 9 12 (.split 14 16 (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.split 10 16 (.split 15 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 12 15 (.split 15 17 (.split 12 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 11 15 (.path ![0,6,15,10,12,17,8,2,11]) (.split 16 18 (.split 16 17 (.path ![0,7,16,15,10,12,17,8,2]) (.path ![0,6,15,16,17,8,2,3,4])) (.four 11 16 15 18)))) (.split 12 17 (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 16 17 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.path ![0,1,10,12,3,4,13,17,16])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15))) (.four 10 17 12 15))) (.path ![0,1,8,5,4,3,12,15,16]))) (.path ![0,6,5,8,2,3,12,10,16]))) (.split 16 18 (.split 14 18 (.split 15 16 (.split 10 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.path ![0,6,5,8,2,3,12,10,16]))) (.split 10 14 (.split 12 15 (.split 10 12 (.path ![1,10,15,6,5,18,7,3,12]) (.split 10 16 (.split 15 17 (.split 12 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 11 15 (.path ![0,6,15,10,12,17,8,2,11]) (.split 16 17 (.path ![0,7,16,15,10,12,17,8,2]) (.path ![0,6,15,16,17,8,2,3,4])))) (.split 12 17 (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 16 17 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.path ![0,1,10,12,3,4,13,17,16])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15))) (.four 10 17 12 15))) (.path ![0,6,5,8,2,3,12,10,16]))) (.path ![0,1,8,5,4,3,12,15,16])) (.four 10 16 14 15))) (.four 7 14 16 18)) (.four 5 16 14 18))) (.path ![1,0,9,12,3,4,5,18,11])) (.path ![4,5,8,2,11,9,0,7,16])) (.four 7 11 16 18)) (.four 5 11 14 18)))) (.split 10 14 (.split 10 16 (.split 11 18 (.split 10 12 (.split 9 12 (.path ![9,0,1,10,18,5,4,3,12]) (.path ![0,9,12,3,2,8,5,18,10])) (.path ![0,6,5,18,10,12,3,2,11])) (.split 11 14 (.split 11 16 (.split 9 11 (.split 9 12 (.split 10 12 (.path ![9,0,1,10,18,5,4,3,12]) (.path ![2,3,12,10,18,5,6,0,9])) (.path ![1,0,9,12,3,4,5,18,11])) (.path ![4,5,8,2,11,9,0,7,16])) (.four 7 11 16 18)) (.four 5 11 14 18))) (.four 7 10 16 18)) (.four 5 10 14 18))) (.split 10 18 (.split 11 18 (.split 14 18 (.split 10 15 (.path ![10,1,2,3,7,18,5,6,15]) (.split 16 18 (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.split 10 16 (.split 15 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 12 15 (.split 15 17 (.split 12 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 11 15 (.path ![0,6,15,10,12,17,8,2,11]) (.split 16 17 (.path ![0,7,16,15,10,12,17,8,2]) (.path ![0,6,15,16,17,8,2,3,4])))) (.split 12 17 (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 16 17 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.path ![0,1,10,12,3,4,13,17,16])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15))) (.four 10 17 12 15))) (.path ![0,1,8,5,4,3,12,15,16]))) (.path ![0,6,5,8,2,3,12,10,16]))) (.split 14 16 (.split 16 17 (.split 10 12 (.split 12 15 (.path ![1,10,15,6,5,18,7,3,12]) (.path ![0,1,10,15,12,3,4,5,18])) (.split 10 16 (.split 15 16 (.path ![1,10,15,6,5,4,3,7,16]) (.split 12 15 (.split 12 17 (.split 15 17 (.path ![0,6,15,10,12,3,2,8,17]) (.split 10 13 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.split 13 16 (.split 13 15 (.path ![0,1,2,3,4,13,17,15,16]) (.path ![0,7,16,15,13,4,5,8,2])) (.four 13 15 16 17))) (.split 13 16 (.split 13 17 (.split 13 15 (.path ![0,6,15,17,8,2,3,4,13]) (.path ![0,1,8,17,15,13,4,3,12])) (.four 10 17 13 15)) (.four 10 16 13 15)))) (.split 15 17 (.path ![0,7,16,15,10,12,17,8,2]) (.four 10 17 12 15))) (.path ![0,1,8,5,4,3,12,15,16]))) (.path ![0,6,5,8,2,3,12,10,16]))) (.four 8 16 17 18)) (.four 5 16 14 18)))) (.four 5 18 8 14)) (.four 2 18 8 11)) (.four 1 18 8 10))) (.four 5 17 8 18)) (.four 5 17 8 14)) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
private theorem farTree10_ok : checked (farSpec true 0) [] farTree10=true := by decide

variable {V : Type*} {G : SimpleGraph V}

theorem far_spec_fits (m : Bool) (c : Fin 2) (f : Fin 18→V) (z : V)
    (core : CoreKnown G m f)
    (s : ∀ a : Fin 7,G.Adj (f (Fin.castLE (by decide) a)) z↔ a=farNeighborSite c)
    (forced : G.Adj (f (⟨c.val+7,by have := c.isLt; omega⟩ : Fin 18)) z) :
    Fit G (push f z) (farSpec m c) := by
  apply nested_fit_sorted
  · intro a b
    simp [farSpec,min_comm,max_comm]
  intro a b t ab h
  simp only [farSpec,Nat.min_eq_left ab,Nat.max_eq_right ab] at h
  by_cases lo : b.val<18
  · rw [dif_pos lo] at h
    rw [push,dif_pos (lt_of_le_of_lt ab lo),push,dif_pos lo]
    exact nested_base_fragment_sound core h
  · rw [dif_neg lo] at h
    by_cases close : a.val<7
    · rw [if_pos close,Option.some.injEq] at h
      rw [←h,push,dif_pos (by omega : a.val<18),push,dif_neg lo]
      exact (s ⟨a.val,close⟩).trans ⟨fun e=>decide_eq_true (congrArg Fin.val e),
        fun e=>Fin.ext (of_decide_eq_true e)⟩
    · rw [if_neg close] at h
      by_cases eq : a.val=c.val+7
      · rw [if_pos eq,Option.some.injEq] at h
        subst t
        rw [push,dif_pos (by have := c.isLt; omega : a.val<18),push,dif_neg lo]
        have e : (⟨a.val,by have := c.isLt; omega⟩ : Fin 18)=⟨c.val+7,by have := c.isLt; omega⟩ :=
          Fin.ext eq
        rw [e]
        exact iff_of_true forced rfl
      · rw [if_neg eq] at h
        contradiction

theorem private_far_control_no_clean_singleton
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (c : Fin 2) (caseOK : m=false ∨ c=0)
    (core : Fin 9→V) (ic : Function.Injective core) (known : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ a : Fin 9,∃ z,PrivateFor G core a z)
    (z : V) (out : ∀ a,z≠core a)
    (s : ∀ i : Fin 7,G.Adj z (core (sIndex i))↔i=farNeighborSite c)
    (adj : G.Adj z (core (cIndex c))) : False := by
  classical
  choose priv p using has
  let f := stitch core priv
  have fresh (i : Fin 18) : z≠f i := by
    by_cases e : i.val<9
    · simpa [f,stitch,e] using out ⟨i.val,e⟩
    · dsimp only [f]
      rw [stitch,dif_neg e]
      intro ze
      let a : Fin 9 := ⟨i.val-9,by have := i.isLt; omega⟩
      have pz : PrivateFor G core a z := ze.symm ▸ p a
      have c1 := (pz.2 (cIndex c)).mp adj
      have c2 := (pz.2 (sIndex (farNeighborSite c))).mp ((s _).mpr rfl)
      have eq := congrArg Fin.val (c1.symm.trans c2)
      have lt := (farNeighborSite c).isLt
      change c.val+7=(farNeighborSite c).val at eq
      omega
  have fit : Fit G (push f z) (farSpec m c) := by
    apply far_spec_fits m c f z (stitch_known_core_pairs m known (fun j=>(p j).2))
    · intro a
      have ha : (Fin.castLE (by decide : 7≤18) a).val<9 := by exact lt_trans a.isLt (by decide)
      dsimp only [f]
      rw [stitch,dif_pos ha,G.adj_comm]
      exact s a
    · have h : c.val+7<9 := by have := c.isLt; omega
      simpa [f,stitch,h,cIndex] using adj.symm
  have inj := push_injective (stitch_injective ic (fun j=>(p j).1) (fun j=>(p j).2)) fresh
  have nil : Graffiti133PrivateGeneric.BitsOK G (push f z) [] := by intro q qm; cases qm
  cases m
  · fin_cases c
    · exact checked_sound h4 h9 inj _ fit farTree00 [] nil farTree00_ok
    · exact checked_sound h4 h9 inj _ fit farTree01 [] nil farTree01_ok
  · have eq : c=0 := caseOK.resolve_left (by decide)
    subst c
    exact checked_sound h4 h9 inj _ fit farTree10 [] nil farTree10_ok

#print axioms private_far_control_no_clean_singleton
end Graffiti133NestedWeightedCore
