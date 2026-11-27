import NestedCorePrivateExpandedRealLift133

namespace Graffiti133ExpandedPrivate
open SimpleGraph Graffiti133 Graffiti133PrivateCross
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000
variable {V : Type*} {G : SimpleGraph V}

def oppIndex (c : Fin 2) : Fin 9 := ⟨8-c.val,by omega⟩

private theorem core_index_cases (a : Fin 9) : (∃ k : Fin 7,a=sIndex k) ∨ a=7 ∨ a=8 := by
  by_cases lo : a.val < 7
  · exact Or.inl ⟨⟨a.val,lo⟩,rfl⟩
  · have small := a.isLt
    have hi : a.val=7 ∨ a.val=8 := by omega
    exact Or.inr (hi.imp Fin.ext Fin.ext)

private theorem core_index_cases_owned (a : Fin 9) (c : Fin 2) :
    (∃ k : Fin 7,a=sIndex k) ∨ a=cIndex c ∨ a=oppIndex c := by
  have h := core_index_cases a
  fin_cases c
  · exact h
  · exact h.imp id Or.symm

private theorem core_private_of_single_site
    (core : Fin 9→V) {z : V} (i : Fin 7) (zo : ∀ a,z≠core a)
    (zs : ∀ k : Fin 7,G.Adj z (core (sIndex k))↔ k=i)
    (a0 : ¬G.Adj z (core 7)) (a1 : ¬G.Adj z (core 8)) :
    PrivateFor G core (sIndex i) z := by
  refine ⟨zo,?_⟩
  intro a
  rcases core_index_cases a with ⟨k,rfl⟩|rfl|rfl
  · rw [zs]
    exact ⟨fun e=>congrArg sIndex e.symm,fun e=>(Fin.ext (congrArg (fun a : Fin 9=>a.val) e) : i=k).symm⟩
  · have n : sIndex i≠(7:Fin 9) := by
      intro e
      have e' := congrArg Fin.val e
      have h := i.isLt
      change i.val=7 at e'
      omega
    simp [a0,n]
  · have n : sIndex i≠(8:Fin 9) := by
      intro e
      have e' := congrArg Fin.val e
      have h := i.isLt
      change i.val=8 at e'
      omega
    simp [a1,n]

theorem very_short_crossing_has_common_control
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (m : Bool) (core : Fin 9→V) (ci : Function.Injective core)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (has : ∀ i,∃ w,PrivateFor G core i w)
    (j : Fin 7) (wide : Bool) (r z : V)
    (ro : ∀ a,r≠core a) (zo : ∀ a,z≠core a)
    (rNo : ∀ k : Fin 7,¬G.Adj r (core (sIndex k)))
    (rHit : G.Adj r (core 7) ∨ G.Adj r (core 8))
    (zSite : ∀ k : Fin 7,G.Adj z (core (sIndex k))↔ k=j ∨ (wide=true ∧ k=j+1))
    (cross : G.Adj r z) :
    ∃ c : Fin 2,G.Adj r (core (cIndex c)) ∧ G.Adj z (core (cIndex c)) := by
  classical
  by_contra! no
  have single (c : Fin 2) (rOwn : G.Adj r (core (cIndex c))) (rOther : ¬G.Adj r (core (oppIndex c))) : False := by
    have ownNo := no c rOwn
    have rp : PrivateFor G core (cIndex c) r := by
      refine ⟨ro,?_⟩
      intro a
      rcases core_index_cases_owned a c with ⟨k,rfl⟩|rfl|rfl
      · have ne : cIndex c≠sIndex k := by
          intro e
          have q := congrArg Fin.val e
          have := k.isLt
          change c.val+7=k.val at q
          omega
        simp [rNo,ne]
      · simp [rOwn]
      · have ne : cIndex c≠oppIndex c := by fin_cases c <;> decide
        simp [rOther,ne]
    let opp := decide (G.Adj z (core (oppIndex c)))
    have crossKnown (a : Fin 9) : G.Adj z (core a)↔
        a.val=j.val ∨ (wide=true ∧ a.val=(j+1).val) ∨ (opp=true ∧ a.val=8-c.val) := by
      rcases core_index_cases_owned a c with ⟨k,rfl⟩|rfl|rfl
      · rw [zSite]
        have ne : k.val≠8-c.val := by have := c.isLt; have := k.isLt; omega
        simp [sIndex,ne,Fin.ext_iff]
      · have j7 := j.isLt
        have jp7 := (j+1).isLt
        have c2 := c.isLt
        have ne1 : c.val+7≠j.val := by omega
        have ne2 : c.val+7≠(j+1).val := by omega
        have ne3 : c.val+7≠8-c.val := by fin_cases c <;> decide
        simp only [cIndex,Fin.val_mk,ne1,ne2,ne3,and_false,or_false,iff_false]
        exact ownNo
      · have j7 := j.isLt
        have jp7 := (j+1).isLt
        have c2 := c.isLt
        have ne1 : 8-c.val≠j.val := by omega
        have ne2 : 8-c.val≠(j+1).val := by omega
        simp [oppIndex,ne1,ne2,opp]
    by_cases g : wide=true ∨ opp=true
    · exact nonprivate_near_crossing_forbidden_for_single_control h4 h9 m core ci fit has c j wide opp
        g r z rp zo crossKnown cross
    · have zs (k : Fin 7) : G.Adj z (core (sIndex k))↔k=j := by
        simp [zSite,show ¬wide=true from fun h=>g (Or.inl h)]
      have opposite : ¬G.Adj z (core (oppIndex c)) := by
        intro adj
        exact g (Or.inr (decide_eq_true adj))
      have ctr : ¬G.Adj z (core 7) ∧ ¬G.Adj z (core 8) := by
        fin_cases c
        · exact ⟨ownNo,opposite⟩
        · exact ⟨opposite,ownNo⟩
      have zp := core_private_of_single_site core j zo zs ctr.1 ctr.2
      let a := cIndex c
      let b := sIndex j
      have ab : a≠b := by
        intro e
        have q := congrArg Fin.val e
        have j7 := j.isLt
        change c.val+7=j.val at q
        omega
      obtain ⟨p,pp⟩ := choose_private_with_reserved core has a r rp
      let w (i : Fin 9) := if i=b then z else p i
      have wa : w a=r := by simp [w,ab,pp.2]
      have wb : w b=z := by simp [w]
      have wp (i : Fin 9) : PrivateFor G core i (w i) := by
        by_cases eq : i=b
        · subst i
          simpa only [wb] using zp
        · simpa only [w,if_neg eq] using pp.1 i
      have forbid := normalized_control_and_cycle_private_witnesses_nonadjacent h4 h9 m core w ci fit
        (fun i=>(wp i).1) (fun i=>(wp i).2) c j
      change ¬G.Adj (w b) (w a) at forbid
      rw [wb,wa] at forbid
      exact forbid cross.symm
  by_cases r7 : G.Adj r (core 7)
  · by_cases r8 : G.Adj r (core 8)
    · have no7 : ¬G.Adj z (core 7) := no 0 r7
      have no8 : ¬G.Adj z (core 8) := no 1 r8
      have rSite (a : Fin 9) : G.Adj r (core a)↔a.val=7 ∨ a.val=8 := by
        rcases core_index_cases a with ⟨k,rfl⟩|rfl|rfl
        · have k7 := k.isLt
          have n7 : k.val≠7 := by omega
          have n8 : k.val≠8 := by omega
          have bo : ¬((sIndex k).val=7 ∨ (sIndex k).val=8) := fun h=>h.elim n7 n8
          exact iff_of_false (rNo k) bo
        · exact iff_of_true r7 (Or.inl rfl)
        · exact iff_of_true r8 (Or.inr rfl)
      cases wide
      · have zs (k : Fin 7) : G.Adj z (core (sIndex k))↔k=j := by simp [zSite]
        exact single_site_crossing_forbidden_for_dual_control h4 h9 m core ci fit has j r z
          (core_private_of_single_site core j zo zs no7 no8) ro rSite cross
      · have zc (a : Fin 9) : G.Adj z (core a)↔a.val=j.val ∨ a.val=(j+1).val := by
          rcases core_index_cases a with ⟨k,rfl⟩|rfl|rfl
          · rw [zSite]
            simp [sIndex,Fin.ext_iff]
          · have h := j.isLt
            have j' := (j+1).isLt
            have n1 : 7≠j.val := by omega
            have n2 : 7≠(j+1).val := by omega
            exact iff_of_false no7 (fun h=>h.elim n1 n2)
          · have h := j.isLt
            have j' := (j+1).isLt
            have n1 : 8≠j.val := by omega
            have n2 : 8≠(j+1).val := by omega
            exact iff_of_false no8 (fun h=>h.elim n1 n2)
        exact adjacent_site_crossing_forbidden_for_dual_control h4 h9 m core ci fit has j r z ro zo rSite zc cross
    · exact single 0 r7 r8
  · exact single 1 (rHit.resolve_left r7) r7

#print axioms very_short_crossing_has_common_control
end Graffiti133ExpandedPrivate
