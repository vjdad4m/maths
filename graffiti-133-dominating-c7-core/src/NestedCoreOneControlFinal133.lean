import NestedCoreOneControlCanonical133
import NestedCorePrivateWitnesses133
import NestedCorePrivateOrbit133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133NestedLongGates Graffiti133NestedWeightedCore Graffiti133MultiWeighted Graffiti133Camby
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem normalize_one_profile :
    ∀ p : Fin 14,
      (∃ t : Fin 7,∃ rev : Bool,∀ i : Fin 7,orbitSite t rev i∈profileContacts p↔i=0 ∨ i=3) ∨
      (profileContacts p).card=3 := by decide

private theorem two_steps_main (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have h : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at h
  exact h

theorem radius_four_minimum_one_control_core_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (hr : 4≤radius G)
    (D : Finset V) (dm : MinimalSize G D) (cy : ∀ i,H.c i∈D)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u : V) (ud : u∈D) (uo : Outside H.c u) (uh : (contactSet H u).Nonempty)
    (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  let J := G.induce (D : Set V)
  let B := restrictedHole H D cy
  let U : (D : Set V) := ⟨u,ud⟩
  have Uoff : Outside B.c U := fun i e=>uo i (congrArg Subtype.val e)
  have hit : ∃ i,J.Adj U (B.c i) := by
    obtain ⟨i,im⟩ := uh
    exact ⟨i,(mem_contactSet H u i).mp im⟩
  obtain ⟨p,pp⟩ := classify_profile B (restricted_c4 h4 D) d7 U Uoff hit
  have matchP : Matches H u p := pp
  have cEq : contactSet H u=profileContacts p := by
    ext i
    exact (mem_contactSet H u i).trans (matchP i)
  rcases normalize_one_profile p with ⟨t,rev,normal⟩|trip
  · let T := orientHole H t rev
    have up (i : Fin 7) : G.Adj u (T.c i)↔i=0 ∨ i=3 := (matchP _).trans (normal i)
    have off : Outside T.c u := (orient_hole_outside H t rev u).mpr uo
    have cy' (i : Fin 7) : T.c i∈D := cy _
    have sh' (w : V) (wm : w∈D) : (∃ i,T.c i=w) ∨ w=u := by
      rcases shape w wm with h|e
      · have wR : w∈Set.range H.c := h
        rw [←orient_hole_range H t rev] at wR
        exact Or.inl wR
      · exact Or.inr e
    have ins (a : Fin 8) : core T u a∈D := by fin_cases a <;> simp [core,cy',ud]
    have us : ∃ i j : Fin 7,i≠j ∧ G.Adj u (T.c i) ∧ G.Adj u (T.c j) :=
      ⟨0,3,by decide,(up 0).mpr (Or.inl rfl),(up 3).mpr (Or.inr rfl)⟩
    have hs (x : V) : (G.induce (D.erase x : Set V)).Connected :=
      Graffiti133PrivateCross.cycle_two_control_core_connected_after_delete T D cy' u u
        (fun y ym=>(sh' y ym).imp id Or.inl) us us x
    have cp := core_injective T u off
    have priv (a : Fin 8) : ∃ z,PrivateFor G (core T u) a z := by
      let x := core T u a
      have adj : ∃ y∈D,G.Adj x y := by
        rcases sh' x (ins a) with ⟨i,e⟩|e
        · have suc (i : Fin 7) : Cyclic i (i+1) := (by decide : ∀ i : Fin 7,Cyclic i (i+1)) i
          exact ⟨T.c (i+1),cy' _,e ▸ (T.adj _ _).mpr (suc i)⟩
        · exact ⟨T.c 0,cy' _,e.symm ▸ (up 0).mpr (Or.inl rfl)⟩
      obtain ⟨y,yd,xy⟩ := adj
      obtain ⟨z,zo,zx,n⟩ := private_of_noncut dm (ins a)
        (Finset.mem_erase.mpr ⟨xy.ne.symm,yd⟩) xy (hs x)
      refine ⟨z,fun b e=>zo (e.symm ▸ ins b),fun b=>?_⟩
      constructor
      · intro e
        apply Classical.byContradiction
        intro h
        exact n _ (ins b) (fun e=>h (cp e).symm) e
      · rintro rfl
        exact zx
    exact canonical_minimum_one_control_mean_four T hc h4 h9 hr D dm.1.2 u off sh' up priv
  · have cm : (contactSet H u).card=3 := by rwa [cEq]
    obtain ⟨i,im,far⟩ := geometry_triple_center _ (contacts_are_allowed H h4 u uo) cm
    have small := radius_three_from_core_cover hc D dm.1.2 (H.c i) (by
      intro w wm
      rcases shape w wm with ⟨j,rfl⟩|eqW
      · by_cases eq : i=j
        · rw [←eq,dist_self]
          decide
        by_cases near : Cyclic i j
        · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr near)]
          decide
        by_cases mid : ∃ k,Cyclic i k ∧ Cyclic j k
        · obtain ⟨k,ik,jk⟩ := mid
          exact two_steps_main hc ((H.adj i k).mpr ik) ((H.adj j k).mpr jk).symm
        · exact two_steps_main hc ((mem_contactSet H u i).mp im).symm
            ((mem_contactSet H u j).mp (far j ⟨eq,near,mid⟩))
      · subst w
        rw [dist_eq_one_iff_adj.mpr ((mem_contactSet H u i).mp im).symm]
        decide)
    omega

private theorem walk_first_ne {W : Type*} {J : SimpleGraph W} {a b : W}
    (p : J.Walk a b) (h : a≠b) : ∃ j,J.Adj a j := by
  cases p with
  | nil => exact (h rfl).elim
  | cons e _ => exact ⟨_,e⟩

theorem radius_four_minimum_one_control_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (hr : 4≤radius G)
    (D : Finset V) (dm : MinimalSize G D) (cy : ∀ i,H.c i∈D)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u : V) (ud : u∈D) (uo : Outside H.c u)
    (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  let U : (D : Set V) := ⟨u,ud⟩
  let C : (D : Set V) := ⟨H.c 0,cy 0⟩
  have dif : U≠C := fun e=>uo 0 (congrArg Subtype.val e)
  obtain ⟨walk⟩ := dm.1.1 U C
  obtain ⟨j,hit⟩ := walk_first_ne walk dif
  have uh : (contactSet H u).Nonempty := by
    rcases shape j.val j.property with ⟨i,e⟩|e
    · exact ⟨i,(mem_contactSet H u i).mpr (e.symm ▸ hit)⟩
    · exact (hit.ne (Subtype.ext e.symm)).elim
  exact radius_four_minimum_one_control_core_mean_four H hc h4 h9 hr D dm cy d7 u ud uo uh shape

#print axioms radius_four_minimum_one_control_mean_four

#print axioms radius_four_minimum_one_control_core_mean_four
end Graffiti133NestedOneControl
