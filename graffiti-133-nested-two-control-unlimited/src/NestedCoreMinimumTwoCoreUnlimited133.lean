import NestedCorePrivateUnlimitedCross133
import NestedCorePrivateWitnesses133
import NestedCorePrivateOrbit133

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedSingleGate Graffiti133PrivateCross Graffiti133Camby
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem radius_four_minimum_two_control_core_unlimited_crossings_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ f : Fin 9→V,InducedPath G f) (hr : 4≤radius G)
    (D K : Finset V) (dmin : MinimalSize G D) (cd : ∀ i,H.c i∈D) (ck : ∀ i,H.c i∈K)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u v : V) (uv : u≠v) (ud : u∈D) (vd : v∈D) (uk : u∈K) (vk : v∈K)
    (shape : ∀ w∈D,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (uoff : Outside H.c u) (voff : Outside H.c v)
    (uh : (contactSet H u).Nonempty) (vh : (contactSet H v).Nonempty)
    (kdom : ∀ y : (K : Set V),Outside (restrictedHole H K ck).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K ck).c i))
    (baseMultis : (multiVertices (restrictedHole H K ck)).card≤4)
    (remote : ∀ w∉K,Remote H w) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  have ddom := dmin.1.2
  let J := G.induce (D : Set V)
  let HJ := restrictedHole H D cd
  have dj (w : (D : Set V)) (wo : Outside HJ.c w) : ∃ i,J.Adj w (HJ.c i) := by
    rcases shape w.val w.property with ⟨i,e⟩|e|e
    · exact (wo i (Subtype.ext e.symm)).elim
    · obtain ⟨i,im⟩ := uh
      exact ⟨i,show G.Adj w.val (H.c i) from e.symm ▸ (mem_contactSet H u i).mp im⟩
    · obtain ⟨i,im⟩ := vh
      exact ⟨i,show G.Adj w.val (H.c i) from e.symm ▸ (mem_contactSet H v i).mp im⟩
  have noedge : ¬G.Adj u v :=
    (outside_independent_and_core_order HJ (restricted_c4 h4 D) d7 dj).1 ⟨u,ud⟩ ⟨v,vd⟩
      (fun i e=>uoff i (congrArg Subtype.val e))
      (fun i e=>voff i (congrArg Subtype.val e))
  obtain ⟨p,q,pu,qv,canon⟩ := radius_four_two_control_core_archetypes H hc h4 hr D cd ddom d7
    u v ud vd shape uoff voff uv uh vh
  obtain ⟨t,rev,swap,triple,up,vp⟩ := orient_to_canonical_archetype H pu qv canon
  let H' := orientHole H t rev
  let U := if swap then v else u
  let W := if swap then u else v
  have Uoff : Outside H'.c U := (orient_hole_outside H t rev U).mpr (by cases swap <;> simp [U,uoff,voff])
  have Woff : Outside H'.c W := (orient_hole_outside H t rev W).mpr (by cases swap <;> simp [W,uoff,voff])
  have UW : U≠W := by cases swap <;> simp [U,W,uv,uv.symm]
  have noUW : ¬G.Adj U W := by
    cases swap
    · exact noedge
    · exact fun e=>noedge e.symm
  have Ud : U∈D := by cases swap <;> simp [U,ud,vd]
  have Wd : W∈D := by cases swap <;> simp [W,ud,vd]
  have Uk : U∈K := by cases swap <;> simp [U,uk,vk]
  have Wk : W∈K := by cases swap <;> simp [W,uk,vk]
  have cd' (i : Fin 7) : H'.c i∈D := cd _
  have ck' (i : Fin 7) : H'.c i∈K := ck _
  have shape' (x : V) (xd : x∈D) : (∃ i,H'.c i=x) ∨ x=U ∨ x=W := by
    rcases shape x xd with hx|hu|hv
    · have w : x∈Set.range H.c := hx
      rw [←orient_hole_range H t rev] at w
      exact Or.inl w
    · cases swap
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr hu)
    · cases swap
      · exact Or.inr (Or.inr hv)
      · exact Or.inr (Or.inl hv)
  let HK := restrictedHole H K ck
  let HK' := restrictedHole H' K ck'
  have hHK : HK'=orientHole HK t rev := rfl
  have kdom' (w : (K : Set V)) (wo : Outside HK'.c w) :
      ∃ i,(G.induce (K : Set V)).Adj w (HK'.c i) := by
    rw [hHK] at wo
    obtain ⟨j,ed⟩ := kdom w ((orient_hole_outside HK t rev w).mp wo)
    obtain ⟨i,eq⟩ := (orbitEquiv t rev).surjective j
    exact ⟨i,by
      change G.Adj w.val (H.c (orbitSite t rev i))
      change orbitSite t rev i=j at eq
      rw [eq]
      exact ed⟩
  have base' : (multiVertices HK').card≤4 := by
    rw [hHK,orient_multi_vertices]
    exact baseMultis
  have remote' (w : V) (wo : w∉K) : Remote H' w :=
    ⟨(orient_hole_outside H t rev w).mpr (remote w wo).1,fun i=>(remote w wo).2 (orbitSite t rev i)⟩
  have us : ∃ i j : Fin 7,i≠j ∧ G.Adj U (H'.c i) ∧ G.Adj U (H'.c j) :=
    ⟨0,3,by decide,(up 0).mpr (Or.inl rfl),(up 3).mpr (Or.inr rfl)⟩
  have vs : ∃ i j : Fin 7,i≠j ∧ G.Adj W (H'.c i) ∧ G.Adj W (H'.c j) := by
    cases triple
    · exact ⟨1,4,by decide,(vp 1).mpr (Or.inl rfl),(vp 4).mpr (Or.inr rfl)⟩
    · exact ⟨1,2,by decide,(vp 1).mpr (Or.inl rfl),(vp 2).mpr (Or.inr (Or.inl rfl))⟩
  have privateAll := minimum_core_has_canonical_private_witnesses H' D dmin cd' U W Uoff Woff UW
    Ud Wd shape' us vs
  exact radius_four_canonical_private_core_unlimited_crossings_mean_four H' hc h4 h9 hr D K cd' ck'
    ddom d7 U W UW Ud Wd Uk Wk shape' Uoff Woff noUW triple up vp privateAll kdom' base' remote'

#print axioms radius_four_minimum_two_control_core_unlimited_crossings_mean_four
end Graffiti133NestedLongGates
