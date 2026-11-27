import C7MultiScoreHelpers133
import NestedCorePrivateWeightedGeometry133
import C7MultiWeightedLocal133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133PrivateCross Graffiti133ExpandedPrivate
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem canonical_priority_far_clean_zero
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (K : Finset V) (cy : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i))
    (m : Bool) (u v : V) (un : Outside H.c u) (vn : Outside H.c v) (uv : u≠v)
    (ue : ∀ j : Fin 7,G.Adj u (H.c j)↔j=0 ∨ j=3)
    (ve : ∀ j : Fin 7,G.Adj v (H.c j)↔(if m then (j=1 ∨ j=2 ∨ j=5) else (j=1 ∨ j=4)))
    (noedge : ¬G.Adj u v)
    (has : ∀ a : Fin 9,∃ z,PrivateFor G (canonCore H u v) a z)
    (x : (K : Set V)) (prio : x.val=u ∨ x.val=v)
    (two : (contactSet (restrictedHole H K cy) x).card=2) :
    ((exteriorNeighbors (restrictedHole H K cy) x) \ markedNeighbors (restrictedHole H K cy) x).card=0 := by
  classical
  let B := restrictedHole H K cy
  have eq0 : contactSet H u=({0,3} : Finset (Fin 7)) := by
    ext j
    exact (mem_contactSet H u j).trans ((ue j).trans (by simp))
  have eq1 : contactSet H v=(if m then ({1,2,5} : Finset (Fin 7)) else {1,4}) := by
    ext j
    cases m <;> exact (mem_contactSet H v j).trans ((ve j).trans (by simp))
  have cx : contactSet B x=contactSet H x.val := restricted_contacts H K cy x
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z zm
  obtain ⟨zExterior,zClean⟩ := Finset.mem_sdiff.mp zm
  obtain ⟨_,zoff,xz⟩ := Finset.mem_filter.mp zExterior
  have za (j : Fin 7) (zj : G.Adj z.val (H.c j)) : j∉contactSet B x := by
    intro jm
    apply zClean
    exact Finset.mem_filter.mpr ⟨zExterior,j,jm,zj⟩
  have xoff : Outside B.c x := by
    intro i eq
    exact prio.elim (fun xu=>un i (xu.symm.trans (congrArg Subtype.val eq)))
      (fun xv=>vn i (xv.symm.trans (congrArg Subtype.val eq)))
  have caseC : ∃ c : Fin 2,(m=false ∨ c=0) ∧ x.val=canonCore H u v (cIndex c) ∧
      contactSet B x=(if c=0 then ({0,3} : Finset (Fin 7)) else {1,4}) := by
    rcases prio with eu|ev
    · exact ⟨0,Or.inr rfl,eu,by rw [cx,eu,eq0]; rfl⟩
    · have em : m=false := by
        cases em : m
        · rfl
        · rw [cx,ev,eq1,em] at two
          change (3:Nat)=2 at two
          contradiction
      exact ⟨1,Or.inl em,ev,by rw [cx,ev,eq1,em]; rfl⟩
  obtain ⟨c,caseOK,xc,xcSites⟩ := caseC
  have only (j : Fin 7) (ed : G.Adj z.val (H.c j)) : j=farNeighborSite c := by
    have s : j∈cleanSites (contactSet B x) := neighbor_sites_clean B (restricted_c4 h4 K) xoff zoff xz j ed
    exact far_control_complementary c j (by rwa [←xcSites]) (by rw [←xcSites]; exact za j ed)
  obtain ⟨j,zj⟩ := dom z zoff
  have exactSite (j : Fin 7) : G.Adj z.val (H.c j)↔j=farNeighborSite c :=
    ⟨only j,fun e=>(e.trans (only _ zj).symm) ▸ zj⟩
  have cv (j : Fin 7) : canonCore H u v (sIndex j)=H.c j := by fin_cases j <;> rfl
  have zU : z.val≠u := by
    intro e
    have h0 := only 0 (e.symm ▸ (ue 0).mpr (Or.inl rfl))
    have h3 := only 3 (e.symm ▸ (ue 3).mpr (Or.inr rfl))
    exact (by decide : (0:Fin 7)≠3) (h0.trans h3.symm)
  have zV : z.val≠v := by
    intro e
    have ed1 : G.Adj v (H.c 1) := (ve 1).mpr (by cases m <;> simp)
    have ed2 : G.Adj v (H.c (if m then 2 else 4)) := (ve _).mpr (by cases m <;> simp)
    have h1 := only 1 (e.symm ▸ ed1)
    have h2 := only _ (e.symm ▸ ed2)
    have different : (1:Fin 7)≠(if m then 2 else 4) := by cases m <;> decide
    exact different (h1.trans h2.symm)
  have zout : ∀ a : Fin 9,z.val≠canonCore H u v a := by
    intro a
    fin_cases a <;> simp [canonCore] <;> first | exact zU | exact zV |
      exact fun e=>zoff _ (Subtype.ext e)
  exact private_far_control_no_clean_singleton h4 h9 m c caseOK _ (canonCore_injective H u v un vn uv)
    (canonCore_fits H u v m noedge ue ve) has z.val zout (fun j=>by rw [cv]; exact exactSite j)
    (show G.Adj z.val (canonCore H u v (cIndex c)) by rw [←xc]; exact xz.symm)

#print axioms canonical_priority_far_clean_zero
end Graffiti133NestedWeightedCore
