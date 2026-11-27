import NestedCoreRadiusFourArchetypes133
import NestedCorePrivateCrossLift133

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
set_option maxRecDepth 100000

private theorem orbit_geometry :
  (∀ (t : Fin 7) (rev : Bool) (i j : Fin 7),
    orbitSite t rev i=orbitSite t rev j → i=j) ∧
  (∀ (t : Fin 7) (rev : Bool) (i : Fin 7),∃ j : Fin 7,orbitSite t rev j=i) ∧
  (∀ (t : Fin 7) (rev : Bool) (i j : Fin 7),
    Cyclic (orbitSite t rev i) (orbitSite t rev j)↔Cyclic i j) := by decide

noncomputable def orbitEquiv (t : Fin 7) (rev : Bool) : Fin 7 ≃ Fin 7 :=
  Equiv.ofBijective (orbitSite t rev) (⟨fun _ _ h=>orbit_geometry.1 t rev _ _ h,orbit_geometry.2.1 t rev⟩)

variable {V : Type*} {G : SimpleGraph V}
def orientHole (H : Hole G 7) (t : Fin 7) (rev : Bool) : Hole G 7 :=
  ⟨H.c ∘ orbitSite t rev,H.inj.comp (orbitEquiv t rev).injective,
    fun i j=>(H.adj ..).trans (orbit_geometry.2.2 t rev i j)⟩

theorem orient_hole_outside (H : Hole G 7) (t : Fin 7) (rev : Bool) (x : V) :
    Outside (orientHole H t rev).c x↔Outside H.c x := by
  refine ⟨fun h i e=>?_,fun h i e=>h (orbitSite t rev i) e⟩
  obtain ⟨j,eq⟩ := orbit_geometry.2.1 t rev i
  exact h j (by change x=H.c (orbitSite t rev j); rw [eq]; exact e)

theorem orient_hole_range (H : Hole G 7) (t : Fin 7) (rev : Bool) :
    Set.range (orientHole H t rev).c=Set.range H.c := by
  ext x
  constructor
  · rintro ⟨i,e⟩
    exact ⟨orbitSite t rev i,e⟩
  · rintro ⟨i,e⟩
    obtain ⟨j,eq⟩ := orbit_geometry.2.1 t rev i
    exact ⟨j,by change H.c (orbitSite t rev j)=x; rw [eq]; exact e⟩

theorem orient_contact_card [Fintype V] (H : Hole G 7) (t : Fin 7) (rev : Bool) (x : V) :
    (contactSet (orientHole H t rev) x).card=(contactSet H x).card := by
  classical
  let e := orbitEquiv t rev
  have eq : (contactSet (orientHole H t rev) x).map e.toEmbedding=contactSet H x := by
    ext j
    constructor
    · intro m
      obtain ⟨i,im,eij⟩ := Finset.mem_map.mp m
      have ed : G.Adj x (H.c (e i)) := (mem_contactSet (orientHole H t rev) x i).mp im
      exact (mem_contactSet H x j).mpr (eij ▸ ed)
    · intro jm
      let i := e.symm j
      have ij : e i=j := e.apply_symm_apply j
      refine Finset.mem_map.mpr ⟨i,(mem_contactSet (orientHole H t rev) x i).mpr ?_,ij⟩
      change G.Adj x (H.c (e i))
      rw [ij]
      exact (mem_contactSet H x j).mp jm
  rw [←eq,Finset.card_map]

theorem orient_multi_vertices [Fintype V] (H : Hole G 7) (t : Fin 7) (rev : Bool) :
    multiVertices (orientHole H t rev)=multiVertices H := by
  ext x
  simp [multiVertices,orient_hole_outside,orient_contact_card]

private theorem oriented_far_control (H : Hole G 7) (p : Fin 14) (x : V)
    (m : Matches H x p) (t : Fin 7) (rev : Bool)
    (eq : profileContacts p={orbitSite t rev 0,orbitSite t rev 3}) :
    ∀ i : Fin 7,G.Adj x ((orientHole H t rev).c i)↔i=0 ∨ i=3 := by
  intro i
  change G.Adj x (H.c (orbitSite t rev i))↔_
  rw [m,eq,Finset.mem_insert,Finset.mem_singleton]
  exact ⟨fun h=>h.imp (fun e=>orbit_geometry.1 t rev _ _ e) (fun e=>orbit_geometry.1 t rev _ _ e),
    fun h=>h.imp (congrArg _) (congrArg _)⟩

private theorem oriented_second_far_control (H : Hole G 7) (p : Fin 14) (x : V)
    (m : Matches H x p) (t : Fin 7) (rev : Bool)
    (eq : profileContacts p={orbitSite t rev 1,orbitSite t rev 4}) :
    ∀ i : Fin 7,G.Adj x ((orientHole H t rev).c i)↔i=1 ∨ i=4 := by
  intro i
  change G.Adj x (H.c (orbitSite t rev i))↔_
  rw [m,eq,Finset.mem_insert,Finset.mem_singleton]
  exact ⟨fun h=>h.imp (fun e=>orbit_geometry.1 t rev _ _ e) (fun e=>orbit_geometry.1 t rev _ _ e),
    fun h=>h.imp (congrArg _) (congrArg _)⟩

private theorem oriented_second_triple_control (H : Hole G 7) (p : Fin 14) (x : V)
    (m : Matches H x p) (t : Fin 7) (rev : Bool)
    (eq : profileContacts p={orbitSite t rev 1,orbitSite t rev 2,orbitSite t rev 5}) :
    ∀ i : Fin 7,G.Adj x ((orientHole H t rev).c i)↔i=1 ∨ i=2 ∨ i=5 := by
  intro i
  change G.Adj x (H.c (orbitSite t rev i))↔_
  rw [m,eq,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (h|h|h)
    · exact Or.inl (orbit_geometry.1 t rev _ _ h)
    · exact Or.inr (Or.inl (orbit_geometry.1 t rev _ _ h))
    · exact Or.inr (Or.inr (orbit_geometry.1 t rev _ _ h))
  · rintro (rfl|rfl|rfl) <;> simp

theorem orient_to_canonical_archetype (H : Hole G 7) {u v : V}
    {p q : Fin 14} (up : Matches H u p) (vq : Matches H v q) (m : CoreArchetype p q) :
    ∃ (t : Fin 7) (rev swap triple : Bool),
      let H' := orientHole H t rev
      let u' := if swap then v else u
      let v' := if swap then u else v
      (∀ i : Fin 7,G.Adj u' (H'.c i)↔i=0 ∨ i=3) ∧
      (∀ i : Fin 7,G.Adj v' (H'.c i)↔(if triple then i=1 ∨ i=2 ∨ i=5 else i=1 ∨ i=4)) := by
  obtain ⟨t,rev,⟨a,b|c⟩|⟨a,b|c⟩⟩ := m
  · exact ⟨t,rev,false,false,oriented_far_control H p u up t rev a,
      oriented_second_far_control H q v vq t rev b⟩
  · exact ⟨t,rev,false,true,oriented_far_control H p u up t rev a,
      oriented_second_triple_control H q v vq t rev c⟩
  · exact ⟨t,rev,true,false,oriented_far_control H q v vq t rev a,
      oriented_second_far_control H p u up t rev b⟩
  · exact ⟨t,rev,true,true,oriented_far_control H q v vq t rev a,
      oriented_second_triple_control H p u up t rev c⟩

#print axioms orient_contact_card
#print axioms orient_to_canonical_archetype
end Graffiti133NestedLongGates
