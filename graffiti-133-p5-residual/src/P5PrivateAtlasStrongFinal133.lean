import P5PrivateAtlasFinal133
import P5PrivateAtlasMatching133

namespace Graffiti133P5PrivateAtlas
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133P5CoreShape
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem nested_spanning_C5_private_matching
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (dm : MinimalSize G D) (h7 : NoPath (G.induce (D : Set V)) 7)
    (E : Finset (D : Set V)) (em : MinimalSize (G.induce (D : Set V)) E)
    (F : Hole ((G.induce (D : Set V)).induce (E : Set (D : Set V))) 5)
    (span : Function.Surjective F.c) :
    ∃ (w : Fin 5→(D : Set V)) (q : Fin 5→V) (m : Fin 32),
      (∀ i, PrivateAt (G.induce (D : Set V)) E (F.c i).val (w i) ∧
        PrivateAt G D (w i).val (q i)) ∧
      m.val∈goodMasks ∧
      (∀ i : Fin 5,m.val.testBit i.val=decide (G.Adj (w i).val (w (i+2)).val)) ∧
      (∀ i j,G.Adj (q i) (q j) → m.val=31 ∧ Cyclic i j) ∧
      (∀ i j k,G.Adj (q i) (q j) → G.Adj (q i) (q k) → j=k) := by
  classical
  obtain ⟨w,q,m,hw,good,bits,force⟩ := nested_spanning_C5_private_atlas h4 h9 D dm h7 E em F span
  refine ⟨w,q,m,hw,good,bits,?_⟩
  rcases force with full|empty
  · let H : Hole G 5 := ⟨fun i=>(F.c i).val.val,
      Subtype.val_injective.comp (Subtype.val_injective.comp F.inj),F.adj⟩
    have wo (i : Fin 5) : Outside H.c (w i).val := by
      intro j e
      exact (hw i).1.1 ((Subtype.ext e).symm ▸ (F.c j).property)
    have wp (i j : Fin 5) : G.Adj (w i).val (H.c j)↔j=i := by
      constructor
      · intro ed
        apply Classical.byContradiction
        intro h
        exact (hw i).1.2.2 _ (F.c j).property (fun e=>h (F.inj (Subtype.ext e))) ed
      · intro h
        subst j
        exact (hw i).1.2.1
    have exactBits (i : Fin 5) :
        (31:Nat).testBit i.val=decide (G.Adj (w i).val (w (i+2)).val) := by rw [←full,bits]
    have h := petersen_outer_matching H h4 h9 D (fun i=>(F.c i).val.property)
      (fun i=>(w i).val) q (fun i=>(w i).property) wo wp (fun i=>(hw i).2) exactBits
    exact ⟨fun i j e=>⟨full,h.1 i j e⟩,h.2⟩
  · exact ⟨fun i j e=>(empty i j e).elim,fun i j _ e _=>(empty i j e).elim⟩

#print axioms nested_spanning_C5_private_matching
end Graffiti133P5PrivateAtlas
