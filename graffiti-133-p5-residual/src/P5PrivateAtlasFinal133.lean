import P5PrivateAtlasGraph133
import P5CorePrivateLayers133

namespace Graffiti133P5PrivateAtlas
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133P5CoreShape
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem nested_spanning_C5_private_atlas
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
      (m.val=31 ∨ ∀ i j,¬G.Adj (q i) (q j)) := by
  classical
  let J := G.induce (D : Set V)
  let H : Hole J 5 := ⟨Subtype.val ∘ F.c,Subtype.val_injective.comp F.inj,F.adj⟩
  let B : Hole G 5 := ⟨Subtype.val ∘ H.c,Subtype.val_injective.comp H.inj,H.adj⟩
  have hc (i : Fin 5) : H.c i∈E := (F.c i).property
  have hs (x : (D : Set V)) (xe : x∈E) : ∃ i,H.c i=x := by
    obtain ⟨i,e⟩ := span ⟨x,xe⟩
    exact ⟨i,congrArg Subtype.val e⟩
  choose w q hw using C5_two_layers_private D dm H E em hc hs
  have wo (i : Fin 5) : Outside B.c (w i).val := by
    intro j e
    exact (hw i).1.1 ((Subtype.ext e).symm ▸ hc j)
  have wa (i j : Fin 5) : G.Adj (w i).val (B.c j)↔j=i := by
    constructor
    · intro ed
      apply Classical.byContradiction
      intro h
      exact (hw i).1.2.2 _ (hc j) (fun e=>h (H.inj e)) ed
    · intro eq
      subst j
      exact (hw i).1.2.1
  obtain ⟨m,mg,mb,force⟩ := private_layers_config B h4 h9 D (fun i=>(H.c i).property) h7
    (fun i=>(w i).val) q (fun i=>(w i).property) wo wa (fun i=>(hw i).2)
  exact ⟨w,q,m,hw,mg,mb,force⟩

#print axioms nested_spanning_C5_private_atlas
end Graffiti133P5PrivateAtlas
