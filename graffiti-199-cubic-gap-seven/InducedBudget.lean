import CoreTransfer

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

/-- An induced graph has no larger induced tree than the original graph.
An induced tree on a finset of subtype vertices is carried across the
graph isomorphism on its image under the subtype embedding. -/
theorem treeNumber_induce_le (X : Set V) [Fintype X] :
    treeNumber (G.induce X) ≤ treeNumber G := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro T ht
  have ht := (Finset.mem_filter.mp ht).2
  change T.card ≤ treeNumber G
  let f : X ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let U := T.map f
  let emb : (↑T : Set X) → (↑U : Set V) := fun x => ⟨f x.val,Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩⟩
  have inj : Function.Injective emb := by
    intro a b h
    exact Subtype.ext (f.injective (congrArg (fun y : (↑U : Set V) => y.val) h))
  have surj : Function.Surjective emb := by
    intro a
    obtain ⟨b,hb,e⟩ := Finset.mem_map.mp a.property
    exact ⟨⟨b,hb⟩,Subtype.ext e⟩
  let equiv := Equiv.ofBijective emb ⟨inj,surj⟩
  let iso : (G.induce X).induce (↑T : Set X) ≃g G.induce (↑U : Set V) :=
    ⟨equiv,by intro a b; rfl⟩
  have tup := SimpleGraph.isTree_iff_connected_and_card.mp ht
  have hU : (G.induce (↑U : Set V)).IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨iso.connected_iff.mp tup.1,?_⟩
    rw [← Nat.card_congr iso.mapEdgeSet,← Nat.card_congr equiv]
    exact tup.2
  rw [← Finset.card_map f]
  exact card_le_treeNumber U hU

/-- Deleting a nonneighbor preserves the degree of the retained vertex. -/
theorem degree_delete_nonneighbor [DecidableEq V] [DecidableRel G.Adj] {x y : V}
    (off : x ≠ y) (no : ¬ G.Adj x y) :
    (G.induce {v | v ≠ y}).degree ⟨x,off⟩ = G.degree x := by
  classical
  let H := G.induce {v | v ≠ y}
  let a : {v : V // v ≠ y} := ⟨x,off⟩
  let e : H.neighborSet a ≃ G.neighborSet x := {
    toFun v := ⟨v.val.val,v.property⟩
    invFun v := ⟨⟨v.val,fun eq => no (eq ▸ v.property)⟩,v.property⟩
    left_inv v := rfl
    right_inv v := rfl }
  change H.degree a = G.degree x
  rw [← H.card_neighborSet_eq_degree a,← G.card_neighborSet_eq_degree x]
  exact Fintype.card_congr e

#print axioms treeNumber_induce_le

end Graffiti199Depleted.Catalogue
