import PageBlocks

namespace TwinForcing
open SimpleGraph Finset

variable {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj]
local notation "G" => (@pageGraph n m H)

theorem page_neighbors (i : Fin n) (j : Fin m) :
    (G).neighborFinset (Sum.inr (i,j)) = {Sum.inl (i,false),Sum.inl (i,true)} := by
  ext x
  rcases x with ⟨k,b⟩ | ⟨k,p⟩
  · cases b <;> simp [pageGraph,pageAdj]
  · simp [pageGraph,pageAdj]

theorem page_degree (i : Fin n) (j : Fin m) :
    (G).degree (Sum.inr (i,j)) = 2 := by
  change ((G).neighborFinset (Sum.inr (i,j))).card = 2
  rw [page_neighbors,Finset.card_pair]
  simp

theorem hub_neighbors (i : Fin n) (b : Bool) :
    (G).neighborFinset (Sum.inl (i,b)) =
      (H.neighborFinset (i,b)).image Sum.inl ∪ pages m i := by
  ext x
  rcases x with ⟨k,c⟩|⟨k,p⟩
  · simp [pageGraph,pageAdj,pages]
  · simp [pageGraph,pageAdj,pages,eq_comm,Prod.mk.injEq]

theorem hub_degree (i : Fin n) (b : Bool) :
    (G).degree (Sum.inl (i,b)) = H.degree (i,b) + m := by
  change ((G).neighborFinset (Sum.inl (i,b))).card = _
  rw [hub_neighbors]
  have dis : Disjoint ((H.neighborFinset (i,b)).image Sum.inl) (pages m i) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp hy
    cases e
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ Sum.inl_injective,
    pages_card,card_neighborFinset_eq_degree]

#print axioms page_degree
#print axioms hub_degree
end TwinForcing
