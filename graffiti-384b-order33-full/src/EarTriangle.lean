import CliquePool
namespace Graffiti384b.Shared
open Finset SimpleGraph
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every degree-two vertex on a triangle specifies that triangle uniquely.
Count the remaining triangles using only the permitted high neighbors. -/
theorem score_cap (v : V) (P : Finset V) (k : ℕ) (size : nbr G v P≤k)
    (shape : ∀ i j,G.Adj v i → G.Adj v j → G.Adj i j →
      i∈high G → j∈high G → i∈P) :
    trianglesAt G v≤(LowSample.twos G).card+k.choose 2 := by
  classical
  let code (w : V) := insert w ((G.neighborFinset w).erase v)
  have low {i j : V} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) (ih : i∉high G) :
      i∈LowSample.twos G ∧ code i={i,j} := by
    have sub : {v,j}⊆G.neighborFinset i := insert_subset ((G.mem_neighborFinset ..).mpr vi.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ij))
    have lower := card_le_card sub
    rw [card_pair vj.ne,card_neighborFinset_eq_degree] at lower
    have upper : G.degree i≤2 := Nat.le_of_not_gt (fun h => ih (mem_filter.mpr ⟨mem_univ _,h⟩))
    have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,card_pair vj.ne]; exact upper)
    exact ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,lower⟩,ih⟩,by simp [code,←eq,vj.ne,vj.ne.symm]⟩
  have cover : Repair.linkEdges G v⊆(LowSample.twos G).image code∪(P.filter (G.Adj v)).powersetCard 2 := by
    intro p pm
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G pm
    obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
    have im : i∈({i,j}:Finset V) := mem_insert_self ..
    have jm : j∈({i,j}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have vi := (G.mem_neighborFinset ..).mp (sub im)
    have vj := (G.mem_neighborFinset ..).mp (sub jm)
    have edge := cl _ im _ jm ij
    by_cases ih : i∈high G
    · by_cases jh : j∈high G
      · exact mem_union_right _ (mem_powersetCard.mpr ⟨insert_subset
          (mem_filter.mpr ⟨shape i j vi vj edge ih jh,vi⟩)
          (singleton_subset_iff.mpr (mem_filter.mpr ⟨shape j i vj vi edge.symm jh ih,vj⟩)),sz⟩)
      · obtain ⟨m,eq⟩ := low vj vi edge.symm jh
        exact mem_union_left _ (mem_image.mpr ⟨j,m,eq.trans (pair_comm ..)⟩)
    · obtain ⟨m,eq⟩ := low vi vj edge ih
      exact mem_union_left _ (mem_image.mpr ⟨i,m,eq⟩)
  have h := (card_le_card cover).trans (card_union_le ..)
  rw [card_powersetCard] at h
  exact h.trans (Nat.add_le_add card_image_le (Nat.choose_le_choose 2 size))

end Graffiti384b.Shared
#print axioms Graffiti384b.Shared.score_cap
