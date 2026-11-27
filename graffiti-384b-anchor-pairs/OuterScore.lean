import CliquePool
namespace Graffiti384b.AnchorPairs
open Finset SimpleGraph
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every degree-two vertex on a triangle specifies that triangle uniquely.
Count the remaining triangles using only the permitted high neighbors. -/
theorem score_cap (v : V) (P edge : Finset V) (k : ℕ) (size : nbr G v P≤k)
    (shape : ∀ i j,G.Adj v i → G.Adj v j → G.Adj i j →
      i∈high G → j∈high G → i∈P ∨ ({i,j}:Finset V)=edge) :
    trianglesAt G v≤nbr G v (LowSample.twos G)+1+k.choose 2 := by
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
  have cover : Repair.linkEdges G v⊆((LowSample.twos G).filter (G.Adj v)).image code∪insert edge ((P.filter (G.Adj v)).powersetCard 2) := by
    intro p pm
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G pm
    obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
    have im : i∈({i,j}:Finset V) := mem_insert_self ..
    have jm : j∈({i,j}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have vi := (G.mem_neighborFinset ..).mp (sub im)
    have vj := (G.mem_neighborFinset ..).mp (sub jm)
    have edge_ := cl _ im _ jm ij
    by_cases ih : i∈high G
    · by_cases jh : j∈high G
      · apply mem_union_right; apply mem_insert.mpr
        rcases shape i j vi vj edge_ ih jh with pi|exception
        · rcases shape j i vj vi edge_.symm jh ih with pj|exception
          · exact Or.inr (mem_powersetCard.mpr ⟨insert_subset (mem_filter.mpr ⟨pi,vi⟩)
              (singleton_subset_iff.mpr (mem_filter.mpr ⟨pj,vj⟩)),sz⟩)
          · exact Or.inl ((pair_comm ..).trans exception)
        · exact Or.inl exception
      · obtain ⟨m,eq⟩ := low vj vi edge_.symm jh
        exact mem_union_left _ (mem_image.mpr ⟨j,mem_filter.mpr ⟨m,vj⟩,eq.trans (pair_comm ..)⟩)
    · obtain ⟨m,eq⟩ := low vi vj edge_ ih
      exact mem_union_left _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨m,vi⟩,eq⟩)
  have h := (card_le_card cover).trans (card_union_le ..)
  have cc := card_insert_le edge ((P.filter (G.Adj v)).powersetCard 2)
  rw [card_powersetCard] at cc
  have ac := card_image_le (s:=(LowSample.twos G).filter (G.Adj v)) (f:=code)
  have ck := Nat.choose_le_choose 2 size
  change _≤(nbr G v P).choose 2+1 at cc
  change _≤nbr G v (LowSample.twos G) at ac
  change trianglesAt G v≤_ at h
  omega

end Graffiti384b.AnchorPairs
#print axioms Graffiti384b.AnchorPairs.score_cap
