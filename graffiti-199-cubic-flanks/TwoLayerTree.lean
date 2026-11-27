import TreeBudget

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An independent first layer joined to a root, and independent
leaves with one attachment each, form an induced tree. -/
theorem two_layer_tree_bound (z : V) (A B : Finset V)
    (rootOff : z ∉ B)
    (first : ∀ x ∈ A, G.Adj z x) (second : ∀ x ∈ B, ¬ G.Adj z x)
    (indA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (indB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (attach : ∀ x ∈ B, ∃! y, y ∈ A ∧ G.Adj x y) :
    A.card + B.card + 1 ≤ treeNumber G := by
  classical
  let S := insert z (A ∪ B)
  let H := G.induce (↑S : Set V)
  let root : (↑S : Set V) := ⟨z,Finset.mem_insert_self _ _⟩
  have offA : z ∉ A := fun h => G.loopless z (first z h)
  have dis : Disjoint A B := Finset.disjoint_left.mpr fun x ha hb => second x hb (first x ha)
  have size : S.card = A.card + B.card + 1 := by
    have off : z ∉ A ∪ B := fun h => (Finset.mem_union.mp h).elim offA rootOff
    change (insert z (A ∪ B)).card = _
    rw [Finset.card_insert_of_not_mem off,Finset.card_union_of_disjoint dis]
  have whereIn (x : (↑S : Set V)) : x = root ∨ x.val ∈ A ∨ x.val ∈ B := by
    have hx := Finset.mem_insert.mp x.property
    exact hx.imp Subtype.ext Finset.mem_union.mp
  let rank (x : (↑S : Set V)) : ℕ := if x = root then 0 else if x.val ∈ A then 1 else 2
  have rootRank : rank root = 0 := by simp [rank]
  have rankA {x : (↑S : Set V)} (hx : x.val ∈ A) : rank x = 1 := by
    have ne : x ≠ root := fun eq => offA ((show x.val = z from congrArg Subtype.val eq) ▸ hx)
    simp [rank,ne,hx]
  have rankB {x : (↑S : Set V)} (hx : x.val ∈ B) : rank x = 2 := by
    have ne : x ≠ root := fun eq => rootOff ((show x.val = z from congrArg Subtype.val eq) ▸ hx)
    have off : x.val ∉ A := fun h => Finset.disjoint_left.mp dis h hx
    simp [rank,ne,off]
  have tree : H.IsTree := by
    apply tree_of_rank root rank
    · intro x y edge
      rcases whereIn x with rfl|a|b <;> rcases whereIn y with rfl|c|d
      · exact (H.loopless root edge).elim
      · simp [rootRank,rankA c]
      · simp [rootRank,rankB d]
      · simp [rootRank,rankA a]
      · exact (indA x.val a y.val c edge).elim
      · simp [rankA a,rankB d]
      · simp [rootRank,rankB b]
      · simp [rankB b,rankA c]
      · exact (indB x.val b y.val d edge).elim
    · intro x h
      have low := h.2
      rw [rootRank] at low
      omega
    · intro x nonroot
      rcases whereIn x with eq|hA|hB
      · exact (nonroot eq).elim
      · refine ⟨root,⟨(first x.val hA).symm,by simp [rootRank,rankA hA]⟩,?_⟩
        intro y hy
        rcases whereIn y with h|a|b
        · exact h
        · have lo := hy.2
          rw [rankA a,rankA hA] at lo
          omega
        · have lo := hy.2
          rw [rankB b,rankA hA] at lo
          omega
      · obtain ⟨y,⟨yA,xy⟩,unique⟩ := attach x.val hB
        let p : (↑S : Set V) := ⟨y,Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl yA))⟩
        refine ⟨p,⟨xy,by simp [rankA (x := p) yA,rankB hB]⟩,?_⟩
        intro q hq
        rcases whereIn q with rfl|a|b
        · exact (second x.val hB hq.1.symm).elim
        · exact Subtype.ext (unique q.val ⟨a,hq.1⟩)
        · have lo := hq.2
          rw [rankB b,rankB hB] at lo
          omega
  exact size ▸ card_le_treeNumber S tree

#print axioms two_layer_tree_bound

end Graffiti199Depleted.Catalogue
