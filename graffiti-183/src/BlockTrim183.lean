import Exceptional183

namespace Graffiti183.Exceptional
open SimpleGraph Finset Short177 Graffiti179

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Use a maximal induced bipartite block whose two removable vertices are
not the entire neighborhood in the block of any exterior vertex. -/
theorem two_gain_from_block {seed : Finset V} (b : Graffiti179.Block G univ seed)
    (hc : G.Connected) {a d : V} (ha : a ∈ b.A ∪ b.B) (hd : d ∈ b.A ∪ b.B)
    (hne : a ≠ d)
    (hcon : Graffiti177.Con G ((b.A ∪ b.B) \ {a,d}))
    (haD : Graffiti177.Dominates G ((b.A ∪ b.B) \ {a,d}) a)
    (hdD : Graffiti177.Dominates G ((b.A ∪ b.B) \ {a,d}) d)
    (hnoblocker : ¬ ∃ x ∉ b.A ∪ b.B, G.Adj x a ∧ G.Adj x d ∧
       ∀ y ∈ (b.A ∪ b.B) \ {a,d}, ¬ G.Adj x y) :
    Fintype.card V + 2 ≤ Graffiti183.maxLeaves G + Graffiti183.bipartiteNumber G := by
  classical
  let T := b.A ∪ b.B
  let D := T \ {a,d}
  have hbud : D.card + 2 ≤ T.card := by
    have sub : ({a,d} : Finset V) ⊆ T := by simp [T,insert_subset_iff,ha,hd]
    have hn := card_sdiff_add_card_eq_card sub
    rw [card_pair hne] at hn
    exact hn.le
  have hcov : closed G T ⊆ closed G D := by
    intro x hx
    by_cases hxt : x ∈ T
    · by_cases xa : x = a
      · subst x
        exact (mem_closed G).mpr (Or.inr haD)
      by_cases xd : x = d
      · subst x
        exact (mem_closed G).mpr (Or.inr hdD)
      exact (mem_closed G).mpr (Or.inl (mem_sdiff.mpr ⟨hxt,by simp [xa,xd]⟩))
    · by_contra! h
      have hh (y : V) (hy : y ∈ D) : ¬G.Adj x y := fun e =>
        h ((mem_closed G).mpr (Or.inr ⟨y,hy,e⟩))
      obtain ⟨⟨y,hy,exy⟩,⟨z,hz,exz⟩⟩ :=
        b.maximal (mem_univ _) hxt (((mem_closed G).mp hx).resolve_left hxt)
      have yT := mem_union_left b.B hy
      have zT := mem_union_right b.A hz
      have ypair : y ∈ ({a,d} : Finset V) := by
        by_contra! hf
        exact hh y (mem_sdiff.mpr ⟨yT,hf⟩) exy
      have zpair : z ∈ ({a,d} : Finset V) := by
        by_contra! hf
        exact hh z (mem_sdiff.mpr ⟨zT,hf⟩) exz
      have yzne : y ≠ z := fun e => (disjoint_left.mp b.disjoint) hy (e.symm ▸ hz)
      simp only [mem_insert,mem_singleton] at ypair zpair
      rcases ypair with rfl | rfl <;> rcases zpair with rfl | rfl
      · exact yzne rfl
      · exact hnoblocker ⟨x,hxt,exy,exz,hh⟩
      · exact hnoblocker ⟨x,hxt,exz,exy,hh⟩
      · exact yzne rfl
  have st : Graffiti179.State G 2 T D :=
    ⟨⟨b.A,b.B,b.disjoint,rfl,b.indA,b.indB⟩,hcon,hbud,hcov⟩
  have h := Graffiti179.complete_state G hc (Graffiti179.trim_one G) 2 T D st ⟨a,ha⟩
  exact h.trans (Nat.add_le_add (Graffiti185.Reuse.leaves_bridge G)
    (Graffiti185.Reuse.bipartite_bridge G))

#print axioms two_gain_from_block

end Graffiti183.Exceptional
