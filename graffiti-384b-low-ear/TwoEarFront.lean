import RootRank
namespace Graffiti384b.TwoEars
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem profile (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G) :
    (high G).card=29 ∧ (LowSample.twos G).card=2 := by
  have lim := type_bound G
  have miss : ((high G).card+1)/2<((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) bad)
  have ne : (high G).card≠30 := fun h => (not_lt_of_ge (Cover31.exact_thirty G t (by omega) h)) bad
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have count : (LowSample.twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  omega

/-- For every order, two degree-two vertices in a failure at the 31/31 quotas
are independent and all their neighbors have degree at least three. -/
theorem high_anchors (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G)
    {e : V} (de : G.degree e=2) : G.neighborFinset e⊆high G := by
  classical
  intro l lm
  by_contra low
  obtain ⟨hs,es⟩ := profile G t q bad
  obtain ⟨z,zm,zl⟩ := exists_mem_ne (s:=G.neighborFinset e) (by rw [card_neighborFinset_eq_degree,de]; decide) l
  have eq := eq_of_subset_of_card_le (insert_subset lm (singleton_subset_iff.mpr zm))
    (by rw [card_neighborFinset_eq_degree,de,card_pair zl.symm])
  have hnon : (high G).Nonempty := card_pos.mp (by omega)
  obtain ⟨c,ch,keep⟩ : ∃ c∈high G,z∉(high G).erase c := by
    by_cases zh : z∈high G
    · exact ⟨z,zh,not_mem_erase _ _⟩
    · obtain ⟨c,ch⟩ := hnon; exact ⟨c,ch,fun m => zh (mem_erase.mp m).2⟩
  apply (not_lt_of_ge (pinned G t hs es ch de ?_)) bad
  intro w wx ew
  have wn := (G.mem_neighborFinset ..).mpr ew
  rw [←eq,mem_insert,mem_singleton] at wn
  exact wn.elim (fun h => low (h ▸ (mem_erase.mp wx).2)) (fun h => keep (h ▸ wx))

theorem exact_of_low_neighbor (t : (types G).card=31) (q : (nonleaves G).card=31)
    {e w : V} (de : G.degree e=2) (ew : G.Adj e w) (low : G.degree w≤2) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have wh := high_anchors G t q bad de ((G.mem_neighborFinset ..).mpr ew)
  have wh' := (mem_filter.mp wh).2; omega

end Graffiti384b.TwoEars
#print axioms Graffiti384b.TwoEars.profile
#print axioms Graffiti384b.TwoEars.high_anchors
#print axioms Graffiti384b.TwoEars.exact_of_low_neighbor
