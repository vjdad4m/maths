import ThreePins
import CompleteAdjacent
namespace Graffiti384b.Shared
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the independent-ear profile, an ear adjacent to a leaf is necessary
for failure. There is no contact-count or connectivity hypothesis. -/
theorem exact_without_leaf_attachment (n : Fintype.card V=33) (q : (nonleaves G).card=32)
    (t : (types G).card=31) (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (noLeaf : ∀ u v,G.degree u=2 → G.degree v=1 → ¬G.Adj u v) : gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨e,a,b,de,ab,ear,thin⟩ := Squares29.thin_at_32 G t q bad
  let A : Finset V := {a,b}
  have highNbr {u w : V} (du : G.degree u=2) (uw : G.Adj u w) : w∈high G := by
    apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
    have ne2 : G.degree w≠2 := fun dw => ind u w du dw uw
    have ne1 : G.degree w≠1 := fun dw => noLeaf u w du dw uw
    have pos : 0<(G.neighborFinset w).card := card_pos.mpr ⟨u,(G.mem_neighborFinset ..).mpr uw.symm⟩
    rw [card_neighborFinset_eq_degree] at pos; omega
  have anchors : A⊆high G := by
    intro w wm; exact highNbr de ((G.mem_neighborFinset ..).mp (ear ▸ wm))
  by_cases clean : ∀ v,G.degree v=2 → v≠e → G.neighborFinset v⊆high G\A
  · exact (not_lt_of_ge (Clean.exact_clean G n q t ear ab thin ind anchors clean)) bad
  push_neg at clean
  obtain ⟨f,df,fe,off⟩ := clean
  obtain ⟨w,wm,wo⟩ := not_subset.mp off
  have wa : w∈A := by
    by_contra h
    exact wo (mem_sdiff.mpr ⟨highNbr df ((G.mem_neighborFinset ..).mp wm),h⟩)
  obtain ⟨z,zm,zw⟩ := exists_mem_ne (s:=G.neighborFinset f) (by rw [card_neighborFinset_eq_degree,df]; decide) w
  have fn : G.neighborFinset f={w,z} := (eq_of_subset_of_card_le
    (insert_subset wm (singleton_subset_iff.mpr zm)) (by rw [card_neighborFinset_eq_degree,df,card_pair zw.symm])).symm
  have za : z∉A := by
    intro membership
    have sub : G.neighborFinset f⊆A := fn ▸ insert_subset wa (singleton_subset_iff.mpr membership)
    have equal := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,df]; exact (card_pair ab).le)
    exact (not_lt_of_ge (Repair.exact_of_twin_degree_two G fe df (equal.trans ear.symm))) bad
  have az : a≠z := fun eq => za (eq ▸ mem_insert_self ..)
  have bz : b≠z := fun eq => za (eq ▸ mem_insert_of_mem (mem_singleton_self _))
  have zh := highNbr df ((G.mem_neighborFinset ..).mp zm)
  have sub : A⊆({a,b,z}:Finset V) := by
    intro i m; rcases mem_insert.mp m with eq|eq
    · exact mem_insert.mpr (Or.inl eq)
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (mem_singleton.mp eq)))
  have pins : ({a,b,z}:Finset V)⊆high G := insert_subset (anchors (mem_insert_self ..))
    (insert_subset (anchors (mem_insert_of_mem (mem_singleton_self _))) (singleton_subset_iff.mpr zh))
  have other : G.neighborFinset f⊆{a,b,z} := fn ▸ insert_subset (sub wa) (singleton_subset_iff.mpr (by simp))
  exact (not_lt_of_ge (three_pins G n q t fe.symm ear ab thin az bz pins df other ind)) bad

/-- Every failure at these three quotas has an edge between a degree-one
vertex and a degree-two vertex, regardless of adjacency among the ears. -/
theorem leaf_necessary (n : Fintype.card V=33) (q : (nonleaves G).card=32)
    (t : (types G).card=31) (bad : bound G<gamma G) :
    ∃ u v,G.degree u=2 ∧ G.degree v=1 ∧ G.Adj u v := by
  classical
  by_contra! noLeaf
  have ind (u v : V) (du : G.degree u=2) (dv : G.degree v=2) (uv : G.Adj u v) : False :=
    (not_lt_of_ge (AdjacentFull.exact G n q t uv du dv)) bad
  exact (not_lt_of_ge (exact_without_leaf_attachment G n q t ind noLeaf)) bad

end Graffiti384b.Shared
#print axioms Graffiti384b.Shared.exact_without_leaf_attachment
#print axioms Graffiti384b.Shared.leaf_necessary
