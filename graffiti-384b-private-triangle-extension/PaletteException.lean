import TrappedAnchor
namespace Graffiti384b.TriangleFrame
open Finset SimpleGraph LowSample FiveChoice
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two high vertices with one triangle each imply that the number of triangle counts
cannot exceed the number of high vertices. -/
theorem palette_of_two_singletons {x y : V} (xh : x∈high G) (yh : y∈high G) (xy : x≠y)
    (sx : trianglesAt G x=1) (sy : trianglesAt G y=1) : (types G).card≤(high G).card := by
  classical
  let S := ((high G).erase x).image (trianglesAt G)
  have one : 1∈S := mem_image.mpr ⟨y,mem_erase.mpr ⟨xy.symm,yh⟩,sy⟩
  have sub : types G⊆insert 0 S := by
    intro k km
    obtain ⟨v,_,rfl⟩ := mem_image.mp km
    by_cases vh : v∈high G
    · by_cases same : v=x
      · subst v; rw [sx]; exact mem_insert_of_mem one
      · exact mem_insert_of_mem (mem_image.mpr ⟨v,mem_erase.mpr ⟨same,vh⟩,rfl⟩)
    · have vd : G.degree v≤2 := by by_contra! dg; exact vh (mem_filter.mpr ⟨mem_univ _,dg⟩)
      have cap := (Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 vd)
      rw [Nat.choose_self] at cap
      rcases Nat.eq_zero_or_pos (trianglesAt G v) with zero|pos
      · rw [zero]; exact mem_insert_self ..
      · rw [show trianglesAt G v=1 by omega]; exact mem_insert_of_mem one
  have comp := (card_le_card sub).trans (card_insert_le 0 S)
  have bound : S.card≤((high G).erase x).card := card_image_le
  rw [card_erase_of_mem xh] at bound
  have pos := card_pos.mpr ⟨x,xh⟩
  omega

/-- A failure of the catalogue bound cannot contain a triangle whose two non-ear
vertices have triangle count one. This removes the local exception from the graph application. -/
theorem no_thin_of_failure (bad : bound G<gamma G) : NoThinPair G ∅ (twos G) := by
  intro a x m xo mo ax am xm
  have highOf {v w : V} (vo : v∉∅∪twos G) (av : G.Adj a v) (aw : G.Adj a w) (vw : G.Adj v w) :
      v∈high G := by
    by_contra low
    have d : 2≤G.degree v := by
      rw [←card_neighborFinset_eq_degree]
      exact one_lt_card.mpr ⟨a,(G.mem_neighborFinset ..).mpr av.symm,w,(G.mem_neighborFinset ..).mpr vw,aw.ne⟩
    exact vo (mem_union_right _ (show v∈twos G from mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,d⟩,low⟩))
  by_contra! small
  have xp := (TrianglePrune.triangle_iff G x).mpr ⟨a,m,ax.symm,xm,am⟩
  have mp := (TrianglePrune.triangle_iff G m).mpr ⟨a,x,am.symm,xm.symm,ax⟩
  have few := palette_of_two_singletons G (highOf xo ax am xm) (highOf mo am ax xm.symm) xm.ne
    (by omega) (by omega)
  exact (not_lt_of_ge (exact_of_high G (by omega))) bad

/-- Structural exception at every diversity: an independent-ear counterexample with enough
nonleaves has a singly exposed anchor trapping all its non-ear triangles. -/
theorem failed_graph_has_trapped_anchor (quota : (types G).card≤(nonleaves G).card)
    (indep : Disjoint (twos G) (anchors G)) (bad : bound G<gamma G) :
    ∃a∈anchors G,nbr G a (twos G)=1 ∧
      (∀p∈link G a,Disjoint p (twos G) → p⊆anchors G) ∧
      trianglesAt G a≤1+(internalTriangles G a).card :=
  necessary_trap G quota indep (no_thin_of_failure G bad) bad

end Graffiti384b.TriangleFrame
#print axioms Graffiti384b.TriangleFrame.palette_of_two_singletons
#print axioms Graffiti384b.TriangleFrame.no_thin_of_failure
#print axioms Graffiti384b.TriangleFrame.failed_graph_has_trapped_anchor
