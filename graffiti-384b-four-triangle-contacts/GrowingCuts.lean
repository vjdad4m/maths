import FourFront
namespace Graffiti384b.Four29
open Finset SimpleGraph LowSample
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Enlarge B by all unassigned vertices having two neighbors already in A. -/
def extendShore (A B : Finset V) := B ∪ ((A∪B)ᶜ.filter (fun v => 2≤nbr G v A))

/-- One round extends the second shore, then the first. -/
def growPins : ℕ → Finset V × Finset V → Finset V × Finset V
  | 0,S => S
  | k+1,S =>
    let F := growPins k S
    let R := extendShore G F.1 F.2
    (extendShore G R F.1,R)

/-- Only vertices in W may still lack their second opposite neighbor. -/
structure Frame (W : Finset V) (F : Finset V × Finset V) : Prop where
  apart : Disjoint F.1 F.2
  low : twos G⊆F.1∪F.2
  left : ∀x∈F.1,x∉W → 2≤nbr G x F.2
  right : ∀x∈F.2,2≤nbr G x F.1

private theorem extend_disjoint {A B : Finset V} (apart : Disjoint A B) :
    Disjoint A (extendShore G A B) := by
  apply disjoint_left.mpr
  intro v va vm
  rcases mem_union.mp vm with vb|ext
  · exact disjoint_left.mp apart va vb
  · exact mem_compl.mp (mem_filter.mp ext).1 (mem_union_left _ va)

theorem grow_frame {W : Finset V} {S : Finset V × Finset V} (start : Frame G W S) (k : ℕ) :
    Frame G W (growPins G k S) := by
  induction k with
  | zero => exact start
  | succ k ih =>
    let F := growPins G k S
    let R := extendShore G F.1 F.2
    let L := extendShore G R F.1
    change Frame G W (L,R)
    have b : F.2⊆R := subset_union_left
    have a : F.1⊆L := subset_union_left
    have sep := extend_disjoint G ih.apart
    refine ⟨(extend_disjoint G sep.symm).symm,ih.low.trans (union_subset_union a b),?_,?_⟩
    · intro v vl vw
      rcases mem_union.mp vl with old|new
      · exact (ih.left v old vw).trans (Repair.nbr_mono G _ b)
      · exact (mem_filter.mp new).2
    · intro v vr
      apply le_trans _ (Repair.nbr_mono G _ a)
      rcases mem_union.mp vr with old|new
      · exact ih.right v old
      · exact (mem_filter.mp new).2

theorem grow_complete {W : Finset V} {S : Finset V × Finset V} (start : Frame G W S) (k : ℕ)
    (quota : (types G).card≤(nonleaves G).card) (coveredRoots : ∀v∈W,2≤nbr G v (growPins G k S).2) :
    gamma G≤bound G := by
  have F := grow_frame G start k
  apply PinnedColor34.complete G F.apart quota ?_ ?_ F.right
  · intro v vn nl nr
    by_contra! small
    have low : v∈twos G := mem_sdiff.mpr ⟨vn,fun h => (not_le_of_gt small) (mem_filter.mp h).2⟩
    exact (mem_union.mp (F.low low)).elim nl nr
  · intro v vl
    by_cases vw : v∈W
    · exact coveredRoots v vw
    · exact F.left v vl vw

/-- No restriction on the number of triangle contacts or on exterior exposure
is needed when any round covers all four anchors. -/
theorem growing_anchors (t : (types G).card=29) (h : (high G).card=27) (q : (nonleaves G).card=29)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f) (k : ℕ)
    (coveredRoots : ∀w∈roots G e f,2≤nbr G w (growPins G k (roots G e f,{e,f})).2) :
    gamma G≤bound G := by
  by_contra! fail
  have D := data_of_failure G t h q fail de df ne
  let W := roots G e f
  let E : Finset V := {e,f}
  have loc (v : V) (ve : v∈E) : G.neighborFinset v⊆W := by
    rcases mem_insert.mp ve with rfl|m
    · exact subset_union_left
    · rw [mem_singleton.mp m]; exact subset_union_right
  have base : Frame G W (W,E) := by
    refine ⟨disjoint_left.mpr (fun v vw ve => (mem_sdiff.mp (D.earSet.symm ▸ ve : v∈twos G)).2 (D.highRoots vw)),
      ?_,fun _ vw h => (h vw).elim,?_⟩
    · rw [D.earSet]; exact subset_union_right
    · intro v ve
      have sub : G.neighborFinset v⊆W.filter (G.Adj v) := fun j hj =>
        mem_filter.mpr ⟨loc v ve hj,(G.mem_neighborFinset _ _).mp hj⟩
      have le := card_le_card sub
      rw [card_neighborFinset_eq_degree] at le
      exact (mem_filter.mp (mem_sdiff.mp (D.earSet.symm ▸ ve : v∈twos G)).1).2.trans le
  exact (not_lt_of_ge (grow_complete G base k (by omega) coveredRoots)) fail
end Graffiti384b.Four29
#print axioms Graffiti384b.Four29.grow_frame
#print axioms Graffiti384b.Four29.grow_complete
#print axioms Graffiti384b.Four29.growing_anchors
