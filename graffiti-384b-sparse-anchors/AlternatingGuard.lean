import SparseGeometry
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the coloring with the two ears on opposite sides, one missing neighbor
at b can be supplied by an edge ending at a common neighbor of c and d. -/
theorem forbidden_edge {e f w b c d i j : V} (bad : bound G<gamma G) (de : G.degree e=2) (df : G.degree f=2)
    (ef : e≠f) (ie : i≠e) (bj : b≠j) (fw : f≠w) (wb : w≠b) (cd : c≠d)
    (ew : G.Adj e w) (eb : G.Adj e b) (fc : G.Adj f c) (fd : G.Adj f d)
    (wc : G.Adj w c) (wd : G.Adj w d) (bi : G.Adj b i) (cj : G.Adj c j) (dj : G.Adj d j)
    (apart : Disjoint ({e,c,d}:Finset V) {f,w,b}) (freshI : i∉({f,w,b}:Finset V))
    (freshJ : j∉({e,c,d}:Finset V)) : ¬G.Adj i j := by
  intro ij
  let L : Finset V := insert j {f,w,b}
  let R : Finset V := insert i {e,c,d}
  have dis : Disjoint L R := by
    dsimp [L,R]; rw [disjoint_insert_left,disjoint_insert_right]
    exact ⟨fun h => (mem_insert.mp h).elim ij.ne.symm freshJ,freshI,apart.symm⟩
  have fr : EarFrame33.Frame G L R := by
    refine ⟨dis,?_,?_⟩
    · intro a am
      simp only [L,mem_insert,mem_singleton] at am
      rcases am with rfl|rfl|rfl|rfl
      · exact PinnedColor34.two G cd cj.symm dj.symm (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G cd fc fd (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G cd wc wd (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G ie bi eb.symm (by simp [R]) (by simp [R])
    · intro a am
      simp only [R,mem_insert,mem_singleton] at am
      rcases am with rfl|rfl|rfl|rfl
      · exact PinnedColor34.two G bj bi.symm ij (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G wb ew eb (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G fw fc.symm wc.symm (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G fw fd.symm wd.symm (by simp [L]) (by simp [L])
  exact ef (Squares29.sparse G bad _ _ fr e (mem_union_right _ (by simp [R])) f (mem_union_left _ (by simp [L])) de df)
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.forbidden_edge
