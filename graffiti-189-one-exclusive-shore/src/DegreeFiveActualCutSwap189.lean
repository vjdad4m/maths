import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Reversing the distinguished cut vertices leaves all shores unchanged. -/
private def swap_cut_graph : (CutGraph (G:=G) a b) ≃g (CutGraph (G:=G) b a) where
  toEquiv :=
    ⟨fun x=>⟨x.val,x.property.2,x.property.1⟩,
      fun x=>⟨x.val,x.property.2,x.property.1⟩,
      fun _=>rfl,fun _=>rfl⟩
  map_rel_iff' := Iff.rfl

private abbrev swapCut :
    (CutGraph (G:=G) a b).ConnectedComponent ≃ (CutGraph (G:=G) b a).ConnectedComponent :=
  swap_cut_graph.connectedComponentEquiv

theorem shore_swapCut (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    Shore (swapCut C) = Shore C := by
  ext v
  rw [mem_shore,mem_shore]
  constructor
  · rintro ⟨h,e⟩
    have e' : swapCut ((CutGraph (G:=G) a b).connectedComponentMk ⟨v,h.2,h.1⟩) = swapCut C := e
    exact ⟨⟨h.2,h.1⟩,swapCut.injective e'⟩
  · rintro ⟨h,e⟩
    exact ⟨⟨h.2,h.1⟩,congrArg swapCut e⟩

#print axioms shore_swapCut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
