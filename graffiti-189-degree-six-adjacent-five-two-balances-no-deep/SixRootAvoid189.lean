import SixRootedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair Graffiti189Ore
open private getVert_injective_on from OreSpliceIndex189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- One rotation preserves the prescribed end and evades a forbidden free
end if that end has at least two neighbors in the support. -/
theorem route_avoid_free_end (S : Finset V) {u z : V}
    (r : RouteOn G S u z) (deg : 2≤(inside G S z).card) :
    ∃ v∈S,v≠z ∧ RouteOn G S u v := by
  obtain ⟨p,pp,ps⟩ := r
  have c : 1<(inside G S z).card := by omega
  obtain ⟨w,wm,wn⟩ := exists_ne_of_one_lt_card c (p.getVert (p.length-1))
  obtain ⟨ws,zw⟩ := mem_filter.mp wm
  obtain ⟨i,iw,il⟩ := mem_support_iff_exists_getVert.mp ((ps w).mpr ws)
  have ine : i≠p.length := by
    intro e
    subst i
    exact zw.ne (p.getVert_length.symm.trans iw)
  have h : i<p.length := by omega
  have jump : G.Adj z (p.getVert i) := iw.symm ▸ zw
  obtain ⟨q,qp,qs⟩ := ore_spliced_path p pp i h jump
  have ioff : i+1≠p.length := by
    intro e
    have f : i=p.length-1 := by omega
    exact wn (iw.symm.trans (congrArg p.getVert f))
  have ene : p.getVert (i+1)≠z := by
    intro e
    exact ioff (getVert_injective_on p pp (by omega) (by omega) (e.trans p.getVert_length.symm))
  have eS : p.getVert (i+1)∈S := (ps _).mp ((qs _).mp q.end_mem_support)
  exact ⟨_,eS,ene,q,qp,fun w=>(qs w).trans (ps w)⟩

#print axioms route_avoid_free_end
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
