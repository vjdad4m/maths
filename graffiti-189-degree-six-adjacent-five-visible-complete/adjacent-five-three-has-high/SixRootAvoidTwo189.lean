import SixRootAvoid189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair Graffiti189Ore
open private getVert_injective_on from OreSpliceIndex189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem route_avoid_two_free (S : Finset V) {u z t : V}
    (r : RouteOn G S u z) (tm : t∈S) (deg : 3≤(inside G S z).card) :
    ∃ v∈S,v≠z ∧ v≠t ∧ RouteOn G S u v := by
  classical
  obtain ⟨p,pp,ps⟩ := r
  obtain ⟨j,jt,jl⟩ := mem_support_iff_exists_getVert.mp ((ps t).mpr tm)
  let a := p.getVert (p.length-1)
  let b := p.getVert (j-1)
  have some : ∃ w∈inside G S z,w≠a ∧ w≠b := by
    by_contra no
    have sub : inside G S z⊆({a,b}:Finset V) := by
      intro w wm
      by_cases x : w=a
      · exact mem_insert.mpr (.inl x)
      by_cases y : w=b
      · exact mem_insert.mpr (.inr (mem_singleton.mpr y))
      exact (no ⟨w,wm,x,y⟩).elim
    have low := card_le_card sub
    have up := card_insert_le a ({b}:Finset V)
    rw [card_singleton] at up
    omega
  obtain ⟨w,wm,wa,wb⟩ := some
  obtain ⟨ws,zw⟩ := mem_filter.mp wm
  obtain ⟨i,iw,il⟩ := mem_support_iff_exists_getVert.mp ((ps w).mpr ws)
  have ine : i≠p.length := by
    intro e
    subst i
    exact zw.ne (p.getVert_length.symm.trans iw)
  have hi : i<p.length := by omega
  have jump : G.Adj z (p.getVert i) := iw.symm ▸ zw
  obtain ⟨q,qp,qs⟩ := ore_spliced_path p pp i hi jump
  have neZ : p.getVert (i+1)≠z := by
    intro e
    have k := getVert_injective_on p pp (by omega) (by omega) (e.trans p.getVert_length.symm)
    have f : i=p.length-1 := by omega
    exact wa (iw.symm.trans (congrArg p.getVert f))
  have neT : p.getVert (i+1)≠t := by
    intro e
    have k := getVert_injective_on p pp (by omega) jl (e.trans jt.symm)
    have f : i=j-1 := by omega
    exact wb (iw.symm.trans (congrArg p.getVert f))
  have vm : p.getVert (i+1)∈S := (ps _).mp ((qs _).mp q.end_mem_support)
  exact ⟨_,vm,neZ,neT,q,qp,fun w=>(qs w).trans (ps w)⟩

#print axioms route_avoid_two_free
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
