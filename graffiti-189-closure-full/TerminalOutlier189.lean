import DegreeFiveRouteBasic189
import ArticulationClique189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
set_option linter.unusedSectionVars false

/-- A spanning path of a clique plus one outlier, with both roots in the
clique. Two outlier neighbors suffice provided one is not a root. -/
theorem terminal_path_in_clique_with_outlier {A : Finset V} (clique : CompleteOn G A)
    {x y z w v : V} (xA : x∈A) (yA : y∈A) (wA : w∈A) (vA : v∈A)
    (zA : z∉A) (xy : x≠y) (wx : w≠x) (wy : w≠y) (wv : w≠v)
    (zw : G.Adj z w) (zv : G.Adj z v) :
    RouteOn G (insert z A) x y := by
  classical
  have run {r t : V} (rA : r∈A) (tA : t∈A) (rt : r≠t)
      (wr : w≠r) (wt : w≠t) (vt : v≠t) :
      RouteOn G (insert z A) r t := by
    let B := A.erase r |>.erase v
    have wB : w∈B := mem_erase.mpr ⟨wv,mem_erase.mpr ⟨wr,wA⟩⟩
    have tB : t∈B := mem_erase.mpr ⟨vt.symm,mem_erase.mpr ⟨rt.symm,tA⟩⟩
    have Bsub : B⊆A := (erase_subset _ _).trans (erase_subset _ _)
    have cB : CompleteOn G B := fun u hu v hv ne=>clique u (Bsub hu) v (Bsub hv) ne
    obtain ⟨q,qp,qs⟩ := path_between_in_clique B cB wB tB wt
    have p : RouteOn G B w t := ⟨q,qp,qs⟩
    have zB : z∉B := fun h=>zA (Bsub h)
    have zV : z≠v := fun e=>zA (e.symm ▸ vA)
    have zR : z≠r := fun e=>zA (e.symm ▸ rA)
    have vB : v∉B := by simp [B]
    have rB : r∉B := by simp [B]
    have p1 := p.prefix zw zB
    have p2 := p1.prefix zv.symm (fun h=>(mem_insert.mp h).elim zV.symm vB)
    by_cases eq : r=v
    · have setEq : insert v (insert z B)=insert z A := by
        ext u
        change u∈insert v (insert z ((A.erase r).erase v)) ↔ _
        by_cases uv : u=v
        · simp [uv,vA]
        simp [eq,uv]
      rw [setEq,←eq] at p2
      exact p2
    have p3 := p2.prefix (clique r rA v vA eq) (by simp [eq,zR.symm,rB])
    have setEq : insert r (insert v (insert z B))=insert z A := by
      ext u
      change u∈insert r (insert v (insert z ((A.erase r).erase v))) ↔ _
      by_cases ur : u=r
      · simp [ur,rA]
      by_cases uv : u=v
      · simp [uv,vA]
      simp [ur,uv]
    rwa [setEq] at p3
  by_cases vy : v=y
  · exact (run yA xA xy.symm wy wx (vy ▸ xy.symm)).reverse
  exact run xA yA xy wx wy vy

#print axioms terminal_path_in_clique_with_outlier
end Graffiti189LongestPath.CrossSaturation
