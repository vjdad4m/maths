import DegreeFiveAlternatingBlock189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem route_clique_join_end_leaf_allow_leaf_start {H L : Finset V} {x y : V}
    (dis : Disjoint H L) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ l∈L,G.Adj h l)
    (cap : L.card≤H.card+1) (xh : x∈H) (yl : y∈L) :
    ∃ z,RouteOn G (H∪L) z y := by
  classical
  by_cases small : L.card≤H.card
  · obtain ⟨z,_,p⟩ := route_clique_join_end_leaf dis cl
      (fun h hh l ll=>cross h hh l (mem_erase.mp ll).2) small xh yl (cross x xh y yl)
    exact ⟨z,p⟩
  have pos : 0<(L.erase y).card := by
    rw [card_erase_of_mem yl]
    have h := card_pos.mpr ⟨x,xh⟩
    omega
  obtain ⟨u,uu⟩ := card_pos.mp pos
  obtain ⟨uy,ul⟩ := mem_erase.mp uu
  let K := L.erase u
  have ks : K⊆L := erase_subset _ _
  have yk : y∈K := mem_erase.mpr ⟨uy.symm,yl⟩
  have cap' : K.card≤H.card := by
    change (L.erase u).card≤H.card
    rw [card_erase_of_mem ul]
    omega
  obtain ⟨z,zh,p⟩ := route_clique_join_end_leaf (dis.mono (Subset.refl _) ks) cl
    (fun h hh l ll=>cross h hh l (ks (mem_erase.mp ll).2)) cap' xh yk (cross x xh y yl)
  have n : u∉H∪K := by
    intro m
    exact (mem_union.mp m).elim (fun uh=>disjoint_left.mp dis uh ul)
      (fun uk=>(mem_erase.mp uk).1 rfl)
  have q := p.prefix (cross z zh u ul).symm n
  have eq : insert u (H∪K)=H∪L := by
    ext v
    by_cases h : v=u
    · subst v
      simp [ul]
    simp [K,h]
  exact ⟨u,eq ▸ q⟩

#print axioms route_clique_join_end_leaf_allow_leaf_start
end Graffiti189LongestPath.CrossSaturation
