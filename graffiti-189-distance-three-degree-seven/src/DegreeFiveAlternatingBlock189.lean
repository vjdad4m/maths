import DegreeFiveAlternatingRoute189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Reserve a single clique slot for a two-vertex peripheral path. -/
theorem route_clique_join_block_before_leaf {H L : Finset V} {x y s t : V}
    (dis : Disjoint H L) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ l∈L.erase y,G.Adj h l)
    (into : ∀ h∈H,G.Adj h s) (out : ∀ h∈H,G.Adj t h)
    (hs : s∉H∪L) (ht : t∉H∪L) (st : G.Adj s t)
    (cap : L.card+1≤H.card) (xh : x∈H) (yl : y∈L) (xy : G.Adj x y) :
    ∃ z∈H,RouteOn G ((H∪L)∪{s,t}) z y := by
  classical
  have k : 0<(H.erase x).card := by
    rw [card_erase_of_mem xh]
    have l := card_pos.mpr ⟨y,yl⟩
    omega
  obtain ⟨u,um⟩ := card_pos.mp k
  obtain ⟨ux,uh⟩ := mem_erase.mp um
  let K := H.erase u
  have kh : K⊆H := erase_subset _ _
  have xk : x∈K := mem_erase.mpr ⟨ux.symm,xh⟩
  have cap' : L.card≤K.card := by
    change L.card≤(H.erase u).card
    rw [card_erase_of_mem uh]
    omega
  have ck : CompleteOn G K := fun r rk v vk ne=>cl r (kh rk) v (kh vk) ne
  obtain ⟨v,vk,p⟩ := route_clique_join_end_leaf (dis.mono kh (Subset.refl _)) ck
    (fun r rk l ll=>cross r (kh rk) l ll) cap' xk yl xy
  have sub : K∪L⊆H∪L := union_subset_union kh (Subset.refl _)
  have tOff : t∉K∪L := fun m=>ht (sub m)
  have sOff : s∉insert t (K∪L) := fun m=>(mem_insert.mp m).elim st.ne (fun m=>hs (sub m))
  have uOff : u∉insert s (insert t (K∪L)) := by
    intro m
    rcases mem_insert.mp m with h|h
    · exact hs (mem_union_left _ (h ▸ uh))
    rcases mem_insert.mp h with h|h
    · exact ht (mem_union_left _ (h ▸ uh))
    exact (mem_union.mp h).elim (fun h=>(mem_erase.mp h).1 rfl)
      (fun ul=>disjoint_left.mp dis uh ul)
  have q := ((p.prefix (out v (kh vk)) tOff).prefix st sOff).prefix (into u uh) uOff
  have eq : insert u (insert s (insert t (K∪L)))=(H∪L)∪{s,t} := by
    ext w
    by_cases h : w=u
    · subst w
      simp [uh]
    simp [K,h,or_comm,or_left_comm,or_assoc]
  exact ⟨u,uh,eq ▸ q⟩

/-- Append a prescribed final two-vertex peripheral block to an alternating
route, maintaining the specified incoming hub. -/
theorem route_clique_join_end_block {H L : Finset V} {x s t : V}
    (dis : Disjoint H L) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ l∈L,G.Adj h l)
    (hs : s∉H∪L) (ht : t∉H∪L) (cap : L.card<H.card) (xh : x∈H)
    (xs : G.Adj x s) (st : G.Adj s t) :
    ∃ z∈H,RouteOn G ((H∪L)∪{s,t}) z t := by
  classical
  obtain ⟨z,zh,p⟩ := route_clique_join_end_hub dis cl cross cap xh
  have off : Disjoint (H∪L) ({s,t} : Finset V) := by
    apply disjoint_left.mpr
    intro u m ut
    rcases mem_insert.mp ut with h|h
    · exact hs (h ▸ m)
    exact ht (mem_singleton.mp h ▸ m)
  exact ⟨z,zh,p.join (RouteOn.edge st) off xs⟩

#print axioms route_clique_join_block_before_leaf
#print axioms route_clique_join_end_block
end Graffiti189LongestPath.CrossSaturation
