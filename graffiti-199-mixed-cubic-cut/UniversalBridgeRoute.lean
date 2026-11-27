import AdjacentShore

namespace Graffiti199Depleted.Catalogue.CubicMixedCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] (F : CubicMixedCut G)

/-- For a nonempty common clique, the only endpoint pairs we need
to avoid have a bridge vertex and the sole common vertex. -/
theorem route_with_hub (budget : treeNumber G ≤ 5) (bcEdge : G.Adj F.b F.c)
    (common : F.hub.Nonempty) {x y : V} (xB : x ∈ F.B) (yB : y ∈ F.B) (xy : x ≠ y)
    (flexible : (∃ u ∈ F.hub, ∃ v ∈ F.hub, u ≠ v) ∨
      ((x ∈ F.leftOnly ∨ x ∈ F.rightOnly) ∨ (y ∈ F.leftOnly ∨ y ∈ F.rightOnly))) :
    Traverses G F.B x y := by
  classical
  let K := F.bridge budget bcEdge
  let N := K.left ∪ K.right
  have cover : N ∪ F.hub = F.B := F.blocks_cover budget
  have apart : Disjoint N F.hub := F.hubApart
  have Nsub : N ⊆ F.B := fun v hv => cover ▸ (show v ∈ N ∪ F.hub from Or.inl hv)
  have hubB : F.hub ⊆ F.B := fun v hv => cover ▸ (show v ∈ N ∪ F.hub from Or.inr hv)
  have large {S : Set V} {v w : V} (P : Traverses G S v w) (ne : v ≠ w)
      (sub : S ⊆ F.B) (core : N ⊆ S) : Traverses G F.B v w := by
    apply P.extend_universal ne sub
    intro t tB tS u uB tu
    have th : t ∈ N ∪ F.hub := cover.symm ▸ tB
    exact F.hub_universal budget (th.resolve_left (fun h => tS (core h))) uB tu
  have hubAdj {u v : V} (uh : u ∈ F.hub) (vN : v ∈ N) : G.Adj u v :=
    F.hub_universal budget uh (Nsub vN) (fun eq => Set.disjoint_left.mp apart (eq.symm ▸ vN) uh)
  have hubOff {z : V} (h : z ∈ F.hub) : z ∉ N := fun t => Set.disjoint_left.mp apart t h
  have adj_first {u v : V} (uN : u ∈ N) (vh : v ∈ F.hub) (uv : u ≠ v)
      (ok : (∃ z ∈ F.hub, ∃ t ∈ F.hub, z ≠ t) ∨ (u ∈ F.leftOnly ∨ u ∈ F.rightOnly)) :
      Traverses G F.B u v := by
    rcases ok with two|exclusive
    · obtain ⟨z,zh,t,th,zt⟩ := two
      have spare : ∃ z ∈ F.hub, z ≠ v := by
        by_cases h : z = v
        · exact ⟨t,th,fun k => zt (h.trans k.symm)⟩
        · exact ⟨z,zh,h⟩
      obtain ⟨d,dh,dv⟩ := spare
      have endpoint : ∃ w ∈ N, u ≠ w := by
        rcases uN with ul|ur
        · exact ⟨K.c,Or.inr K.cr,K.left_ne_right ul K.cr⟩
        · exact ⟨K.b,Or.inl K.bl,(K.left_ne_right K.bl ur).symm⟩
      obtain ⟨w,wN,uw⟩ := endpoint
      have core := K.route_with_one_universal uN wN uw (hubOff dh) (fun _ h => hubAdj dh h)
      have vOff : v ∉ N ∪ ({d} : Set V) := by
        rintro (h|eq)
        · exact hubOff vh h
        · exact dv (show v = d from eq).symm
      have path := core.join (Traverses.single v) (Set.disjoint_singleton_right.mpr vOff) (hubAdj vh wN).symm
      apply large path uv
      · rintro t ((tN|td)|tv)
        · exact Nsub tN
        · exact hubB ((show t = d from td).symm ▸ dh)
        · exact hubB ((show t = v from tv).symm ▸ vh)
      · exact fun _ h => Or.inl (Or.inl h)
    · have core : ∃ w ∈ N, Traverses G N u w := by
        rcases exclusive with ul|ur
        · obtain ⟨w,wr,Q⟩ := K.route_from_left (Or.inr ul) (Or.inl ul.1.2.1)
          exact ⟨w,Or.inr wr,Q⟩
        · obtain ⟨w,wr,Q⟩ := K.flip.route_from_left (Or.inr ur) (Or.inl ur.1.2.2)
          have eq : K.flip.left ∪ K.flip.right = N := by
            change K.right ∪ K.left = K.left ∪ K.right
            exact Set.union_comm _ _
          exact ⟨w,Or.inl wr,eq ▸ Q⟩
      obtain ⟨w,wN,P⟩ := core
      have path := P.join (Traverses.single v)
        (Set.disjoint_singleton_right.mpr (hubOff vh)) (hubAdj vh wN).symm
      apply large path uv
      · rintro t (tN|eq)
        · exact Nsub tN
        · exact hubB ((show t = v from eq).symm ▸ vh)
      · exact fun _ h => Or.inl h
  have xcase : x ∈ N ∨ x ∈ F.hub := by
    change x ∈ N ∪ F.hub
    rwa [cover]
  have ycase : y ∈ N ∨ y ∈ F.hub := by
    change y ∈ N ∪ F.hub
    rwa [cover]
  have same (v : V) (vh : v ∈ F.hub) : ¬ (v ∈ F.leftOnly ∨ v ∈ F.rightOnly) := by
    rintro (l|r)
    · exact hubOff vh (Or.inl (Or.inr l))
    · exact hubOff vh (Or.inr (Or.inr r))
  rcases xcase with xN|xh <;> rcases ycase with yN|yh
  · obtain ⟨z,zh⟩ := common
    have P := K.route_with_one_universal xN yN xy (hubOff zh) (fun _ h => hubAdj zh h)
    exact large P xy (fun t h => h.elim (fun e => Nsub e)
      (fun e => hubB ((show t = z from e).symm ▸ zh))) (fun _ h => Or.inl h)
  · exact adj_first xN yh xy (flexible.imp id (fun h => h.resolve_right (same y yh)))
  · exact (adj_first yN xh xy.symm (flexible.imp id (fun h => h.resolve_left (same x xh)))).reverse
  · obtain ⟨u,ul,v,vr,P⟩ := K.some_route
    have first := (Traverses.single x).join P
      (Set.disjoint_singleton_left.mpr (hubOff xh)) (hubAdj xh (Or.inl ul))
    have yOff : y ∉ ({x} : Set V) ∪ N := by
      rintro (eq|hh)
      · exact xy eq.symm
      · exact hubOff yh hh
    have path := first.join (Traverses.single y) (Set.disjoint_singleton_right.mpr yOff)
      (hubAdj yh (Or.inr vr)).symm
    apply large path xy
    · rintro t ((tx|tN)|ty)
      · exact (show t = x from tx).symm ▸ xB
      · exact Nsub tN
      · exact (show t = y from ty).symm ▸ yB
    · exact fun _ h => Or.inl (Or.inr h)

#print axioms route_with_hub

end Graffiti199Depleted.Catalogue.CubicMixedCut
