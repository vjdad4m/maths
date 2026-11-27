import ThreePathWithRoute

open private ClawShore.leaf_mem ClawShore.center_mem ClawShore.leaf_only from OppositeClaw
open private two_present_ports from TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

private theorem shared_port_of_claw (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3) (boundary : ShoreBoundary G D B) :
    ∃ q ∈ D, ∃ x ∈ C.leaves, ∃ z ∈ C.leaves, x ≠ z ∧ G.Adj q x ∧ G.Adj q z := by
  obtain ⟨x,hx⟩ : C.leaves.Nonempty := Finset.card_pos.mp (by have := C.three; omega)
  obtain ⟨z,hz,zx⟩ := Finset.exists_ne_of_one_lt_card (by have := C.three; omega : 1 < C.leaves.card) x
  let nx := D.filter (G.Adj x)
  let nz := D.filter (G.Adj z)
  have twoX : 2 ≤ nx.card := at_least_two_ports_of_shore_endpoint conn boundary (ClawShore.leaf_mem C hx) (ClawShore.leaf_only C hx)
  have twoZ : 2 ≤ nz.card := at_least_two_ports_of_shore_endpoint conn boundary (ClawShore.leaf_mem C hz) (ClawShore.leaf_only C hz)
  have upper : (nx ∪ nz).card ≤ 3 := by
    rw [← size]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..))
  have counts := Finset.card_union_add_card_inter nx nz
  obtain ⟨q,hq⟩ : (nx ∩ nz).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨qx,qz⟩ := Finset.mem_inter.mp hq
  exact ⟨q,(Finset.mem_filter.mp qx).1,x,hx,z,hz,zx.symm,(Finset.mem_filter.mp qx).2.symm,
    (Finset.mem_filter.mp qz).2.symm⟩

omit [DecidableRel G.Adj] [Fintype V] in
private theorem traceable_of_claw_after_route (C : ClawShore G B)
    {p s q x z y : V} (ps : p ≠ s) (pq : p ≠ q) (sq : s ≠ q)
    (offA : ∀ v ∈ ({p,s,q} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,s,q} : Finset V), v ∉ B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,s,q} : Finset V))
    (frame : C.leaves = {x,z,y}) (xz : x ≠ z) (xy : x ≠ y) (zy : z ≠ y)
    (sz : G.Adj s z) (qz : G.Adj q z) (qx : G.Adj q x)
    (route : ShoreRoute G A p s) : Traceable G := by
  have hx : x ∈ C.leaves := frame.symm ▸ (by simp : x ∈ ({x,z,y} : Finset V))
  have hy : y ∈ C.leaves := frame.symm ▸ (by simp : y ∈ ({x,z,y} : Finset V))
  have hz : z ∈ C.leaves := frame.symm ▸ (by simp : z ∈ ({x,z,y} : Finset V))
  have neCenter (v : V) (hv : v ∈ C.leaves) : C.center ≠ v := fun eq => C.off (eq.symm ▸ hv)
  let ports := [p,s,q]
  let claw := [C.center,x,z,y]
  have memPorts (v : V) : v ∈ ports ↔ v ∈ ({p,s,q} : Finset V) := by simp [ports]
  have memClaw (v : V) : v ∈ claw ↔ v ∈ B := by
    have eq : v ∈ B ↔ v ∈ insert C.center (↑C.leaves : Set V) :=
      Iff.of_eq (congrArg (fun U : Set V => v ∈ U) C.cover)
    rw [eq,frame]
    simp [claw]
  have nd : (ports ++ claw).Nodup := by
    refine List.nodup_append.mpr ⟨by simp [ports,ps,pq,sq],
      by simp [claw,neCenter _ hx,neCenter _ hy,neCenter _ hz,xz,xy,zy],?_⟩
    exact fun v h₁ h₂ => offB v ((memPorts v).mp h₁) ((memClaw v).mp h₂)
  let f : Fin 7 → V := ![p,s,q,C.center,x,z,y]
  have perm : ([p] ++ [s,z,q,x,C.center,y]).Perm (ports ++ claw) :=
    (show ([0,1,5,2,4,3,6] : List (Fin 7)).Perm [0,1,2,3,4,5,6] by decide).map f
  have coverage (v : V) : v ∈ [p] ++ [s,z,q,x,C.center,y] ↔ v ∉ A := by
    rw [perm.mem_iff,List.mem_append,memPorts,memClaw]
    constructor
    · rintro (vd|vb)
      · exact offA _ vd
      · exact Set.disjoint_left.mp apart.symm vb
    · intro va
      rcases cover v with h|h|h
      · exact (va h).elim
      · exact Or.inr h
      · exact Or.inl h
  exact traceable_of_route_between_lists (L := [p]) (R := [s,z,q,x,C.center,y])
    route (List.chain'_singleton _)
    (by simp [List.chain'_cons,sz,qz.symm,qx,(C.spokes _ hx).symm,C.spokes _ hy])
    (by simp) (by simp) ((List.Perm.nodup_iff perm).mpr nd) coverage

private theorem traceable_of_claw_and_route_with_shared_port (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) {p s q x z : V}
    (ps : p ≠ s) (pq : p ≠ q) (sq : s ≠ q)
    (offA : ∀ v ∈ ({p,s,q} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,s,q} : Finset V), v ∉ B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,s,q} : Finset V))
    (boundary : ShoreBoundary G {p,s,q} B)
    (hx : x ∈ C.leaves) (hz : z ∈ C.leaves) (xz : x ≠ z) (qx : G.Adj q x) (qz : G.Adj q z)
    (route : ShoreRoute G A p s) : Traceable G := by
  classical
  obtain ⟨y,hy,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show ({x,z} : Finset V).card < C.leaves.card by rw [Finset.card_pair xz,C.three]; decide)
  have xy : x ≠ y := fun e => off (by simp [← e])
  have zy : z ≠ y := fun e => off (by simp [← e])
  have frame : C.leaves = {x,z,y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl
      · exact hx
      · exact hz
      · exact hy
    · rw [C.three,Finset.card_insert_of_not_mem (by simp [xz,xy]),Finset.card_pair zy]
  by_cases sz : G.Adj s z
  · exact traceable_of_claw_after_route C ps pq sq offA offB apart cover frame xz xy zy sz qz qx route
  · have two := at_least_two_ports_of_shore_endpoint conn boundary (ClawShore.leaf_mem C hz) (ClawShore.leaf_only C hz)
    have perm : ({p,q,s} : Finset V) = {p,s,q} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have pz := (two_present_ports pq (by simpa only [perm] using two) sz).1
    have swap : ({s,p,q} : Finset V) = {p,s,q} := Finset.insert_comm _ _ _
    exact traceable_of_claw_after_route C ps.symm sq pq (swap.symm ▸ offA) (swap.symm ▸ offB)
      apart (swap.symm ▸ cover) frame xz xy zy pz qz qx route.reverse

omit [DecidableRel G.Adj] [Fintype V] in
private theorem split_other_ports (size : D.card = 3) {q : V} (hq : q ∈ D) :
    ∃ p s, p ≠ s ∧ p ≠ q ∧ s ≠ q ∧ D = {p,s,q} := by
  have count : (D.erase q).card = 2 := by rw [Finset.card_erase_of_mem hq,size]
  obtain ⟨p,s,ps,ports⟩ := Finset.card_eq_two.mp count
  have pE : p ∈ D.erase q := ports.symm ▸ (by simp : p ∈ ({p,s} : Finset V))
  have sE : s ∈ D.erase q := ports.symm ▸ (by simp : s ∈ ({p,s} : Finset V))
  refine ⟨p,s,ps,(Finset.mem_erase.mp pE).1,(Finset.mem_erase.mp sE).1,?_⟩
  rw [← Finset.insert_erase hq,ports]
  ext v
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

/-- A clique component can provide the route opposite an induced claw. -/
theorem traceable_of_clique_shore_and_claw (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (clique : A.Pairwise G.Adj) (large : 3 ≤ Nat.card A) : Traceable G := by
  classical
  obtain ⟨q,qD,x,hx,z,hz,xz,qx,qz⟩ := shared_port_of_claw C conn size boundB
  obtain ⟨p,s,ps,pq,sq,frame⟩ := split_other_ports size qD
  subst D
  obtain ⟨f,edges⟩ := shore_distinct_attachments conn size offA boundA large
    ⟨C.center,Set.disjoint_left.mp apart.symm (ClawShore.center_mem C),fun h => offB _ h (ClawShore.center_mem C)⟩
  have route := clique_shore_route clique (p := ⟨p,by simp⟩) (q := ⟨s,by simp⟩)
    (fun h => ps (congrArg Subtype.val h)) f edges
  exact traceable_of_claw_and_route_with_shared_port C conn ps pq sq offA offB apart cover
    boundB hx hz xz qx qz route

/-- An induced three-vertex path and an induced claw separated by
a three-cut yield a spanning path if the six-vertex tree is forbidden. -/
theorem traceable_of_three_vertex_path_shore_and_claw
    (S : ThreeVertexShore G A) (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D) : Traceable G := by
  classical
  by_contra no
  obtain ⟨q,qD,x,hx,z,hz,xz,qx,qz⟩ := shared_port_of_claw C conn size boundB
  obtain ⟨p,s,ps,pq,sq,frame⟩ := split_other_ports size qD
  subst D
  have forbidden : ¬ ShoreRoute G A p s := fun route =>
    no (traceable_of_claw_and_route_with_shared_port C conn ps pq sq offA offB apart cover
      boundB hx hz xz qx qz route)
  obtain ⟨shared,pair|pair⟩ := common_ports_of_forbidden_three_path_route S conn pq sq boundA forbidden
  · have perm : ({p,q,s} : Finset V) = {p,s,q} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact no (traceable_of_twin_path_shore_and_claw S C conn budget pq ps sq.symm
      (perm.symm ▸ offA) (perm.symm ▸ offB) (perm.symm ▸ boundA) (perm.symm ▸ boundB)
      apart (perm.symm ▸ cover) pair.1 shared.1 pair.2 shared.2)
  · have perm : ({s,q,p} : Finset V) = {p,s,q} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact no (traceable_of_twin_path_shore_and_claw S C conn budget sq ps.symm pq.symm
      (perm.symm ▸ offA) (perm.symm ▸ offB) (perm.symm ▸ boundA) (perm.symm ▸ boundB)
      apart (perm.symm ▸ cover) pair.1 shared.1 pair.2 shared.2)

#print axioms traceable_of_clique_shore_and_claw
#print axioms traceable_of_three_vertex_path_shore_and_claw

end Graffiti199Depleted.Catalogue
