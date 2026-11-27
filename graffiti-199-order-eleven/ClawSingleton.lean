import OneSingletonRoutes

open private ClawShore.leaf_mem ClawShore.center_mem ClawShore.leaf_only from OppositeClaw
open private shared_port_of_claw split_other_ports from ClawViaCommonPort
open private two_present_ports from TwoShortShores
open private clique_or_path_of_three from CrossingOrder
open private traceable_of_route_clique_with_singleton from OrderTenSingleton

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V} {r : V}

omit [DecidableRel G.Adj] [Fintype V] in
private theorem traceable_of_claw_after_route_and_singleton (C : ClawShore G B)
    {p s q x z y : V} (ps : p ≠ s) (pq : p ≠ q) (sq : s ≠ q)
    (offA : ∀ v ∈ ({p,s,q} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,s,q} : Finset V), v ∉ B)
    (apart : Disjoint A B) (hr : CutSingleton G {p,s,q} r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,s,q} : Finset V) ∨ v = r)
    (frame : C.leaves = {x,z,y}) (xz : x ≠ z) (xy : x ≠ y) (zy : z ≠ y)
    (sz : G.Adj s z) (qz : G.Adj q z) (qx : G.Adj q x)
    (route : ShoreRoute G A p s) : Traceable G := by
  have hx : x ∈ C.leaves := frame.symm ▸ (by simp : x ∈ ({x,z,y} : Finset V))
  have hy : y ∈ C.leaves := frame.symm ▸ (by simp : y ∈ ({x,z,y} : Finset V))
  have hz : z ∈ C.leaves := frame.symm ▸ (by simp : z ∈ ({x,z,y} : Finset V))
  have neCenter (v : V) (hv : v ∈ C.leaves) : C.center ≠ v := fun eq => C.off (eq.symm ▸ hv)
  let ports := [r,p,s,q]
  let claw := [C.center,x,z,y]
  have memPorts (v : V) : v ∈ ports ↔ v = r ∨ v ∈ ({p,s,q} : Finset V) := by simp [ports]
  have memClaw (v : V) : v ∈ claw ↔ v ∈ B := by
    have eq : v ∈ B ↔ v ∈ insert C.center (↑C.leaves : Set V) :=
      Iff.of_eq (congrArg (fun U : Set V => v ∈ U) C.cover)
    rw [eq,frame]
    simp [claw]
  have neR (u : V) (hd : u ∈ ({p,s,q} : Finset V)) : r ≠ u := fun e => hr.1 (e.symm ▸ hd)
  have nd : (ports ++ claw).Nodup := by
    refine List.nodup_append.mpr ⟨by simp [ports,ps,pq,sq,neR p (by simp),neR s (by simp),neR q (by simp)],
      by simp [claw,neCenter _ hx,neCenter _ hy,neCenter _ hz,xz,xy,zy],?_⟩
    intro v h₁ h₂
    rcases (memPorts v).mp h₁ with e|hd
    · exact rB (e ▸ (memClaw v).mp h₂)
    · exact offB v hd ((memClaw v).mp h₂)
  let f : Fin 8 → V := ![r,p,s,q,C.center,x,z,y]
  have perm : ([r,p] ++ [s,z,q,x,C.center,y]).Perm (ports ++ claw) :=
    (show ([0,1,2,6,3,5,4,7] : List (Fin 8)).Perm [0,1,2,3,4,5,6,7] by decide).map f
  have coverage (v : V) : v ∈ [r,p] ++ [s,z,q,x,C.center,y] ↔ v ∉ A := by
    rw [perm.mem_iff,List.mem_append,memPorts,memClaw]
    constructor
    · rintro ((e|vd)|vb)
      · exact e.symm ▸ rA
      · exact offA _ vd
      · exact Set.disjoint_left.mp apart.symm vb
    · intro va
      rcases cover v with h|h|h|h
      · exact (va h).elim
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
  exact traceable_of_route_between_lists (L := [r,p]) (R := [s,z,q,x,C.center,y])
    route (List.chain'_pair.mpr ((hr.2 p).mpr (by simp)))
    (by simp [List.chain'_cons,sz,qz.symm,qx,(C.spokes _ hx).symm,C.spokes _ hy])
    (by simp) (by simp) ((List.Perm.nodup_iff perm).mpr nd) coverage

private theorem traceable_of_claw_and_route_with_shared_port_and_singleton (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) {p s q x z : V}
    (ps : p ≠ s) (pq : p ≠ q) (sq : s ≠ q)
    (offA : ∀ v ∈ ({p,s,q} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,s,q} : Finset V), v ∉ B)
    (apart : Disjoint A B) (hr : CutSingleton G {p,s,q} r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,s,q} : Finset V) ∨ v = r)
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
  · exact traceable_of_claw_after_route_and_singleton C ps pq sq offA offB apart hr rA rB cover frame xz xy zy sz qz qx route
  · have two := at_least_two_ports_of_shore_endpoint conn boundary (ClawShore.leaf_mem C hz) (ClawShore.leaf_only C hz)
    have perm : ({p,q,s} : Finset V) = {p,s,q} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have pz := (two_present_ports pq (by simpa only [perm] using two) sz).1
    have swap : ({s,p,q} : Finset V) = {p,s,q} := Finset.insert_comm _ _ _
    exact traceable_of_claw_after_route_and_singleton C ps.symm sq pq (swap.symm ▸ offA) (swap.symm ▸ offB)
      apart (swap.symm ▸ hr) rA rB (swap.symm ▸ cover) frame xz xy zy pz qz qx route.reverse

private theorem impossible_claw_next_to_shared_pair_and_singleton
    (S : ThreeVertexShore G A) (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) {p q t : V}
    (qt : q ≠ t)
    (offA : ∀ v ∈ ({p,q,t} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,t} : Finset V), v ∉ B)
    (boundA : ShoreBoundary G {p,q,t} A) (boundB : ShoreBoundary G {p,q,t} B)
    (apart : Disjoint A B) (hr : CutSingleton G {p,q,t} r) (rA : r ∉ A) (rB : r ∉ B)
    (pu : G.Adj p S.left) (pz : G.Adj p S.right)
    (qu : G.Adj q S.left) (qz : G.Adj q S.right) : False := by
  have cap (x : V) (xd : x ∈ ({p,q,t} : Finset V))
      (xu : G.Adj x S.left) (xz : G.Adj x S.right) :
      (C.leaves.filter (G.Adj x)).card ≤ 1 := by
    have deny (cl : (shoreContacts G A x).Pairwise G.Adj) : False :=
      S.noLR (cl (show S.left ∈ shoreContacts G A x from ⟨S.left_mem,xu⟩)
        (show S.right ∈ shoreContacts G A x from ⟨S.right_mem,xz⟩) S.lr)
    have choice := contact_clique_on_one_side_of_singleton budget offA offB boundA apart xd hr rA rB
    have cl := choice.resolve_left deny
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    by_contra different
    obtain ⟨ha,xa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,xb⟩ := Finset.mem_filter.mp hb
    exact C.independent _ ha _ hb
      (cl (show a ∈ shoreContacts G B x from ⟨ClawShore.leaf_mem C ha,xa⟩)
        (show b ∈ shoreContacts G B x from ⟨ClawShore.leaf_mem C hb,xb⟩) different)
  let U := C.leaves.filter (G.Adj p)
  let W := C.leaves.filter (G.Adj q)
  have cU : U.card ≤ 1 := cap p (by simp) pu pz
  have cW : W.card ≤ 1 := cap q (by simp) qu qz
  have sub : C.leaves ⊆ U ∪ W := by
    intro v hv
    by_cases pv : G.Adj p v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,pv⟩)
    have two := at_least_two_ports_of_shore_endpoint conn boundB
      (ClawShore.leaf_mem C hv) (ClawShore.leaf_only C hv)
    have frame : ({q,t,p} : Finset V) = {p,q,t} := by
      ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
    have qv := (two_present_ports qt (by simpa only [frame] using two) pv).1
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,qv⟩)
  have lower := Finset.card_le_card sub
  have upper := Finset.card_union_le U W
  rw [C.three] at lower
  omega

theorem traceable_of_clique_and_claw_with_singleton (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (hr : CutSingleton G D r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r)
    (clique : A.Pairwise G.Adj) (large : 3 ≤ Nat.card A) : Traceable G := by
  obtain ⟨q,qd,x,hx,z,hz,xz,qx,qz⟩ := shared_port_of_claw C conn size boundB
  obtain ⟨p,s,ps,pq,sq,frame⟩ := split_other_ports size qd
  subst D
  obtain ⟨f,edges⟩ := shore_distinct_attachments conn size offA boundA large ⟨r,rA,hr.1⟩
  have R := clique_shore_route clique (p := ⟨p,by simp⟩) (q := ⟨s,by simp⟩)
    (fun h => ps (congrArg Subtype.val h)) f edges
  exact traceable_of_claw_and_route_with_shared_port_and_singleton C conn ps pq sq
    offA offB apart hr rA rB cover boundB hx hz xz qx qz R

theorem traceable_of_three_path_and_claw_with_singleton
    (S : ThreeVertexShore G A) (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (hr : CutSingleton G D r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r) : Traceable G := by
  classical
  by_contra no
  obtain ⟨q,qd,x,hx,z,hz,xz,qx,qz⟩ := shared_port_of_claw C conn size boundB
  obtain ⟨p,s,ps,pq,sq,frame⟩ := split_other_ports size qd
  subst D
  have forbidden : ¬ ShoreRoute G A p s := fun R =>
    no (traceable_of_claw_and_route_with_shared_port_and_singleton C conn ps pq sq
      offA offB apart hr rA rB cover boundB hx hz xz qx qz R)
  obtain ⟨shared,pair|pair⟩ := common_ports_of_forbidden_three_path_route S conn pq sq boundA forbidden
  · have perm : ({p,q,s} : Finset V) = {p,s,q} := by
      ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
    exact impossible_claw_next_to_shared_pair_and_singleton S C conn budget sq.symm
      (perm.symm ▸ offA) (perm.symm ▸ offB) (perm.symm ▸ boundA) (perm.symm ▸ boundB)
      apart (perm.symm ▸ hr) rA rB pair.1 pair.2 shared.1 shared.2
  · have perm : ({s,q,p} : Finset V) = {p,s,q} := by
      ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
    exact impossible_claw_next_to_shared_pair_and_singleton S C conn budget pq.symm
      (perm.symm ▸ offA) (perm.symm ▸ offB) (perm.symm ▸ boundA) (perm.symm ▸ boundB)
      apart (perm.symm ▸ hr) rA rB pair.1 pair.2 shared.1 shared.2

/-- The order-eleven split into components of orders three, four, and
one has a spanning path under the induced-tree budget. -/
theorem traceable_of_three_and_four_with_singleton
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (hr : CutSingleton G D r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (nA : Nat.card A = 3) (nB : Nat.card B = 4) : Traceable G := by
  classical
  have other : ∃ v : V, v ∉ B ∧ v ∉ D := ⟨r,rB,hr.1⟩
  rcases clique_or_path_of_three connA nA with clique|path
  · rcases route_or_claw_of_four_shore conn size offB boundB connB nB other with route|claw
    · obtain ⟨p,hp,q,hq,pq,R⟩ := route
      have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ D ∨ v = r := by
        have h := cover v; tauto
      exact traceable_of_route_clique_with_singleton conn size rB rA hr.1
        (fun v hv => (hr.2 v).mpr hv) offB offA boundA apart.symm swap clique (by omega) hp hq pq R
    · obtain ⟨C⟩ := claw
      exact traceable_of_clique_and_claw_with_singleton C conn size offA offB boundA boundB
        apart hr rA rB cover clique (by omega)
  · obtain ⟨S⟩ := path
    rcases route_or_claw_of_four_shore conn size offB boundB connB nB other with route|claw
    · obtain ⟨p,hp,q,hq,pq,R⟩ := route
      exact traceable_of_three_path_and_opposite_route_with_singleton S conn size offA offB
        boundA apart hr rA rB cover hp hq pq R
    · obtain ⟨C⟩ := claw
      exact traceable_of_three_path_and_claw_with_singleton S C conn budget size offA offB
        boundA boundB apart hr rA rB cover

#print axioms traceable_of_clique_and_claw_with_singleton
#print axioms traceable_of_three_path_and_claw_with_singleton
#print axioms traceable_of_three_and_four_with_singleton

end Graffiti199Depleted.Catalogue
