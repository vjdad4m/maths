import ShoreRouting

open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private shore_anticomplete from CubicPortThreeShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable {D : Finset V} {A B : Set V}

/-- The vertices and edges of an induced three-vertex path on a shore. -/
structure ThreeVertexShore (G : SimpleGraph V) (A : Set V) where
  left : V
  middle : V
  right : V
  shape : A = {left,middle,right}
  lm : G.Adj left middle
  mr : G.Adj middle right
  lr : left ≠ right
  noLR : ¬ G.Adj left right

namespace ThreeVertexShore

omit [Fintype V] [DecidableRel G.Adj] in
theorem left_mem (H : ThreeVertexShore G A) : H.left ∈ A :=
  Eq.mpr (congrArg (fun S : Set V => H.left ∈ S) H.shape) (by simp)

omit [Fintype V] [DecidableRel G.Adj] in
theorem right_mem (H : ThreeVertexShore G A) : H.right ∈ A :=
  Eq.mpr (congrArg (fun S : Set V => H.right ∈ S) H.shape) (by simp)

omit [Fintype V] [DecidableRel G.Adj] in
private def reversed (H : ThreeVertexShore G A) : ThreeVertexShore G A :=
  ⟨H.right,H.middle,H.left,H.shape.trans (by ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto),
    H.mr.symm,H.lm.symm,H.lr.symm,fun e => H.noLR e.symm⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem traverses (H : ThreeVertexShore G A) : Traverses G A H.left H.right := by
  let p : PathOn G A :=
    ⟨[H.left,H.middle,H.right],by simp,
      List.chain'_cons.mpr ⟨H.lm,List.chain'_pair.mpr H.mr⟩,
      by simp [H.lm.ne,H.mr.ne,H.lr],fun v => by simp [H.shape]⟩
  exact ⟨p,rfl,rfl⟩

private theorem left_two (H : ThreeVertexShore G A) (conn : ConnectivityAtLeast G 3)
    (boundary : ShoreBoundary G D A) : 2 ≤ (D.filter (G.Adj H.left)).card := by
  apply at_least_two_ports_of_shore_endpoint conn boundary H.left_mem (w := H.middle)
  intro x xA ex
  rw [H.shape] at xA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at xA
  rcases xA with rfl|rfl|rfl
  · exact (G.loopless _ ex).elim
  · rfl
  · exact (H.noLR ex).elim

private theorem right_two (H : ThreeVertexShore G A) (conn : ConnectivityAtLeast G 3)
    (boundary : ShoreBoundary G D A) : 2 ≤ (D.filter (G.Adj H.right)).card :=
  H.reversed.left_two conn boundary

private theorem route_from (H : ThreeVertexShore G A) (conn : ConnectivityAtLeast G 3)
    (boundary : ShoreBoundary G D A) {r : V} (edge : G.Adj r H.left) :
    ∃ s ∈ D, s ≠ r ∧ ShoreRoute G A s r := by
  obtain ⟨s,hs,ne⟩ := Finset.exists_ne_of_one_lt_card
    (lt_of_lt_of_le (by decide : 1 < 2) (H.right_two conn boundary)) r
  obtain ⟨sD,edgeS⟩ := Finset.mem_filter.mp hs
  exact ⟨s,sD,ne,H.right,H.left,edgeS.symm,edge.symm,H.traverses.reverse⟩

end ThreeVertexShore

private theorem no_third_port_at_path_endpoint [DecidableEq V]
    (conn : ConnectivityAtLeast G 3) (no : ¬ Traceable G)
    {p q r : V} (pq : p ≠ q) (pr : p ≠ r) (qr : q ≠ r)
    (offA : ∀ v ∈ ({p,q,r} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,r} : Finset V), v ∉ B)
    (boundaryB : ShoreBoundary G {p,q,r} B)
    (disjoint : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,r} : Finset V))
    (route : ShoreRoute G A p q) (H : ThreeVertexShore G B) : ¬ G.Adj r H.left := by
  intro edge
  obtain ⟨s,hs,ne,route₂⟩ := H.route_from conn boundaryB edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with eq|eq|eq
  · subst s
    have same : ({q,p,r} : Finset V) = {p,q,r} := Finset.insert_comm _ _ _
    exact no (traceable_of_compatible_shore_routes pq.symm qr pr
      (same.symm ▸ offA) (same.symm ▸ offB) disjoint
      (same.symm ▸ cover) route.reverse route₂)
  · subst s
    exact no (traceable_of_compatible_shore_routes pq pr qr offA offB disjoint cover route route₂)
  · exact ne eq

omit [Fintype V] in
private theorem two_present_ports [DecidableEq V] {p q r v : V} (pq : p ≠ q)
    (two : 2 ≤ (({p,q,r} : Finset V).filter (G.Adj v)).card) (noR : ¬ G.Adj r v) :
    G.Adj p v ∧ G.Adj q v := by
  have sub : ({p,q,r} : Finset V).filter (G.Adj v) ⊆ {p,q} := by
    intro x hx
    obtain ⟨hx,edge⟩ := Finset.mem_filter.mp hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
    exact hx.imp_right (fun h => h.resolve_right (fun eq => noR (eq ▸ edge.symm)))
  have eq : ({p,q,r} : Finset V).filter (G.Adj v) = {p,q} :=
    Finset.eq_of_subset_of_card_le sub (by rw [Finset.card_pair pq]; exact two)
  have hp : p ∈ ({p,q,r} : Finset V).filter (G.Adj v) := by rw [eq]; simp
  have hq : q ∈ ({p,q,r} : Finset V).filter (G.Adj v) := by rw [eq]; simp
  exact ⟨(Finset.mem_filter.mp hp).2.symm,(Finset.mem_filter.mp hq).2.symm⟩

/-- If deletion of three vertices leaves precisely two induced three-vertex
paths, the graph has a Hamiltonian path under the induced-tree budget.
If the two routes cannot be made compatible, the third port and the four
path endpoints form an independent five-set with a common neighbor. -/
theorem traceable_of_two_three_vertex_path_shores
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (P : ThreeVertexShore G A) (Q : ThreeVertexShore G B) : Traceable G := by
  classical
  by_contra no
  obtain ⟨p,pD,q,qD,pq,route⟩ := three_vertex_path_shore_route conn boundA P.shape P.lm P.mr P.lr P.noLR
  obtain ⟨r,rD,rOff⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show ({p,q} : Finset V).card < D.card by rw [Finset.card_pair pq,size]; decide)
  have pr : p ≠ r := fun e => rOff (by simp [← e])
  have qr : q ≠ r := fun e => rOff (by simp [← e])
  have ports : D = {p,q,r} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl
      · exact pD
      · exact qD
      · exact rD
    · rw [size,Finset.card_insert_of_not_mem (by simp [pq,pr]),Finset.card_pair qr]
  subst D
  have nonBleft := no_third_port_at_path_endpoint conn no pq pr qr offA offB boundB apart cover route Q
  have nonBright : ¬ G.Adj r Q.right :=
    no_third_port_at_path_endpoint conn no pq pr qr offA offB boundB apart cover route Q.reversed
  have bL := two_present_ports pq (Q.left_two conn boundB) nonBleft
  have bR := two_present_ports pq (Q.right_two conn boundB) nonBright
  have routeB : ShoreRoute G B p q := ⟨Q.left,Q.right,bL.1,bR.2.symm,Q.traverses⟩
  have cover' (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ ({p,q,r} : Finset V) := by
    have h := cover v
    tauto
  have nonAleft := no_third_port_at_path_endpoint conn no pq pr qr offB offA boundA apart.symm cover' routeB P
  have nonAright : ¬ G.Adj r P.right :=
    no_third_port_at_path_endpoint conn no pq pr qr offB offA boundA apart.symm cover' routeB P.reversed
  have aL := two_present_ports pq (P.left_two conn boundA) nonAleft
  have aR := two_present_ports pq (P.right_two conn boundA) nonAright
  have adj : G.Adj r p ∨ G.Adj r q := by
    by_contra bad
    have bp : ¬ G.Adj r p := fun e => bad (Or.inl e)
    have bq : ¬ G.Adj r q := fun e => bad (Or.inr e)
    have sub : G.neighborFinset r ⊆ {P.middle,Q.middle} := by
      intro v hv
      have rv := (G.mem_neighborFinset _ _).mp hv
      rcases cover v with vA|vB|vD
      · rw [P.shape] at vA
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at vA
        rcases vA with eq|eq|eq
        · exact (nonAleft (eq ▸ rv)).elim
        · simp [eq]
        · exact (nonAright (eq ▸ rv)).elim
      · rw [Q.shape] at vB
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at vB
        rcases vB with eq|eq|eq
        · exact (nonBleft (eq ▸ rv)).elim
        · simp [eq]
        · exact (nonBright (eq ▸ rv)).elim
      · simp only [Finset.mem_insert,Finset.mem_singleton] at vD
        rcases vD with eq|eq|eq
        · exact (bp (eq ▸ rv)).elim
        · exact (bq (eq ▸ rv)).elim
        · exact (G.loopless r (eq ▸ rv)).elim
    have up := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at up
    have bound : ({P.middle,Q.middle} : Finset V).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le P.middle ({Q.middle} : Finset V)
    have low := degree_of_small_deletion_preconnected (G := G)
      (by have n := conn.1; omega : 4 ≤ Fintype.card V)
      (fun R hR => (conn.2 R hR).preconnected) r
    omega
  have rA : r ∉ A := offA r (by simp)
  have rB : r ∉ B := offB r (by simp)
  have dis := Set.disjoint_left.mp apart
  have cross {x y : V} (hx : x ∈ A) (hy : y ∈ B) : ¬ G.Adj x y :=
    shore_anticomplete offB boundA apart hx hy
  let L := [r,P.left,P.right,Q.left,Q.right]
  have distinct : L.Nodup := by
    have ne (v : V) (vA : v ∈ A) : r ≠ v := fun e => rA (e.symm ▸ vA)
    have ne' (v : V) (vB : v ∈ B) : r ≠ v := fun e => rB (e.symm ▸ vB)
    have apart' (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) : x ≠ y :=
      fun e => dis hx (e.symm ▸ hy)
    simp [L,ne _ P.left_mem,ne _ P.right_mem,ne' _ Q.left_mem,ne' _ Q.right_mem,
      P.lr,Q.lr,apart' _ P.left_mem _ Q.left_mem,apart' _ P.left_mem _ Q.right_mem,
      apart' _ P.right_mem _ Q.left_mem,apart' _ P.right_mem _ Q.right_mem]
  have independent (x : V) (hx : x ∈ L.toFinset) (y : V) (hy : y ∈ L.toFinset) : ¬ G.Adj x y := by
    simp only [L,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with e|e|e|e|e <;> subst x <;> rcases hy with e|e|e|e|e <;> subst y <;>
      simp [nonAleft,nonAright,nonBleft,nonBright,
        G.adj_comm P.left r,G.adj_comm P.right r,G.adj_comm Q.left r,G.adj_comm Q.right r,
        P.noLR,G.adj_comm P.right P.left,Q.noLR,G.adj_comm Q.right Q.left,
        cross P.left_mem Q.left_mem,cross P.left_mem Q.right_mem,
        cross P.right_mem Q.left_mem,cross P.right_mem Q.right_mem,
        G.adj_comm Q.left P.left,G.adj_comm Q.right P.left,
        G.adj_comm Q.left P.right,G.adj_comm Q.right P.right]
  have cardinal : 5 ≤ L.toFinset.card := by rw [List.toFinset_card_of_nodup distinct]; simp [L]
  have forbidden (c : V) (cr : G.Adj c r) (ca : G.Adj c P.left) (ca' : G.Adj c P.right)
      (cb : G.Adj c Q.left) (cb' : G.Adj c Q.right) : False := by
    have edges (x : V) (hx : x ∈ L.toFinset) : G.Adj c x := by
      simp only [L,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> assumption
    have large := six_le_treeNumber_of_five_independent_neighbors L.toFinset c cardinal edges independent
    omega
  rcases adj with rp|rq
  · exact forbidden p rp.symm aL.1 aR.1 bL.1 bR.1
  · exact forbidden q rq.symm aL.2 aR.2 bL.2 bR.2

#print axioms traceable_of_two_three_vertex_path_shores

end Graffiti199Depleted.Catalogue
