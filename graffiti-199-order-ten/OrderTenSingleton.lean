import OrderTenTwoShores

open private clique_or_path_of_three from CrossingOrder
open private exists_third_port from ThreePathWithRoute
open private ThreeVertexShore.reversed ThreeVertexShore.traverses
  ThreeVertexShore.left_two ThreeVertexShore.right_two ThreeVertexShore.route_from
  two_present_ports from TwoShortShores
open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private shore_anticomplete from CubicPortThreeShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V} {r : V}

omit [Fintype V] [DecidableRel G.Adj] in
private theorem splice_shores_with_singleton {p q s : V}
    (pq : p ≠ q) (ps : p ≠ s) (qs : q ≠ s)
    (rA : r ∉ A) (rB : r ∉ B) (rD : r ∉ ({p,q,s} : Finset V)) (rp : G.Adj r p)
    (offA : ∀ v ∈ ({p,q,s} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,s} : Finset V), v ∉ B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,s} : Finset V) ∨ v = r)
    (first : ShoreRoute G A p q) (second : ShoreRoute G B q s) : Traceable G := by
  obtain ⟨a,a',pa,aq,P⟩ := first
  obtain ⟨b,b',qb,bs,Q⟩ := second
  have h₀ : Disjoint ({r} : Set V) {p} := by
    apply Set.disjoint_left.mpr
    intro v hr hp
    have e : r = p := (show v = r from hr).symm.trans (show v = p from hp)
    exact rD (by simp [e])
  have h₁ : Disjoint (({r} : Set V) ∪ {p}) A := by
    apply Set.disjoint_left.mpr
    rintro v (hr|hp) va
    · exact rA ((show v = r from hr) ▸ va)
    · exact offA p (by simp) ((show v = p from hp) ▸ va)
  have h₂ : Disjoint ((({r} : Set V) ∪ {p}) ∪ A) {q} := by
    apply Set.disjoint_left.mpr
    rintro v ((hr|hp)|va) hq
    · have e : r = q := (show v = r from hr).symm.trans (show v = q from hq)
      exact rD (by simp [e])
    · exact pq ((show v = p from hp).symm.trans (show v = q from hq))
    · exact offA q (by simp) ((show v = q from hq) ▸ va)
  have h₃ : Disjoint (((({r} : Set V) ∪ {p}) ∪ A) ∪ {q}) B := by
    apply Set.disjoint_left.mpr
    rintro v (((hr|hp)|va)|hq) vb
    · exact rB ((show v = r from hr) ▸ vb)
    · exact offB p (by simp) ((show v = p from hp) ▸ vb)
    · exact Set.disjoint_left.mp apart va vb
    · exact offB q (by simp) ((show v = q from hq) ▸ vb)
  have h₄ : Disjoint ((((({r} : Set V) ∪ {p}) ∪ A) ∪ {q}) ∪ B) {s} := by
    apply Set.disjoint_left.mpr
    rintro v ((((hr|hp)|va)|hq)|vb) hs
    · have e : r = s := (show v = r from hr).symm.trans (show v = s from hs)
      exact rD (by simp [e])
    · exact ps ((show v = p from hp).symm.trans (show v = s from hs))
    · exact offA s (by simp) ((show v = s from hs) ▸ va)
    · exact qs ((show v = q from hq).symm.trans (show v = s from hs))
    · exact offB s (by simp) ((show v = s from hs) ▸ vb)
  have full : (((((({r} : Set V) ∪ {p}) ∪ A) ∪ {q}) ∪ B) ∪ {s}) = Set.univ := by
    ext v
    have h := cover v
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    tauto
  have j₀ := (Traverses.single (G := G) r).join (Traverses.single p) h₀ rp
  have j₁ := j₀.join P h₁ pa
  have j₂ := j₁.join (Traverses.single q) h₂ aq
  have j₃ := j₂.join Q h₃ qb
  have joined := j₃.join (Traverses.single s) h₄ bs
  rw [full] at joined
  obtain ⟨R,_,_⟩ := joined
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨R⟩)

private theorem no_third_port_of_two_paths_with_singleton {p q s : V}
    (conn : ConnectivityAtLeast G 3) (no : ¬ Traceable G)
    (pq : p ≠ q) (ps : p ≠ s) (qs : q ≠ s)
    (rA : r ∉ A) (rB : r ∉ B) (rD : r ∉ ({p,q,s} : Finset V))
    (rp : G.Adj r p) (rq : G.Adj r q)
    (offA : ∀ v ∈ ({p,q,s} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,s} : Finset V), v ∉ B)
    (boundB : ShoreBoundary G {p,q,s} B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,s} : Finset V) ∨ v = r)
    (R : ShoreRoute G A p q) (Q : ThreeVertexShore G B) : ¬ G.Adj s Q.left := by
  intro edge
  obtain ⟨t,tD,ts,RT⟩ := ThreeVertexShore.route_from Q conn boundB edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at tD
  rcases tD with eq|eq|eq
  · subst t
    have swap : ({q,p,s} : Finset V) = {p,q,s} := Finset.insert_comm _ _ _
    exact no (splice_shores_with_singleton pq.symm qs ps rA rB (swap.symm ▸ rD) rq
      (swap.symm ▸ offA) (swap.symm ▸ offB) apart (swap.symm ▸ cover) R.reverse RT)
  · subst t
    exact no (splice_shores_with_singleton pq ps qs rA rB rD rp offA offB apart cover R RT)
  · exact ts eq

private theorem traceable_of_two_paths_with_singleton (P : ThreeVertexShore G A)
    (Q : ThreeVertexShore G B) (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (size : D.card = 3) (rA : r ∉ A) (rB : r ∉ B) (rD : r ∉ D)
    (rPorts : ∀ v ∈ D, G.Adj r v)
    (rNoA : ∀ v ∈ A, ¬ G.Adj r v) (rNoB : ∀ v ∈ B, ¬ G.Adj r v)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r) :
    Traceable G := by
  classical
  by_contra no
  obtain ⟨p,hp,q,hq,pq,routeA⟩ := three_vertex_path_shore_route conn boundA P.shape P.lm P.mr P.lr P.noLR
  obtain ⟨s,ps,qs,frame⟩ := exists_third_port size hp hq pq
  subst D
  have rp := rPorts p hp
  have rq := rPorts q hq
  have forbidB := no_third_port_of_two_paths_with_singleton conn no pq ps qs rA rB rD rp rq offA offB
    boundB apart cover routeA
  have bl := two_present_ports pq (ThreeVertexShore.left_two Q conn boundB) (forbidB Q)
  have br := two_present_ports pq (ThreeVertexShore.right_two Q conn boundB) (forbidB (ThreeVertexShore.reversed Q))
  have routeB : ShoreRoute G B p q := ⟨Q.left,Q.right,bl.1,br.2.symm,ThreeVertexShore.traverses Q⟩
  have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ ({p,q,s} : Finset V) ∨ v = r := by
    have h := cover v
    tauto
  have forbidA := no_third_port_of_two_paths_with_singleton conn no pq ps qs rB rA rD rp rq offB offA
    boundA apart.symm swap routeB
  have al := two_present_ports pq (ThreeVertexShore.left_two P conn boundA) (forbidA P)
  have ar := two_present_ports pq (ThreeVertexShore.right_two P conn boundA) (forbidA (ThreeVertexShore.reversed P))
  let L := [r,P.left,P.right,Q.left,Q.right]
  have distinct : L.Nodup := by
    have ne (v : V) (h : v ∈ A) : r ≠ v := fun e => rA (e.symm ▸ h)
    have ne' (v : V) (h : v ∈ B) : r ≠ v := fun e => rB (e.symm ▸ h)
    have cross (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) : x ≠ y :=
      fun e => Set.disjoint_left.mp apart hx (e.symm ▸ hy)
    simp [L,ne _ P.left_mem,ne _ P.right_mem,ne' _ Q.left_mem,ne' _ Q.right_mem,P.lr,Q.lr,
      cross _ P.left_mem _ Q.left_mem,cross _ P.left_mem _ Q.right_mem,
      cross _ P.right_mem _ Q.left_mem,cross _ P.right_mem _ Q.right_mem]
  have indep (x : V) (hx : x ∈ L.toFinset) (y : V) (hy : y ∈ L.toFinset) : ¬ G.Adj x y := by
    have cross {v w : V} (hv : v ∈ A) (hw : w ∈ B) : ¬ G.Adj v w :=
      shore_anticomplete offB boundA apart hv hw
    simp only [L,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with e|e|e|e|e <;> subst x <;> rcases hy with e|e|e|e|e <;> subst y <;>
      simp [rNoA _ P.left_mem,rNoA _ P.right_mem,rNoB _ Q.left_mem,rNoB _ Q.right_mem,
        G.adj_comm P.left r,G.adj_comm P.right r,G.adj_comm Q.left r,G.adj_comm Q.right r,
        P.noLR,G.adj_comm P.right P.left,Q.noLR,G.adj_comm Q.right Q.left,
        cross P.left_mem Q.left_mem,cross P.left_mem Q.right_mem,
        cross P.right_mem Q.left_mem,cross P.right_mem Q.right_mem,
        G.adj_comm Q.left P.left,G.adj_comm Q.right P.left,
        G.adj_comm Q.left P.right,G.adj_comm Q.right P.right]
  have contacts (x : V) (hx : x ∈ L.toFinset) : G.Adj p x := by
    simp only [L,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with e|e|e|e|e <;> subst x
    · exact rp.symm
    · exact al.1
    · exact ar.1
    · exact bl.1
    · exact br.1
  have card : 5 ≤ L.toFinset.card := by rw [List.toFinset_card_of_nodup distinct]; simp [L]
  have six := six_le_treeNumber_of_five_independent_neighbors L.toFinset p card contacts indep
  omega

omit [DecidableRel G.Adj] in
private theorem traceable_of_route_clique_with_singleton
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (rA : r ∉ A) (rB : r ∉ B) (rD : r ∉ D) (rPorts : ∀ v ∈ D, G.Adj r v)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundB : ShoreBoundary G D B) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r)
    (cl : B.Pairwise G.Adj) (largeB : 3 ≤ Nat.card B)
    {p q : V} (pD : p ∈ D) (qD : q ∈ D) (pq : p ≠ q) (R : ShoreRoute G A p q) : Traceable G := by
  obtain ⟨s,ps,qs,frame⟩ := exists_third_port size pD qD pq
  subst D
  obtain ⟨f,ff⟩ := shore_distinct_attachments conn size offB boundB largeB ⟨r,rB,rD⟩
  have Q := clique_shore_route cl (p := ⟨q,qD⟩) (q := ⟨s,by simp⟩)
    (fun h => qs (congrArg Subtype.val h)) f ff
  exact splice_shores_with_singleton pq ps qs rA rB rD (rPorts _ pD) offA offB apart cover R Q

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem any_route_of_three_clique
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (rA : r ∉ A) (rD : r ∉ D) (offA : ∀ v ∈ D, v ∉ A) (boundA : ShoreBoundary G D A)
    (cl : A.Pairwise G.Adj) (largeA : 3 ≤ Nat.card A) :
    ∃ p ∈ D, ∃ q ∈ D, p ≠ q ∧ ShoreRoute G A p q := by
  obtain ⟨f,ff⟩ := shore_distinct_attachments conn size offA boundA largeA ⟨r,rA,rD⟩
  obtain ⟨p,pD⟩ : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,qD,qp⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < D.card) p
  exact ⟨p,pD,q,qD,qp.symm,clique_shore_route cl (p := ⟨p,pD⟩) (q := ⟨q,qD⟩)
    (fun h => qp (congrArg Subtype.val h).symm) f ff⟩

/-- Two order-three components and a singleton can be joined through a
three-cut. If the two path components offer only the same terminal
pair, the singleton is the fifth leaf of a forbidden induced star. -/
theorem traceable_of_two_three_shores_and_singleton
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (rA : r ∉ A) (rB : r ∉ B) (rD : r ∉ D)
    (rPorts : ∀ v ∈ D, G.Adj r v)
    (rNoA : ∀ v ∈ A, ¬ G.Adj r v) (rNoB : ∀ v ∈ B, ¬ G.Adj r v)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (nA : Nat.card A = 3) (nB : Nat.card B = 3) : Traceable G := by
  classical
  rcases clique_or_path_of_three connA nA with clA|pA
  · have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ D ∨ v = r := by
      have h := cover v
      tauto
    have possible : ∃ p ∈ D, ∃ q ∈ D, p ≠ q ∧ ShoreRoute G B p q := by
      rcases clique_or_path_of_three connB nB with clB|pB
      · exact any_route_of_three_clique conn size rB rD offB boundB clB (by omega)
      · obtain ⟨Q⟩ := pB
        exact three_vertex_path_shore_route conn boundB Q.shape Q.lm Q.mr Q.lr Q.noLR
    obtain ⟨p,hp,q,hq,pq,R⟩ := possible
    exact traceable_of_route_clique_with_singleton conn size rB rA rD rPorts offB offA boundA
      apart.symm swap clA (by omega) hp hq pq R
  · obtain ⟨P⟩ := pA
    rcases clique_or_path_of_three connB nB with clB|pB
    · obtain ⟨p,hp,q,hq,pq,R⟩ := three_vertex_path_shore_route conn boundA P.shape P.lm P.mr P.lr P.noLR
      exact traceable_of_route_clique_with_singleton conn size rA rB rD rPorts offA offB boundB
        apart cover clB (by omega) hp hq pq R
    · obtain ⟨Q⟩ := pB
      exact traceable_of_two_paths_with_singleton P Q conn budget size rA rB rD rPorts
        rNoA rNoB offA offB boundA boundB apart cover

#print axioms traceable_of_two_three_shores_and_singleton

end Graffiti199Depleted.Catalogue
