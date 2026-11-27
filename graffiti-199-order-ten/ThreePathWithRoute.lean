import FourShoreRouting

open private no_third_port_at_path_endpoint two_present_ports from TwoShortShores
open private ThreeVertexShore.reversed ThreeVertexShore.traverses
  ThreeVertexShore.left_two ThreeVertexShore.right_two from TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- If a three-vertex path cannot use a prescribed pair, its endpoints
have the same two ports and both see the third port. -/
theorem common_ports_of_forbidden_three_path_route (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) {p q s : V}
    (ps : p ≠ s) (qs : q ≠ s)
    (boundary : ShoreBoundary G {p,q,s} A) (no : ¬ ShoreRoute G A p q) :
    (G.Adj s S.left ∧ G.Adj s S.right) ∧
      ((G.Adj p S.left ∧ G.Adj p S.right) ∨ (G.Adj q S.left ∧ G.Adj q S.right)) := by
  classical
  have twoL := ThreeVertexShore.left_two S conn boundary
  have twoR := ThreeVertexShore.right_two S conn boundary
  have nonPair (left : G.Adj p S.left) (right : G.Adj q S.right) : False :=
    no ⟨S.left,S.right,left,right.symm,ThreeVertexShore.traverses S⟩
  have nonReverse (left : G.Adj q S.left) (right : G.Adj p S.right) : False :=
    no ⟨S.right,S.left,right,left.symm,(ThreeVertexShore.traverses S).reverse⟩
  have withoutQ (v : V) (two : 2 ≤ (({p,q,s} : Finset V).filter (G.Adj v)).card)
      (nq : ¬ G.Adj q v) : G.Adj p v ∧ G.Adj s v := by
    apply two_present_ports ps _ nq
    have eq : ({p,s,q} : Finset V) = {p,q,s} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    simpa only [eq] using two
  have withoutP (v : V) (two : 2 ≤ (({p,q,s} : Finset V).filter (G.Adj v)).card)
      (np : ¬ G.Adj p v) : G.Adj q v ∧ G.Adj s v := by
    apply two_present_ports qs _ np
    have eq : ({q,s,p} : Finset V) = {p,q,s} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    simpa only [eq] using two
  by_cases leftP : G.Adj p S.left
  · have right := withoutQ _ twoR (nonPair leftP)
    have left := withoutQ _ twoL (fun h => nonReverse h right.1)
    exact ⟨⟨left.2,right.2⟩,Or.inl ⟨left.1,right.1⟩⟩
  · have left := withoutP _ twoL leftP
    have right := withoutP _ twoR (nonReverse left.1)
    exact ⟨⟨left.2,right.2⟩,Or.inr ⟨left.1,right.1⟩⟩

omit [DecidableRel G.Adj] [Fintype V] in
private theorem exists_third_port (size : D.card = 3) {p q : V} (hp : p ∈ D) (hq : q ∈ D)
    (pq : p ≠ q) : ∃ s : V, p ≠ s ∧ q ≠ s ∧ D = {p,q,s} := by
  have lt : ({p,q} : Finset V).card < D.card := by rw [Finset.card_pair pq,size]; decide
  obtain ⟨s,hs,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card lt
  have ps : p ≠ s := fun eq => off (by simp [← eq])
  have qs : q ≠ s := fun eq => off (by simp [← eq])
  refine ⟨s,ps,qs,(Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact hp
    · exact hq
    · exact hs
  · rw [size,Finset.card_insert_of_not_mem (by simp [pq,ps]),Finset.card_pair qs]

/-- A three-vertex path component can use every spanning route of the
other side, allowing the path component to be split when needed. -/
theorem traceable_of_three_vertex_path_and_opposite_route (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundary : ShoreBoundary G D A) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    {p q : V} (hp : p ∈ D) (hq : q ∈ D) (pq : p ≠ q) (route : ShoreRoute G B p q) :
    Traceable G := by
  classical
  by_contra no
  obtain ⟨s,ps,qs,frame⟩ := exists_third_port (D := D) size hp hq pq
  subst D
  have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ ({p,q,s} : Finset V) := by
    have h := cover v
    tauto
  have sl := no_third_port_at_path_endpoint conn no pq ps qs offB offA boundary
    apart.symm swap route S
  have sr : ¬ G.Adj s S.right :=
    no_third_port_at_path_endpoint conn no pq ps qs offB offA boundary apart.symm swap route (ThreeVertexShore.reversed S)
  have left := two_present_ports pq (ThreeVertexShore.left_two S conn boundary) sl
  have right := two_present_ports pq (ThreeVertexShore.right_two S conn boundary) sr
  obtain ⟨y,hy,sy⟩ := contact_of_shore conn (by omega) offA boundary
    ⟨S.left,S.left_mem⟩ (p := s) (by simp)
  have h : y ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  have middle : G.Adj s S.middle := by
    rcases h with e|e|e
    · exact (sl (e ▸ sy)).elim
    · exact e ▸ sy
    · exact (sr (e ▸ sy)).elim
  exact no (traceable_of_twin_path_shore_and_route S pq ps qs offA offB apart cover
    left.1 left.2 right.1 right.2 middle hp hq pq route)

#print axioms common_ports_of_forbidden_three_path_route
#print axioms traceable_of_three_vertex_path_and_opposite_route

end Graffiti199Depleted.Catalogue
