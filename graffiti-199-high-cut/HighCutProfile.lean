import CubicShorePacking

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {D : Finset V} {A : Set V} {r : V}

/-- After omitting a cubic vertex with a neighbor on its own shore, every
spanning path in the deletion uses an edge on that shore from one of its
neighbors to one of its nonneighbors. The two ends occur consecutively. -/
theorem cubic_shore_has_internal_flank
    (cutSize : D.card = 3) (off : ∀ v ∈ D, v ∉ A)
    (boundary : ShoreBoundary G D A) (rA : r ∈ A) (degree : G.degree r = 3)
    (own : ∃ x ∈ A, G.Adj r x)
    (p : PathOn G {x | x ≠ r}) (no : ¬ Traceable G) :
    ∃ i j : Fin p.vertices.length, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      p.vertices.get i ∈ A ∧ G.Adj r (p.vertices.get i) ∧
      p.vertices.get j ∈ A ∧ ¬ G.Adj r (p.vertices.get j) := by
  classical
  by_contra! absent
  let N := G.neighborFinset r
  let U := N.filter (fun x => x ∈ A)
  let P := N.filter (fun x => x ∈ D)
  let T := D \ N
  have ncard : N.card = 3 := by rw [G.card_neighborFinset_eq_degree,degree]
  have split : N.filter (fun x => x ∉ A) = P := by
    ext x
    change x ∈ N.filter (fun x => x ∉ A) ↔ _
    simp only [P,Finset.mem_filter]
    exact ⟨fun h => ⟨h.1,boundary _ rA _ h.2 ((G.mem_neighborFinset _ _).mp h.1)⟩,
      fun h => ⟨h.1,off _ h.2⟩⟩
  have total : U.card + P.card = 3 := by
    change (N.filter (fun x => x ∈ A)).card + P.card = 3
    rw [← split,Finset.filter_card_add_filter_neg_card_eq_card,ncard]
  have diff : T = D \ P := by
    ext x
    simp only [T,P,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have sub : P ⊆ D := fun _ h => (Finset.mem_filter.mp h).2
  have pt : T.card + P.card = 3 := by
    rw [diff,Finset.card_sdiff_add_card_eq_card sub,cutSize]
  have all (v : V) (hv : v ∈ U) : v ∈ p.vertices := by
    apply (p.covers v).mpr
    exact ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hv).1).ne.symm
  have ne : U.Nonempty := by
    obtain ⟨x,xA,rx⟩ := own
    exact ⟨x,Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr rx,xA⟩⟩
  have flank (i : Fin p.vertices.length) (hi : p.vertices.get i ∈ U) :
      (∃ j : Fin p.vertices.length, j.val + 1 = i.val ∧ p.vertices.get j ∈ T) ∧
      (∃ j : Fin p.vertices.length, i.val + 1 = j.val ∧ p.vertices.get j ∈ T) := by
    obtain ⟨iN,iA⟩ := Finset.mem_filter.mp hi
    have ri := (G.mem_neighborFinset _ _).mp iN
    have force (j : Fin p.vertices.length) (pos : i.val+1 = j.val ∨ j.val+1 = i.val)
        (ij : G.Adj (p.vertices.get i) (p.vertices.get j))
        (rj : ¬ G.Adj r (p.vertices.get j)) : p.vertices.get j ∈ T := by
      have outside : p.vertices.get j ∉ A := fun jA => rj (absent i j pos iA ri jA)
      exact Finset.mem_sdiff.mpr ⟨boundary _ iA _ outside ij,fun h => rj ((G.mem_neighborFinset _ _).mp h)⟩
    obtain ⟨⟨j,before,ij,rj⟩,⟨k,after,ik,rk⟩⟩ := path_flanks_of_nontraceable p no i ri
    exact ⟨⟨j,before,force j (Or.inr before) ij rj⟩,⟨k,after,force k (Or.inl after) ik rk⟩⟩
  have strict := card_lt_of_path_flanks p.nodup all ne (fun i hi => (flank i hi).1)
    (fun i hi => (flank i hi).2)
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem neighbor_on_connected_shore (connected : (G.induce A).Connected)
    (large : 2 ≤ Nat.card A) (rA : r ∈ A) : ∃ x ∈ A, G.Adj r x := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card] at large
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let a : A := ⟨r,rA⟩
  obtain ⟨b,ne⟩ := exists_ne a
  obtain ⟨w⟩ := connected.preconnected a b
  have start {x y : A} (w : (G.induce A).Walk x y) (different : x ≠ y) :
      ∃ z : A, (G.induce A).Adj x z := by
    cases w with
    | nil => exact (different rfl).elim
    | cons edge _ => exact ⟨_,edge⟩
  obtain ⟨z,hz⟩ := start w ne.symm
  exact ⟨z,z.property,hz⟩

/-- A cubic vertex in any nonsingleton component of a three-vertex
deletion must have a nonneighbor in that same component. -/
theorem nonneighbor_on_cubic_shore
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (cutSize : D.card = 3) (C : (DeletionGraph G D).ConnectedComponent)
    (large : 2 ≤ Nat.card (componentShore D C))
    (rA : r ∈ componentShore D C) (degree : G.degree r = 3) :
    ∃ x ∈ componentShore D C, x ≠ r ∧ ¬ G.Adj r x := by
  obtain ⟨p⟩ := pathOn_of_traceable_delete
    (traceable_after_cubic_delete smaller conn budget order no ind degree)
  have own := neighbor_on_connected_shore (componentShore_connected D C) large rA
  obtain ⟨_,j,_,_,_,jA,rj⟩ := cubic_shore_has_internal_flank cutSize
    (componentShore_off_cut D C) (componentShore_boundary D C) rA degree own p no
  exact ⟨p.vertices.get j,jA,(p.covers _).mp (List.get_mem _ _),rj⟩

/-- In the remaining crossing failure, each nonsingleton clique
component, as well as the cut itself, consists exclusively of vertices
of degree at least four. -/
theorem high_cut_and_clique_shores_of_crossing_failure
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) :
    ∃ F : LargeCrossingFailure G, (∀ v ∈ F.cut, 4 ≤ G.degree v) ∧
      ∀ C : (DeletionGraph G F.cut).ConnectedComponent,
        2 ≤ Nat.card (componentShore F.cut C) → (componentShore F.cut C).Pairwise G.Adj →
        ∀ v ∈ componentShore F.cut C, 4 ≤ G.degree v := by
  obtain ⟨F,cutHigh⟩ := high_cut_of_crossing_failure_of_independent_cubics
    smaller conn budget order no ind fail
  refine ⟨F,cutHigh,?_⟩
  intro C large clique v vA
  have low := degree_of_small_deletion_preconnected (G := G) (by omega : 4 ≤ Fintype.card V)
    (fun D h => (conn.2 D h).preconnected) v
  have ne : G.degree v ≠ 3 := by
    intro degree
    obtain ⟨x,xA,xv,noEdge⟩ := nonneighbor_on_cubic_shore smaller conn budget order no ind
      F.size C large vA degree
    exact noEdge (clique vA xA xv.symm)
  omega

#print axioms cubic_shore_has_internal_flank
#print axioms nonneighbor_on_cubic_shore
#print axioms high_cut_and_clique_shores_of_crossing_failure

end Graffiti199Depleted.Catalogue
