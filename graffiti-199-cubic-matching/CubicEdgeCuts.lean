import TreeBudget

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

noncomputable def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V := by
  classical
  exact (G.neighborFinset u).erase v ∪ (G.neighborFinset v).erase u

theorem mem_edgeBoundary {u v x : V} :
    x ∈ edgeBoundary G u v ↔ x ≠ u ∧ x ≠ v ∧ (G.Adj x u ∨ G.Adj x v) := by
  classical
  simp only [edgeBoundary,Finset.mem_union,Finset.mem_erase,G.mem_neighborFinset]
  constructor
  · rintro (⟨xv,ux⟩|⟨xu,vx⟩)
    · exact ⟨ux.ne.symm,xv,Or.inl ux.symm⟩
    · exact ⟨xu,vx.ne.symm,Or.inr vx.symm⟩
  · rintro ⟨xu,xv,(xuEdge|xvEdge)⟩
    · exact Or.inl ⟨xv,xuEdge.symm⟩
    · exact Or.inr ⟨xu,xvEdge.symm⟩

omit [DecidableRel G.Adj] in
private theorem six_le_treeNumber_of_five_independent_neighbors
    (T : Finset V) (c : V) (five : 5 ≤ T.card)
    (edges : ∀ x ∈ T, G.Adj c x) (ind : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y) :
    6 ≤ Catalogue.treeNumber G := by
  classical
  obtain ⟨U,sub,count⟩ := Finset.exists_subset_card_eq five
  let S := insert c U
  have off : c ∉ U := fun h => G.loopless c (edges c (sub h))
  have size : S.card = 6 := by simp [S,off,count]
  let r : (↑S : Set V) := ⟨c,Finset.mem_insert_self _ _⟩
  let rank (x : (↑S : Set V)) : ℕ := if x = r then 0 else 1
  have other (x : (↑S : Set V)) (h : x ≠ r) : x.val ∈ U := by
    exact (Finset.mem_insert.mp x.property).resolve_left (fun eq => h (Subtype.ext eq))
  have tree : (G.induce (↑S : Set V)).IsTree := by
    apply Catalogue.tree_of_rank r rank
    · intro x y e
      by_cases xr : x = r
      · have yr : y ≠ r := fun h => e.ne (xr.trans h.symm)
        simp [rank,xr,yr]
      · by_cases yr : y = r
        · simp [rank,xr,yr]
        · exact (ind x.val (sub (other x xr)) y.val (sub (other y yr)) e).elim
    · intro x h
      simp [rank] at h
    · intro x xr
      have edge : (G.induce (↑S : Set V)).Adj x r := (edges x.val (sub (other x xr))).symm
      refine ⟨r,⟨edge,by simp [rank,xr]⟩,?_⟩
      intro y hy
      by_contra yr
      simp [rank,xr,yr] at hy
  simpa only [size] using Catalogue.card_le_treeNumber S tree

/-- For the archived crossing law, the two other-neighbor sets of
adjacent cubic vertices are disjoint. Otherwise their boundary has at
most three vertices, and its exterior gives a star on six vertices. -/
theorem adjacent_cubic_no_common_neighbor
    (cross : CrossingBetweenSurvivingEdges G)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    {u v : V} (uv : G.Adj u v) (cu : G.degree u = 3) (cv : G.degree v = 3)
    (x : V) : ¬ (G.Adj x u ∧ G.Adj x v) := by
  classical
  rintro ⟨xu,xv⟩
  let A := (G.neighborFinset u).erase v
  let B := (G.neighborFinset v).erase u
  let D := edgeBoundary G u v
  have dEq : D = A ∪ B := rfl
  have ac : A.card = 2 := by
    change ((G.neighborFinset u).erase v).card = 2
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u v).mpr uv),
      G.card_neighborFinset_eq_degree,cu]
  have bc : B.card = 2 := by
    change ((G.neighborFinset v).erase u).card = 2
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v u).mpr uv.symm),
      G.card_neighborFinset_eq_degree,cv]
  have someInter : (A ∩ B).Nonempty := ⟨x,Finset.mem_inter.mpr
    ⟨Finset.mem_erase.mpr ⟨xv.ne,(G.mem_neighborFinset u x).mpr xu.symm⟩,
      Finset.mem_erase.mpr ⟨xu.ne,(G.mem_neighborFinset v x).mpr xv.symm⟩⟩⟩
  have small : D.card ≤ 3 := by
    have pos := Finset.card_pos.mpr someInter
    rw [dEq]
    have tally := Finset.card_union_add_card_inter A B
    omega
  let U : Set V := {u,v}
  let W := Finset.univ \ insert u (insert v D)
  have outU (y : V) (hy : y ∈ W) : y ∉ U := by
    simp only [U,Set.mem_insert_iff,Set.mem_singleton_iff]
    exact fun h => (Finset.mem_sdiff.mp hy).2 (h.elim
      (fun eq => eq.symm ▸ Finset.mem_insert_self _ _)
      (fun eq => Finset.mem_insert_of_mem (eq.symm ▸ Finset.mem_insert_self _ _)))
  have outD (y : V) (hy : y ∈ W) : y ∉ D :=
    fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have ind (y : V) (hy : y ∈ W) (z : V) (hz : z ∈ W) : ¬ G.Adj y z := by
    intro yz
    have uD : u ∉ D := fun h => (mem_edgeBoundary.mp h).1 rfl
    have vD : v ∉ D := fun h => (mem_edgeBoundary.mp h).2.1 rfl
    obtain ⟨a,aU,b,bU,_,bD,ab⟩ := cross D small U
      ⟨u,by simp [U],v,by simp [U],uD,vD,uv⟩
      ⟨y,outU y hy,z,outU z hz,outD y hy,outD z hz,yz⟩
    have bu : b ≠ u := fun eq => bU (by simp [U,eq])
    have bv : b ≠ v := fun eq => bU (by simp [U,eq])
    have which : a = u ∨ a = v := by simpa [U] using aU
    exact bD (mem_edgeBoundary.mpr ⟨bu,bv,which.elim
      (fun eq => Or.inl (eq ▸ ab.symm)) (fun eq => Or.inr (eq ▸ ab.symm))⟩)
  have five : 5 ≤ W.card := by
    change 5 ≤ (Finset.univ \ insert u (insert v D)).card
    rw [Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ]
    have h₁ := Finset.card_insert_le u (insert v D)
    have h₂ := Finset.card_insert_le v D
    omega
  have all (y : V) (hy : y ∈ W) : G.neighborFinset y ⊆ D := by
    intro z hz
    have yz := (G.mem_neighborFinset y z).mp hz
    have yu : y ≠ u := fun h => outU y hy (by simp [U,h])
    have yv : y ≠ v := fun h => outU y hy (by simp [U,h])
    by_contra zD
    have zu : z ≠ u := fun eq => outD y hy
      (mem_edgeBoundary.mpr ⟨yu,yv,Or.inl (eq ▸ yz)⟩)
    have zv : z ≠ v := fun eq => outD y hy
      (mem_edgeBoundary.mpr ⟨yu,yv,Or.inr (eq ▸ yz)⟩)
    have zW : z ∈ W := by simp [W,zu,zv,zD]
    exact ind y hy z zW yz
  have same (y : V) (hy : y ∈ W) : G.neighborFinset y = D := by
    have degree := degree_of_small_deletion_preconnected (G := G) (by omega)
      (fun S h => (conn.2 S h).preconnected) y
    apply Finset.eq_of_subset_of_card_le (all y hy)
    rw [G.card_neighborFinset_eq_degree]
    omega
  have xD : x ∈ D := mem_edgeBoundary.mpr ⟨xu.ne,xv.ne,Or.inl xu⟩
  have six := six_le_treeNumber_of_five_independent_neighbors (G := G) W x five
    (fun y hy => G.symm ((G.mem_neighborFinset y x).mp ((same y hy).symm ▸ xD))) ind
  omega

#print axioms adjacent_cubic_no_common_neighbor

end Graffiti199Depleted
