import RootedTreeRank

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Count an induced tree specified by an injective copy in the ambient graph. -/
theorem card_le_treeNumber_of_induced_copy [Fintype V] [Fintype W]
    (f : W ↪ V) (chart : ∀ x y, G.Adj (f x) (f y) ↔ H.Adj x y) (tree : H.IsTree) :
    Fintype.card W ≤ treeNumber G := by
  classical
  let S := Finset.univ.map f
  let g : W → (↑S : Set V) := fun x => ⟨f x,Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩
  have inj : Function.Injective g := fun _ _ e => f.injective (congrArg Subtype.val e)
  have surj : Function.Surjective g := by
    intro y
    obtain ⟨x,_,eq⟩ := Finset.mem_map.mp y.property
    exact ⟨x,Subtype.ext eq⟩
  let e := Equiv.ofBijective g ⟨inj,surj⟩
  let iso : H ≃g G.induce (↑S : Set V) := ⟨e,fun {x y} => chart x y⟩
  rcases SimpleGraph.isTree_iff_connected_and_card.mp tree with ⟨conn,count⟩
  have treeS : (G.induce (↑S : Set V)).IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨iso.connected_iff.mp conn,?_⟩
    rw [← Nat.card_congr iso.mapEdgeSet,← Nat.card_congr e]
    exact count
  simpa [S] using card_le_treeNumber S treeS

/-- Replace one edge of an induced tree by a chordless path with new
interior vertices, with no other edges between the old and new vertices. -/
theorem card_le_treeNumber_of_subdivided_edge [Fintype V] [Fintype W]
    (tree : H.IsTree) {a b : W} (ab : H.Adj a b) (f : W ↪ V) {m : ℕ}
    (c : Fin (m+1) ↪ V) (disjoint : ∀ x i, f x ≠ c i)
    (old : ∀ x y, G.Adj (f x) (f y) ↔ H.Adj x y ∧
      ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (inner : ∀ i j, G.Adj (c i) (c j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (ends : ∀ x i, G.Adj (f x) (c i) ↔ (x = a ∧ i.val = 0) ∨ (x = b ∧ i.val = m)) :
    Fintype.card W + (m+1) ≤ treeNumber G := by
  classical
  let g : W ⊕ Fin (m+1) ↪ V :=
    ⟨Sum.elim f c,by
      intro x y eq
      rcases x with (x|x) <;> rcases y with (y|y)
      · exact congrArg Sum.inl (f.injective eq)
      · exact (disjoint x y eq).elim
      · exact (disjoint y x eq.symm).elim
      · exact congrArg Sum.inr (c.injective eq)⟩
  let J := G.comap g
  obtain ⟨rho,zero,separate,parent⟩ := rooted_tree_rank tree a
  let rank : W ⊕ Fin (m+1) → ℕ :=
    Sum.elim (fun x => if x = a then 0 else m+1+rho x) (fun i => i.val+1)
  have rhoa : rho a = 0 := (zero _).mpr rfl
  have pos {x : W} (off : x ≠ a) : 0 < rho x :=
    Nat.pos_of_ne_zero (fun z => off ((zero _).mp z))
  have ranka : rank (Sum.inl a) = 0 := by simp [rank]
  have rank_old {x : W} (off : x ≠ a) : rank (Sum.inl x) = m+1+rho x := by simp [rank,off]
  have earlier {x y : W} (off : x ≠ a) :
      rank (Sum.inl y) < rank (Sum.inl x) ↔ rho y < rho x := by
    rw [rank_old off]
    by_cases ya : y = a
    · subst y
      rw [ranka,rhoa]
      have p := pos off
      omega
    · rw [rank_old ya]
      omega
  have rank_inner (i : Fin (m+1)) : rank (Sum.inr i) = i.val+1 := rfl
  have treeJ : J.IsTree := by
    apply tree_of_rank (Sum.inl a) rank
    · intro x y edge eq
      rcases x with (x|i) <;> rcases y with (y|j)
      · have adj : H.Adj x y := ((old x y).mp edge).1
        by_cases xa : x = a
        · subst x
          have p := pos adj.ne.symm
          rw [ranka,rank_old adj.ne.symm] at eq
          omega
        · by_cases ya : y = a
          · subst y
            have p := pos xa
            rw [rank_old xa,ranka] at eq
            omega
          · rw [rank_old xa,rank_old ya] at eq
            exact separate adj (by omega)
      · rw [rank_inner] at eq
        by_cases xa : x = a
        · subst x
          rw [ranka] at eq
          omega
        · have p := pos xa
          rw [rank_old xa] at eq
          have lim := j.isLt
          omega
      · rw [rank_inner] at eq
        by_cases ya : y = a
        · subst y
          rw [ranka] at eq
          omega
        · have p := pos ya
          rw [rank_old ya] at eq
          have lim := i.isLt
          omega
      · have adj := (inner i j).mp edge
        rw [rank_inner,rank_inner] at eq
        omega
    · intro x h
      rw [ranka] at h
      omega
    · intro x notRoot
      rcases x with (x|i)
      · have xa : x ≠ a := fun eq => notRoot (congrArg Sum.inl eq)
        by_cases xb : x = b
        · subst x
          let j : Fin (m+1) := Fin.last m
          refine ⟨Sum.inr j,⟨(ends b j).mpr (Or.inr ⟨rfl,rfl⟩),?_⟩,?_⟩
          · rw [rank_inner,rank_old xa]
            change m+1 < m+1+rho b
            have p := pos xa
            omega
          · rintro (y|i) ⟨edge,lt⟩
            · obtain ⟨adj,removed⟩ := (old b y).mp edge
              have eq := (parent b xa).unique ⟨adj,(earlier xa).mp lt⟩ ⟨ab.symm,by
                rw [rhoa]; exact pos xa⟩
              exact (removed (Or.inr ⟨rfl,eq⟩)).elim
            · have hit := (ends b i).mp edge
              exact congrArg Sum.inr (Fin.ext ((hit.resolve_left (fun h => xa h.1)).2))
        · obtain ⟨y,⟨adj,prev⟩,only⟩ := parent x xa
          refine ⟨Sum.inl y,⟨(old x y).mpr ⟨adj,fun h => h.elim (fun h => xa h.1)
            (fun h => xb h.1)⟩,(earlier xa).mpr prev⟩,?_⟩
          rintro (z|i) ⟨edge,lt⟩
          · exact congrArg Sum.inl (only z ⟨((old x z).mp edge).1,(earlier xa).mp lt⟩)
          · exact (((ends x i).mp edge).elim (fun h => xa h.1) (fun h => xb h.1)).elim
      · by_cases iz : i.val = 0
        · refine ⟨Sum.inl a,⟨((ends a i).mpr (Or.inl ⟨rfl,iz⟩)).symm,?_⟩,?_⟩
          · rw [rank_inner,ranka]; omega
          · rintro (x|j) ⟨edge,lt⟩
            · by_cases xa : x = a
              · exact congrArg Sum.inl xa
              · rw [rank_old xa,rank_inner] at lt
                have p := pos xa
                omega
            · rw [rank_inner,rank_inner] at lt
              omega
        · let j : Fin (m+1) := ⟨i.val-1,by have h := i.isLt; omega⟩
          have step : j.val+1 = i.val := by dsimp [j]; omega
          refine ⟨Sum.inr j,⟨(inner i j).mpr (Or.inr step),?_⟩,?_⟩
          · rw [rank_inner,rank_inner]; omega
          · rintro (x|k) ⟨edge,lt⟩
            · by_cases xa : x = a
              · subst x
                exact (((ends a i).mp edge.symm).elim (fun h => iz h.2)
                  (fun h => ab.ne h.1)).elim
              · rw [rank_old xa,rank_inner] at lt
                have p := pos xa
                have lim := i.isLt
                omega
            · have adj := (inner i k).mp edge
              rw [rank_inner,rank_inner] at lt
              exact congrArg Sum.inr (Fin.ext (by omega))
  simpa using card_le_treeNumber_of_induced_copy g (H := J) (fun _ _ => Iff.rfl) treeJ

#print axioms card_le_treeNumber_of_subdivided_edge

end Graffiti199Depleted.Catalogue
