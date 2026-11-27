import FootprintApplication
import MainGraphBridges

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- The three labels of the open neighborhood of a singleton root
determine its rooted block and the private-singleton certificate. -/
theorem privateSingleton_of_neighborhood {U : Set V} {k a b c : V}
    (neighbors : ∀ u : V, G.Adj k u ↔ u = a ∨ u = b ∨ u = c)
    (triangle : G.Adj a b) (looseA : ¬ G.Adj a c) (looseB : ¬ G.Adj b c)
    (block : U = {k,a,b,c}) :
    ∃ R : PrivateSingleton G, labelRegion R.f = U ∧ R.f 0 = k ∧ R.f 1 = a ∧
      R.f 2 = b ∧ R.f 3 = c := by
  classical
  have ka := (neighbors a).mpr (Or.inl rfl)
  have kb := (neighbors b).mpr (Or.inr (Or.inl rfl))
  have kc := (neighbors c).mpr (Or.inr (Or.inr rfl))
  have ac : a ≠ c := fun e => looseB (e ▸ triangle.symm)
  have bc : b ≠ c := fun e => looseA (e ▸ triangle)
  let L := [k,a,b,c]
  have nd : L.Nodup := by simp [L,ka.ne,kb.ne,kc.ne,triangle.ne,ac,bc]
  let f : Fin 4 ↪ V := ⟨L.get,fun _ _ eq => nd.get_inj_iff.mp eq⟩
  have root : G.degree k = 3 := by
    apply (degree_three_iff_three_neighbors k).mpr
    refine ⟨{a,b,c},?_,fun u => (neighbors u).trans ?_⟩
    · rw [Finset.card_insert_of_not_mem,Finset.card_pair bc]
      simp [triangle.ne,ac]
    · simp
  have edges : ∀ i j, (i,j) ∈ singletonEdges → G.Adj (f i) (f j) := by
    intro i j e
    simp only [singletonEdges,List.mem_cons,List.not_mem_nil,or_false] at e
    rcases e with h|h|h|h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    · exact ka
    · exact kb
    · exact kc
    · exact triangle
  let R : PrivateSingleton G := ⟨f,edges,looseA,root⟩
  refine ⟨R,?_,rfl,rfl,rfl,rfl⟩
  ext u
  change (∃ i : Fin L.length, L.get i = u) ↔ u ∈ U
  rw [← List.mem_iff_get,block]
  simp [L]

/-- Join disjoint vertex labellings without changing the labels of either block. -/
private def appendDisjoint {m n : ℕ} (f : Fin m ↪ V) (g : Fin n ↪ V)
    (sep : Disjoint (labelRegion f) (labelRegion g)) : Fin (m+n) ↪ V where
  toFun := Fin.append f g
  inj' := by
    intro x y
    refine Fin.addCases (m := m) (n := n) (motive := fun x => Fin.append f g x =
      Fin.append f g y → x = y) ?_ ?_ x
    · intro i
      refine Fin.addCases (m := m) (n := n) (motive := fun y => Fin.append f g (i.castAdd n) =
        Fin.append f g y → i.castAdd n = y) ?_ ?_ y
      · intro j e
        rw [Fin.append_left,Fin.append_left] at e
        exact congrArg (Fin.castAdd n) (f.injective e)
      · intro j e
        rw [Fin.append_left,Fin.append_right] at e
        exact (Set.disjoint_left.mp sep ⟨i,rfl⟩ ⟨j,e.symm⟩).elim
    · intro i
      refine Fin.addCases (m := m) (n := n) (motive := fun y => Fin.append f g (i.natAdd m) =
        Fin.append f g y → i.natAdd m = y) ?_ ?_ y
      · intro j e
        rw [Fin.append_right,Fin.append_left] at e
        exact (Set.disjoint_left.mp sep ⟨j,rfl⟩ ⟨i,e⟩).elim
      · intro j e
        rw [Fin.append_right,Fin.append_right] at e
        exact congrArg (Fin.natAdd m) (g.injective e)

omit [Fintype V] in
private theorem appendDisjoint_region {m n : ℕ} (f : Fin m ↪ V) (g : Fin n ↪ V)
    (sep : Disjoint (labelRegion f) (labelRegion g)) :
    labelRegion (appendDisjoint f g sep) = labelRegion f ∪ labelRegion g := by
  ext v
  constructor
  · rintro ⟨i,eq⟩
    revert eq
    refine Fin.addCases (m := m) (n := n) (motive := fun i => appendDisjoint f g sep i = v →
      v ∈ labelRegion f ∪ labelRegion g) ?_ ?_ i
    · intro j e
      exact Or.inl ⟨j,(Fin.append_left f g j).symm.trans e⟩
    · intro j e
      exact Or.inr ⟨j,(Fin.append_right f g j).symm.trans e⟩
  · rintro (⟨i,rfl⟩|⟨i,rfl⟩)
    · exact ⟨i.castAdd n,Fin.append_left f g i⟩
    · exact ⟨i.natAdd m,Fin.append_right f g i⟩

/-- Adjoin the two low vertices of the paired block and the two tips of its
retained half. Its other two tips are the first singleton's triangle tips. -/
theorem mergedSameHalf_of_blocks (S : PrivateSingleton G) (Q : Fin 4 ↪ V)
    (sep : Disjoint (labelRegion S.f) (labelRegion Q))
    (lowEdge : G.Adj (Q 0) (Q 1))
    (sharedA : G.Adj (Q 0) (S.f 1)) (sharedB : G.Adj (Q 0) (S.f 2))
    (retainedA : G.Adj (Q 1) (Q 2)) (retainedB : G.Adj (Q 1) (Q 3))
    (retainedEdge : G.Adj (Q 2) (Q 3))
    (degreeA : G.degree (Q 0) = 3) (degreeB : G.degree (Q 1) = 3) :
    ∃ M : MergedSameHalf G, labelRegion M.f = labelRegion S.f ∪ labelRegion Q := by
  let f := appendDisjoint S.f Q sep
  have edges : ∀ i j, (i,j) ∈ sameHalfEdges → G.Adj (f i) (f j) := by
    intro i j h
    simp only [sameHalfEdges,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e|e|e|e|e|e <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    · exact S.edges 0 1 (by decide)
    · exact S.edges 0 2 (by decide)
    · exact S.edges 0 3 (by decide)
    · exact S.edges 1 2 (by decide)
    · exact lowEdge
    · exact sharedA
    · exact sharedB
    · exact retainedA
    · exact retainedB
    · exact retainedEdge
  have degree : ∀ i ∈ ([0,4,5] : List (Fin 8)), G.degree (f i) = 3 := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl
    · exact S.degree
    · exact degreeA
    · exact degreeB
  exact ⟨⟨f,edges,degree⟩,appendDisjoint_region S.f Q sep⟩

/-- The same-half arrangement has eight vertices in the merged region and
four vertices in each private singleton region. -/
theorem MergedSameHalf.order (M : MergedSameHalf G) (R T : PrivateSingleton G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f) :
    Fintype.card V = 16 := by
  let head := appendDisjoint M.f R.f mr
  have headRegion : labelRegion head = labelRegion M.f ∪ labelRegion R.f :=
    appendDisjoint_region M.f R.f mr
  have sep : Disjoint (labelRegion head) (labelRegion T.f) :=
    headRegion.symm ▸ Set.disjoint_union_left.mpr ⟨mt,rt⟩
  let all := appendDisjoint head T.f sep
  have onto : Function.Surjective all := by
    intro v
    change v ∈ labelRegion all
    rw [appendDisjoint_region,headRegion]
    exact (cover v).elim (fun hm => Or.inl (Or.inl hm))
      (fun rest => rest.elim (fun hr => Or.inl (Or.inr hr)) Or.inr)
  have count := Fintype.card_congr (Equiv.ofBijective all ⟨all.injective,onto⟩)
  simpa using count.symm

/-- The same-half splice under cut hypotheses on the original graph and
degree-three exclusion at the two private loose vertices. -/
theorem hamiltonian_same_half_of_induced_cuts [DecidableEq V] (M : MergedSameHalf G)
    (R T : PrivateSingleton G)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : V, s ∉ D ∧ (∀ t : V, t ∉ D → ¬ G.Adj s t) ∧
          (G.induce {v | v ∉ D ∧ v ≠ s}).Preconnected)
    (noSix : NoIndependentSix G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f)
    (rOff : ¬ G.Adj (R.f 2) (R.f 3)) (tOff : ¬ G.Adj (T.f 2) (T.f 3))
    (rDegree : G.degree (R.f 3) ≠ 3) (tDegree : G.degree (T.f 3) ≠ 3) :
    Fintype.card V = 16 ∧ ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  classical
  have size := M.order R T mr mt rt cover
  have lo := degree_of_small_deletion_preconnected (by omega) below
  have rMin := lo (R.f 3)
  have tMin := lo (T.f 3)
  refine ⟨size,pathOn_univ_iff_hamiltonian_walk.mp (traceable_three_singletons_same_half_tips M R T
    (edgeReach_of_induced_singleton_cuts below three) noSix mr mt rt cover rOff tOff (by omega) (by omega))⟩

#print axioms privateSingleton_of_neighborhood
#print axioms mergedSameHalf_of_blocks
#print axioms MergedSameHalf.order
#print axioms hamiltonian_same_half_of_induced_cuts

end Graffiti199Depleted
