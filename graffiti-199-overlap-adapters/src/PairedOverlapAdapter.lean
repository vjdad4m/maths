import NeighborhoodAdapter

open private appendDisjoint appendDisjoint_region from NeighborhoodAdapter

namespace Graffiti199Depleted

open SimpleGraph

private def tipLow (i : O) : O := if i.val < 4 then 0 else 1

private def otherLow (i : O) : O := if i = 0 then 1 else 0

private def mate (i : O) : O :=
  match i with
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | _ => 0

private def same (i j : O) : Bool := tipLow i == tipLow j

/-- The unshared labels, starting with the low vertex on the side of the first shared tip. -/
private def residualLabels (i j : O) : Fin 4 → O :=
  ![tipLow i,otherLow (tipLow i),
    if same i j then (if tipLow i = 0 then 4 else 2) else mate i,
    if same i j then (if tipLow i = 0 then 5 else 3) else mate j]

private def originalPairLabel (i j : O) : Fin 8 → O :=
  ![0,i,j,0,residualLabels i j 0,residualLabels i j 1,residualLabels i j 2,residualLabels i j 3]

private def originalPairIndices : List (Fin 8) := [1,2,4,5,6,7]

private def mergedSingletonEdges : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(1,2)]

private def mergedEdges (i j : O) : List (Fin 8 × Fin 8) :=
  if same i j then sameHalfEdges else splitTipsEdges

private theorem residual_cert (i j : O) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) (neq : i ≠ j) :
    Function.Injective (residualLabels i j) ∧
      (∀ k : O, (∃ l : Fin 4, residualLabels i j l = k) ↔ k ≠ i ∧ k ≠ j) ∧
      residualLabels i j 0 ∈ ([0,1] : List O) ∧ residualLabels i j 1 ∈ ([0,1] : List O) := by
  revert i j
  decide

private theorem merged_edges_cert (i j : O) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) (neq : i ≠ j) :
    ∀ a b : Fin 8, (a,b) ∈ mergedEdges i j → (a,b) ∈ mergedSingletonEdges ∨
      (a ∈ originalPairIndices ∧ b ∈ originalPairIndices ∧
        terminalHas (originalPairLabel i j a) (originalPairLabel i j b) = true) := by
  revert i j
  decide

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- A paired block and a singleton sharing precisely the singleton's two
triangle tips yield one of the two certified eight-vertex merged blocks.
The paired vertices keep their original two-low, four-tip labelling. -/
theorem merged_block_of_two_shared_tips (S : PrivateSingleton G) (Q : O ↪ V)
    (pairEdges : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (Q a) (Q b))
    (pairDegree : ∀ a ∈ ([0,1] : List O), G.degree (Q a) = 3)
    {i j : O} (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (left : Q i = S.f 1) (right : Q j = S.f 2)
    (others : ∀ k : O, k ≠ i → k ≠ j → Q k ∉ labelRegion S.f) :
    (∃ M : MergedSameHalf G, labelRegion M.f = labelRegion S.f ∪ labelRegion Q) ∨
      ∃ M : MergedSplitTips G, labelRegion M.f = labelRegion S.f ∪ labelRegion Q := by
  have neq : i ≠ j := fun eq =>
    S.f.injective.ne (by decide : (1 : Fin 4) ≠ 2) (left.symm.trans (eq ▸ right))
  obtain ⟨inj,image,deg0,deg1⟩ := residual_cert i j hi hj neq
  let remainder : Fin 4 ↪ V := (⟨residualLabels i j,inj⟩ : Fin 4 ↪ O).trans Q
  have dis : Disjoint (labelRegion S.f) (labelRegion remainder) := by
    apply Set.disjoint_left.mpr
    rintro _ hs ⟨k,rfl⟩
    have off := (image (residualLabels i j k)).mp ⟨k,rfl⟩
    exact others _ off.1 off.2 hs
  let f := appendDisjoint S.f remainder dis
  have sameRegion : labelRegion f = labelRegion S.f ∪ labelRegion Q := by
    rw [appendDisjoint_region]
    ext v
    constructor
    · rintro (hs|⟨k,rfl⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨residualLabels i j k,rfl⟩
    · rintro (hs|⟨k,rfl⟩)
      · exact Or.inl hs
      · by_cases ki : k = i
        · exact Or.inl ⟨1,ki.symm ▸ left.symm⟩
        · by_cases kj : k = j
          · exact Or.inl ⟨2,kj.symm ▸ right.symm⟩
          · obtain ⟨l,e⟩ := (image k).mpr ⟨ki,kj⟩
            exact Or.inr ⟨l,congrArg Q e⟩
  have onPair (k : Fin 8) (hk : k ∈ originalPairIndices) : f k = Q (originalPairLabel i j k) := by
    fin_cases k
    · exact ((by decide : (0 : Fin 8) ∉ originalPairIndices) hk).elim
    · exact left.symm
    · exact right.symm
    · exact ((by decide : (3 : Fin 8) ∉ originalPairIndices) hk).elim
    · rfl
    · rfl
    · rfl
    · rfl
  have edge (a b : Fin 8) (e : (a,b) ∈ mergedEdges i j) : G.Adj (f a) (f b) := by
    rcases merged_edges_cert i j hi hj neq a b e with hs|⟨ha,hb,ab⟩
    · simp only [mergedSingletonEdges,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with h|h|h|h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      · exact S.edges 0 1 (by decide)
      · exact S.edges 0 2 (by decide)
      · exact S.edges 0 3 (by decide)
      · exact S.edges 1 2 (by decide)
    · rw [onPair a ha,onPair b hb]
      simp only [terminalHas,Bool.or_eq_true,List.contains_iff_mem] at ab
      exact ab.elim (pairEdges _ _) (fun h => (pairEdges _ _ h).symm)
  have degrees : ∀ k ∈ ([0,4,5] : List (Fin 8)), G.degree (f k) = 3 := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl
    · exact S.degree
    · exact pairDegree _ deg0
    · exact pairDegree _ deg1
  cases placement : same i j
  · exact Or.inr ⟨⟨f,fun a b e => edge a b (by simpa [mergedEdges,placement] using e),degrees⟩,sameRegion⟩
  · exact Or.inl ⟨⟨f,fun a b e => edge a b (by simpa [mergedEdges,placement] using e),degrees⟩,sameRegion⟩

/-- With two shared triangle tips, three singleton blocks and one paired
block give a Hamiltonian path in either placement of the shared tips. -/
theorem hamiltonian_of_two_shared_tips [DecidableEq V] (S R T : PrivateSingleton G) (Q : O ↪ V)
    (pairEdges : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (Q a) (Q b))
    (pairDegree : ∀ a ∈ ([0,1] : List O), G.degree (Q a) = 3)
    {i j : O} (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (left : Q i = S.f 1) (right : Q j = S.f 2)
    (others : ∀ k : O, k ≠ i → k ≠ j → Q k ∉ labelRegion S.f)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : V, s ∉ D ∧ (∀ t : V, t ∉ D → ¬ G.Adj s t) ∧
          (G.induce {v | v ∉ D ∧ v ≠ s}).Preconnected)
    (noSix : NoIndependentSix G)
    (mr : Disjoint (labelRegion S.f ∪ labelRegion Q) (labelRegion R.f))
    (mt : Disjoint (labelRegion S.f ∪ labelRegion Q) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion S.f ∪ labelRegion Q ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f)
    (rOff : ¬ G.Adj (R.f 2) (R.f 3)) (tOff : ¬ G.Adj (T.f 2) (T.f 3))
    (rDegree : G.degree (R.f 3) ≠ 3) (tDegree : G.degree (T.f 3) ≠ 3) :
    ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  rcases merged_block_of_two_shared_tips S Q pairEdges pairDegree hi hj left right others with
    ⟨M,reg⟩|⟨M,reg⟩
  · exact (hamiltonian_same_half_of_induced_cuts M R T below three noSix
      (reg.symm ▸ mr) (reg.symm ▸ mt) rt (fun v => reg.symm ▸ cover v)
      rOff tOff rDegree tDegree).2
  · exact pathOn_univ_iff_hamiltonian_walk.mp
      (traceable_three_singletons_split_tips M R T (edgeReach_of_induced_singleton_cuts below three)
        noSix (reg.symm ▸ mr) (reg.symm ▸ mt) rt (fun v => reg.symm ▸ cover v))

#print axioms merged_block_of_two_shared_tips
#print axioms hamiltonian_of_two_shared_tips

end Graffiti199Depleted
