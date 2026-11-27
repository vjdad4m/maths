import SharedHighCut
import ConnectivitySplice

open private FullPair.low FullPair.low_degree FullPair.low_stays FullPair.degree_three_off
  from SharedHighSeparation
open private pair_low_cases from FourBlockIntegration
open private pair_ports_card from PairSeparationAtOrders

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable (F : FourBlockPacking G)

/-- If at least three high vertices are shared, there are at most two
private highs. Deleting them separates the paired regions from a
singleton root. -/
theorem FourBlockPacking.shared_paired_highs_lt_three
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (conn : Catalogue.ConnectivityAtLeast G 3) (budget : Catalogue.treeNumber G ≤ 5) :
    (verticesIn (pairPorts F.depleted ∩ pairPorts F.terminal)).card < 3 := by
  classical
  let P := F.depleted
  let Q := F.terminal
  let A := verticesIn (pairPorts P)
  let B := verticesIn (pairPorts Q)
  let R := A ∩ B
  let D := (A ∪ B) \ R
  have qHigh (v : V) (hv : v ∈ pairPorts Q) : G.degree v ≠ 3 :=
    F.highDegree v (Or.inr hv)
  have rDef : verticesIn (pairPorts P ∩ pairPorts Q) = R := by
    ext v
    simp [R,A,B]
  change (verticesIn (pairPorts P ∩ pairPorts Q)).card < 3
  rw [rDef]
  by_contra! many
  have countA : A.card = 4 := pair_ports_card P
  have countB : B.card = 4 := pair_ports_card Q
  have sum := Finset.card_union_add_card_inter A B
  have sub : R ⊆ A ∪ B :=
    fun _ h => Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp h).1)
  have dCard : D.card = (A ∪ B).card - R.card := Finset.card_sdiff sub
  have rCard : R.card = (A ∩ B).card := rfl
  have few : D.card < 3 := by omega
  let U := labelRegion P.f ∪ labelRegion Q.f
  have firstOffP : F.first.f 0 ∉ labelRegion P.f :=
    FullPair.degree_three_off P F.first.degree
      (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 2))
      (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 3)) pHigh
  have firstOffQ : F.first.f 0 ∉ labelRegion Q.f :=
    FullPair.degree_three_off Q F.first.degree
      (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 4))
      (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 5)) qHigh
  have keepP : P.f 0 ∉ D := by
    intro deleted
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp deleted).1 with hp|hq
    · exact pHigh _ (mem_verticesIn.mp hp) (P.degree 0 (by decide))
    · exact qHigh _ (mem_verticesIn.mp hq) (P.degree 0 (by decide))
  have keepFirst : F.first.f 0 ∉ D := by
    intro deleted
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp deleted).1 with hp|hq
    · exact pHigh _ (mem_verticesIn.mp hp) F.first.degree
    · exact qHigh _ (mem_verticesIn.mp hq) F.first.degree
  have below (S : Finset V) (small : S.card < 3) :
      (G.induce {v | v ∉ S}).Preconnected := (conn.2 S small).preconnected
  obtain ⟨x,xU,y,yOff,xKeep,_,edge⟩ := cross_after_fewer_than_three below few (U := U)
    (Or.inl ⟨0,rfl⟩ : P.f 0 ∈ U)
    (fun h => h.elim firstOffP firstOffQ) keepP keepFirst
  have yP : y ∉ labelRegion P.f := fun h => yOff (Or.inl h)
  have yQ : y ∉ labelRegion Q.f := fun h => yOff (Or.inr h)
  have impossible (inUnion : x ∈ A ∪ B) : False := by
    have hx : x ∈ R :=
      Classical.byContradiction fun offR => xKeep (Finset.mem_sdiff.mpr ⟨inUnion,offR⟩)
    obtain ⟨xp,xq⟩ := Finset.mem_inter.mp hx
    exact F.shared_paired_high_no_outside_neighbor pHigh budget
      (mem_verticesIn.mp xp) (mem_verticesIn.mp xq) yP yQ edge
  rcases xU with ⟨i,rfl⟩|⟨i,rfl⟩
  · by_cases high : 2 ≤ i.val
    · exact impossible (Finset.mem_union.mpr
        (Or.inl (mem_verticesIn.mpr ⟨i,high,rfl⟩)))
    · rcases pair_low_cases i (by omega) with rfl|rfl
      · exact yP (FullPair.low_stays P false edge)
      · exact yP (FullPair.low_stays P true edge)
  · by_cases high : 2 ≤ i.val
    · exact impossible (Finset.mem_union.mpr
        (Or.inr (mem_verticesIn.mpr ⟨i,high,rfl⟩)))
    · rcases pair_low_cases i (by omega) with rfl|rfl
      · exact yQ (FullPair.low_stays Q false edge)
      · exact yQ (FullPair.low_stays Q true edge)

/-- The covered two-pair packing is impossible at connectivity at least
three and induced-tree number at most five, independently of the
order, singleton overlap and independence number. -/
theorem FourBlockPacking.impossible_of_connectivity_three_tree_budget
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (conn : Catalogue.ConnectivityAtLeast G 3) (budget : Catalogue.treeNumber G ≤ 5) :
    False :=
  (Nat.not_lt_of_ge (F.three_le_shared_paired_highs pHigh conn budget))
    (F.shared_paired_highs_lt_three pHigh conn budget)

namespace Catalogue

theorem no_canonical_four_block_packing_at_connectivity_three
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (conn : vertexConnectivity G = 3) (budget : treeNumber G ≤ 5) :
    False := by
  letI : Nonempty V := ⟨F.first.f 0⟩
  exact F.impossible_of_connectivity_three_tree_budget pHigh
    (conn ▸ connectivityAtLeast_vertexConnectivity (G := G)) budget

#print axioms FourBlockPacking.shared_paired_highs_lt_three
#print axioms FourBlockPacking.impossible_of_connectivity_three_tree_budget
#print axioms no_canonical_four_block_packing_at_connectivity_three

end Catalogue
end Graffiti199Depleted
