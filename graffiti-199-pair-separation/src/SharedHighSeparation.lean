import TreeBudget
import RetainedGeometry

open private FullPair.neighbors_zero FullPair.neighbors_one from RetainedGeometry
open private pair_low_cases from FourBlockIntegration

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private def lowLabel (s : Bool) : O := if s then 1 else 0

private def FullPair.low (P : FullPair G) (s : Bool) : V := P.f (lowLabel s)

private theorem FullPair.low_degree (P : FullPair G) (s : Bool) : G.degree (P.low s) = 3 := by
  cases s
  · exact P.degree 0 (by decide)
  · exact P.degree 1 (by decide)

private theorem FullPair.low_edge (P : FullPair G) (s : Bool) : G.Adj (P.low s) (P.low (!s)) := by
  cases s
  · exact P.edges 0 1 (by decide)
  · exact (P.edges 0 1 (by decide)).symm

private theorem FullPair.low_stays (P : FullPair G) (s : Bool) {v : V} (h : G.Adj (P.low s) v) :
    v ∈ labelRegion P.f := by
  cases s
  · obtain ⟨j,_,e⟩ := FullPair.neighbors_zero P h
    exact ⟨j,e⟩
  · obtain ⟨j,_,e⟩ := FullPair.neighbors_one P h
    exact ⟨j,e⟩

private theorem FullPair.high_side (P : FullPair G) {v : V} (vp : v ∈ pairPorts P) :
    ∃ s : Bool, G.Adj v (P.low s) ∧ ¬ G.Adj v (P.low (!s)) := by
  obtain ⟨i,hi,rfl⟩ := vp
  have off0 (off : i ∉ ([1,2,3] : List O)) : ¬ G.Adj (P.f i) (P.f 0) := by
    intro edge
    obtain ⟨j,hj,e⟩ := FullPair.neighbors_zero P edge.symm
    exact off (P.f.injective e ▸ hj)
  have off1 (off : i ∉ ([0,4,5] : List O)) : ¬ G.Adj (P.f i) (P.f 1) := by
    intro edge
    obtain ⟨j,hj,e⟩ := FullPair.neighbors_one P edge.symm
    exact off (P.f.injective e ▸ hj)
  fin_cases i
  · exact ((by decide : ¬ 2 ≤ (0 : O).val) hi).elim
  · exact ((by decide : ¬ 2 ≤ (1 : O).val) hi).elim
  · exact ⟨false,(P.edges 0 2 (by decide)).symm,off1 (by decide)⟩
  · exact ⟨false,(P.edges 0 3 (by decide)).symm,off1 (by decide)⟩
  · exact ⟨true,(P.edges 1 4 (by decide)).symm,off0 (by decide)⟩
  · exact ⟨true,(P.edges 1 5 (by decide)).symm,off0 (by decide)⟩

private theorem FullPair.degree_three_off (P : FullPair G) {v : V}
    (degree : G.degree v = 3) (off0 : v ≠ P.f 0) (off1 : v ≠ P.f 1)
    (pHigh : ∀ u ∈ pairPorts P, G.degree u ≠ 3) :
    v ∉ labelRegion P.f := by
  rintro ⟨i,eq⟩
  by_cases hi : 2 ≤ i.val
  · exact pHigh v ⟨i,hi,eq⟩ degree
  · rcases pair_low_cases i (by omega) with rfl|rfl
    · exact off0 eq.symm
    · exact off1 eq.symm

private theorem singleton_high_adj (S : PrivateSingleton G) {v : V} (hs : v ∈ singletonPorts S) :
    G.Adj v (S.f 0) := by
  obtain ⟨i,hi,rfl⟩ := hs
  fin_cases i
  · cases hi
  · exact (S.edges 0 1 (by decide)).symm
  · exact (S.edges 0 2 (by decide)).symm
  · exact (S.edges 0 3 (by decide)).symm

private def branchEdges : List (Fin 6 × Fin 6) := [(0,1),(1,2),(0,3),(3,4),(0,5)]

private def branchAdj (i j : Fin 6) : Bool :=
  branchEdges.contains (i,j) || branchEdges.contains (j,i)

private theorem branch_earlier : ∀ i : Fin 6, i ≠ 0 →
    ∃ j : Fin 6, branchAdj i j = true ∧ j < i ∧
      ∀ k : Fin 6, branchAdj i k = true → k < i → k = j := by decide

variable (F : FourBlockPacking G)

/-- A common high of the two paired neighborhoods cannot see a vertex
outside both full paired neighborhoods under the tree budget. -/
theorem FourBlockPacking.shared_paired_high_no_outside_neighbor
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (bound : Catalogue.treeNumber G ≤ 5) {x y : V}
    (xp : x ∈ pairPorts F.depleted) (xq : x ∈ pairPorts F.terminal)
    (yp : y ∉ labelRegion F.depleted.f) (yq : y ∉ labelRegion F.terminal.f) :
    ¬ G.Adj x y := by
  intro xy
  let P := F.depleted
  let Q := F.terminal
  obtain ⟨p,px,pOff⟩ := P.high_side xp
  obtain ⟨q,qx,qOff⟩ := Q.high_side xq
  have qHigh (v : V) (h : v ∈ pairPorts Q) := F.highDegree v (Or.inr h)
  have outsideP (s : Bool) : Q.low s ∉ labelRegion P.f := by
    apply P.degree_three_off (Q.low_degree s) _ _ pHigh
    · cases s
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 2)
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 2)
    · cases s
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 3)
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 3)
  have noCross (a b : Bool) : ¬ G.Adj (P.low a) (Q.low b) :=
    fun h => outsideP b (P.low_stays a h)
  have pNe (s : Bool) : x ≠ P.low s := fun e => qHigh x xq (e.symm ▸ P.low_degree s)
  have qNe (s : Bool) : x ≠ Q.low s := fun e => qHigh x xq (e.symm ▸ Q.low_degree s)
  have midNe (a b : Bool) : P.low a ≠ Q.low b :=
    fun e => outsideP b ⟨lowLabel a,e⟩
  have pyNe (s : Bool) : P.low s ≠ y := fun e => yp ⟨lowLabel s,e⟩
  have qyNe (s : Bool) : Q.low s ≠ y := fun e => yq ⟨lowLabel s,e⟩
  have pyOff (s : Bool) : ¬ G.Adj (P.low s) y := fun edge => yp (P.low_stays s edge)
  have qyOff (s : Bool) : ¬ G.Adj (Q.low s) y := fun edge => yq (Q.low_stays s edge)
  have pp := P.low_edge p
  have qq := Q.low_edge q
  let L := [x,P.low p,P.low (!p),Q.low q,Q.low (!q),y]
  have nd : L.Nodup := by
    simp [L,pNe,qNe,midNe,pyNe,qyNe,xy.ne,pp.ne,qq.ne]
  let f : Fin 6 ↪ V := ⟨L.get,fun _ _ e => nd.get_inj_iff.mp e⟩
  have revNoCross (a b : Bool) : ¬ G.Adj (Q.low b) (P.low a) := fun h => noCross a b h.symm
  have revPy (s : Bool) : ¬ G.Adj y (P.low s) := fun h => pyOff s h.symm
  have revQy (s : Bool) : ¬ G.Adj y (Q.low s) := fun h => qyOff s h.symm
  have pOff' : ¬ G.Adj (P.low (!p)) x := fun h => pOff h.symm
  have qOff' : ¬ G.Adj (Q.low (!q)) x := fun h => qOff h.symm
  have v0 : f 0 = x := rfl
  have v1 : f 1 = P.low p := rfl
  have v2 : f 2 = P.low (!p) := rfl
  have v3 : f 3 = Q.low q := rfl
  have v4 : f 4 = Q.low (!q) := rfl
  have v5 : f 5 = y := rfl
  have chart (a b : Fin 6) : G.Adj (f a) (f b) ↔ branchAdj a b = true := by
    fin_cases a <;> fin_cases b <;>
      simp [v0,v1,v2,v3,v4,v5,branchAdj,branchEdges,px,px.symm,pOff,pOff',qx,qx.symm,qOff,qOff',
        pp,pp.symm,qq,qq.symm,xy,xy.symm,noCross,revNoCross,pyOff,qyOff,revPy,revQy] <;> decide
  have six := Catalogue.six_le_treeNumber_of_ordering (G := G) f (by
    intro i hi
    obtain ⟨j,ij,lt,all⟩ := branch_earlier i hi
    exact ⟨j,(chart _ _).mpr ij,lt,fun k e l => all k ((chart _ _).mp e) l⟩)
  omega

/-- Shared paired highs cannot belong to either singleton. This is a
partial separation theorem, independent of the no-independent-six premise. -/
theorem FourBlockPacking.no_paired_pair_singleton_triple_overlap
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (bound : Catalogue.treeNumber G ≤ 5) :
    Disjoint (pairPorts F.depleted ∩ pairPorts F.terminal)
      (singletonPorts F.first ∪ singletonPorts F.second) := by
  apply Set.disjoint_left.mpr
  intro x xp xs
  have qHigh (v : V) (h : v ∈ pairPorts F.terminal) := F.highDegree v (Or.inr h)
  rcases xs with h|h
  · exact F.shared_paired_high_no_outside_neighbor pHigh bound xp.1 xp.2
      (F.depleted.degree_three_off F.first.degree
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 2))
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 3)) pHigh)
      (F.terminal.degree_three_off F.first.degree
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 4))
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 5)) qHigh)
      (singleton_high_adj F.first h)
  · exact F.shared_paired_high_no_outside_neighbor pHigh bound xp.1 xp.2
      (F.depleted.degree_three_off F.second.degree
        (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 2))
        (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 3)) pHigh)
      (F.terminal.degree_three_off F.second.degree
        (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 4))
        (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 5)) qHigh)
      (singleton_high_adj F.second h)

#print axioms FourBlockPacking.shared_paired_high_no_outside_neighbor
#print axioms FourBlockPacking.no_paired_pair_singleton_triple_overlap

end Graffiti199Depleted
