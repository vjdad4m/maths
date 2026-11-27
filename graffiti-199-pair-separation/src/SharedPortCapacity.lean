import OppositeHalf

open private FullPair.low FullPair.high_side from SharedHighSeparation
open private FullPair.neighbors_zero FullPair.neighbors_one from RetainedGeometry

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

noncomputable def verticesIn (U : Set V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ U

@[simp] theorem mem_verticesIn {U : Set V} {v : V} : v ∈ verticesIn U ↔ v ∈ U := by
  classical
  simp [verticesIn]

private def FullPair.halfFinset (P : FullPair G) (s : Bool) : Finset V :=
  (if s then ({4,5} : Finset O) else {2,3}).map P.f

private theorem FullPair.halfFinset_card (P : FullPair G) (s : Bool) :
    (P.halfFinset s).card = 2 := by
  rw [FullPair.halfFinset,Finset.card_map]
  cases s <;> decide

private theorem FullPair.mem_half_of_adj (P : FullPair G) {s : Bool} {v : V}
    (hv : v ∈ pairPorts P) (e : G.Adj v (FullPair.low P s)) : v ∈ P.halfFinset s := by
  obtain ⟨i,hi,ie⟩ := hv
  have forbid0 : P.f 0 ≠ v := fun eq => ((by decide : ¬ 2 ≤ (0 : O).val)
    (P.f.injective (eq.trans ie.symm) ▸ hi))
  have forbid1 : P.f 1 ≠ v := fun eq => ((by decide : ¬ 2 ≤ (1 : O).val)
    (P.f.injective (eq.trans ie.symm) ▸ hi))
  cases s
  · obtain ⟨j,m,eq⟩ := FullPair.neighbors_zero P e.symm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with rfl|rfl|rfl
    · exact (forbid1 eq).elim
    · exact Finset.mem_map.mpr ⟨2,by decide,eq⟩
    · exact Finset.mem_map.mpr ⟨3,by decide,eq⟩
  · obtain ⟨j,m,eq⟩ := FullPair.neighbors_one P e.symm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with rfl|rfl|rfl
    · exact (forbid0 eq).elim
    · exact Finset.mem_map.mpr ⟨4,by decide,eq⟩
    · exact Finset.mem_map.mpr ⟨5,by decide,eq⟩

variable (F : FourBlockPacking G)

private theorem sides_equal
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3) (bound : Catalogue.treeNumber G ≤ 5)
    {x y : V} (xp : x ∈ pairPorts F.depleted) (xq : x ∈ pairPorts F.terminal)
    (yp : y ∈ pairPorts F.depleted) (ys : y ∈ singletonPorts F.first ∪ singletonPorts F.second)
    {a b : Bool}
    (xa : G.Adj x (FullPair.low F.depleted a)) (yb : G.Adj y (FullPair.low F.depleted b)) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact (F.no_owned_high_opposite_shared_high pHigh bound false xp xq yp ys xa yb).elim
  · exact (F.no_owned_high_opposite_shared_high pHigh bound true xp xq yp ys xa yb).elim
  · rfl

/-- If a paired block has both a high shared with the other pair and
a high owned by a singleton, all those highs fit in one two-port half. -/
theorem FourBlockPacking.shared_owned_highs_capacity
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3) (bound : Catalogue.treeNumber G ≤ 5)
    (A : Finset V) (B : Finset V)
    (ae : ∀ v, v ∈ A ↔ v ∈ pairPorts F.depleted ∩ pairPorts F.terminal)
    (be : ∀ v, v ∈ B ↔ v ∈ pairPorts F.depleted ∩
      (singletonPorts F.first ∪ singletonPorts F.second))
    (asome : A.Nonempty) (bsome : B.Nonempty) : A.card + B.card ≤ 2 := by
  classical
  obtain ⟨x,hx⟩ := asome
  obtain ⟨y,hy⟩ := bsome
  have xp := (ae x).mp hx
  have yp := (be y).mp hy
  obtain ⟨a,xa,_⟩ := FullPair.high_side F.depleted xp.1
  obtain ⟨b,yb,_⟩ := FullPair.high_side F.depleted yp.1
  have ab : a = b := sides_equal F pHigh bound xp.1 xp.2 yp.1 yp.2 xa yb
  have aHalf (v : V) (h : v ∈ A) : v ∈ F.depleted.halfFinset b := by
    have vm := (ae v).mp h
    obtain ⟨r,vr,_⟩ := FullPair.high_side F.depleted vm.1
    have eq := sides_equal F pHigh bound vm.1 vm.2 yp.1 yp.2 vr yb
    exact F.depleted.mem_half_of_adj vm.1 (eq ▸ vr)
  have bHalf (v : V) (h : v ∈ B) : v ∈ F.depleted.halfFinset b := by
    have vm := (be v).mp h
    obtain ⟨r,vr,_⟩ := FullPair.high_side F.depleted vm.1
    have eq := sides_equal F pHigh bound xp.1 xp.2 vm.1 vm.2 xa vr
    exact F.depleted.mem_half_of_adj vm.1 ((eq.symm.trans ab) ▸ vr)
  have triple := F.no_paired_pair_singleton_triple_overlap pHigh bound
  have separate : Disjoint A B := Finset.disjoint_left.mpr fun v a b =>
    Set.disjoint_left.mp triple ((ae v).mp a) ((be v).mp b).2
  have cap := Finset.card_le_card (Finset.union_subset aHalf bHalf)
  rw [Finset.card_union_of_disjoint separate,FullPair.halfFinset_card] at cap
  exact cap

#print axioms FourBlockPacking.shared_owned_highs_capacity

end Graffiti199Depleted
