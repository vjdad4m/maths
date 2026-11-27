import CutGeometry180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In an upper block on at least four vertices with a split lower graph,
the seam has a third lower neighbor in addition to the two tips. -/
theorem third_seam_neighbor {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w r : V} {S T : Finset V} (s : Split J w S T) (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S)
    (xw : J.Adj x w) (wy : J.Adj w y) (block : NoCut (J⊔edge x y))
    (sp : SparseAt (J⊔edge x y) r) : ∃ z,J.Adj w z ∧ z≠x ∧ z≠y := by
  classical
  have sideThird {Q R : Finset V} {a b : V} (q : Split J w Q R) (aQ : a∈Q) (bQ : b∉Q)
      (aw : J.Adj a w) (no : NoCut (J⊔edge a b)) (sparse : SparseAt (J⊔edge a b) r)
      (big : 2<Q.card) : ∃ z,J.Adj w z ∧ z≠a ∧ z≠b := by
    have nc := (wing_odd jc q aQ bQ aw no sparse).1
    have size : 2<Fintype.card ↥Q := by simpa only [Fintype.card_coe]
    obtain ⟨i,j,wi,wj,ij⟩ := block_neighbors (side J Q) (q.connectedL jc) size nc ⟨w,q.both.1⟩
    by_cases ia : i.val=a
    · exact ⟨j,wj,fun h => ij (Subtype.ext (ia.trans h.symm)),fun h => bQ (h ▸ j.property)⟩
    · exact ⟨i,wi,ia,fun h => bQ (h ▸ i.property)⟩
  by_cases big : 2<S.card
  · exact sideThird s xs ys xw block sp big
  have count := card_union_add_card_inter S T
  rw [s.cover,s.meet,card_univ,card_singleton] at count
  have swap : J⊔edge y x=J⊔edge x y := by rw [edge_comm y x]
  obtain ⟨z,wz,zy,zx⟩ := sideThird s.flip yt xt wy.symm (swap ▸ block) (swap ▸ sp) (by omega)
  exact ⟨z,wz,zx,zy⟩

/-- A shortest-path spanning tree can take both outward spokes while
branching at the seam. The third incident edge goes toward the root when
the seam is not the root. -/
theorem branching_layer_tree {J : SimpleGraph V} (jc : J.Connected) {r w x y : V}
    (xw : J.Adj x w) (wy : J.Adj w y)
    (dx : J.dist x r=J.dist w r+1) (dy : J.dist y r=J.dist w r+1)
    (two : ∃ i j,J.Adj r i ∧ J.Adj r j ∧ i≠j)
    (extra : w=r → ∃ z,J.Adj w z ∧ z≠x ∧ z≠y) (odd : Bool) :
    ∃ M≤J, M.IsTree ∧ r∉leaves M ∧ M.Adj x w ∧ M.Adj y w ∧
      (∃ z,M.Adj w z ∧ z≠x ∧ z≠y) ∧
      ∀ {i j}, M.Adj i j → (i∈parity J r odd ↔ j∉parity J r odd) := by
  classical
  let p (i : V) := if i=x ∨ i=y then w else if h : i=r then r else (Graffiti169.exists_predecessor J jc r i h).choose
  have pred (i : V) (ir : i≠r) : J.Adj i (p i) ∧ J.dist i r=J.dist (p i) r+1 := by
    by_cases tip : i=x ∨ i=y
    · rw [show p i=w from if_pos tip]
      exact tip.elim (fun h => h ▸ ⟨xw,dx⟩) (fun h => h ▸ ⟨wy.symm,dy⟩)
    · simpa [p,tip,ir] using (Graffiti169.exists_predecessor J jc r i ir).choose_spec
  obtain ⟨M,mj,tr,cross,take,star⟩ := predecessor_tree J jc r odd p pred
  have nr {a : V} (d : J.dist a r=J.dist w r+1) : a≠r := by
    rintro rfl
    rw [dist_self] at d
    omega
  have mx : M.Adj x w := by simpa [p] using take x (nr dx)
  have my : M.Adj y w := by simpa [p] using take y (nr dy)
  obtain ⟨i,j,ri,rj,ne⟩ := two
  refine ⟨M,mj,tr,fun h => ne (leaf_unique M h (star i ri) (star j rj)),mx,my,?_,cross⟩
  by_cases wr : w=r
  · obtain ⟨z,wz,zx,zy⟩ := extra wr
    exact ⟨z,wr ▸ star z (wr ▸ wz),zx,zy⟩
  · have d := (pred w wr).2
    exact ⟨p w,take w wr,fun h => by rw [h] at d; omega,fun h => by rw [h] at d; omega⟩

/-- The actual horizontal cut gives a branching tree with both spokes and
an internal root, including the depth-one case. -/
theorem cut_layer_tree {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T) (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S)
    (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y) (r : ↥S)
    (block : NoCut (J⊔edge x y)) (sp : SparseAt (J⊔edge x y) r.val)
    (flat : (J⊔edge x y).dist x r.val=(J⊔edge x y).dist y r.val) (odd : Bool) :
    ∃ M≤J, M.IsTree ∧ r.val∉leaves M ∧ M.Adj x w ∧ M.Adj y w ∧
      (∃ z,M.Adj w z ∧ z≠x ∧ z≠y) ∧
      ∀ {i j}, M.Adj i j → (i∈parity J r.val odd ↔ j∉parity J r.val odd) := by
  obtain ⟨_,dx,dy⟩ := seam_layers jc s yt wy old r flat
  have nr {v : V} (h : J.dist v r.val=J.dist w r.val+1) : r.val≠v := by
    intro eq
    rw [←eq,dist_self] at h
    omega
  have same {j : V} (e : (J⊔edge x y).Adj r.val j) : J.Adj r.val j := by
    rcases e with e|e
    · exact e
    rcases ((edge_adj ..).mp e).1 with p|p
    · exact (nr dx p.1).elim
    · exact (nr dy p.1).elim
  obtain ⟨i,j,ri,rj,ij⟩ := block_neighbors (J⊔edge x y) (jc.mono le_sup_left) (by omega) block r.val
  exact branching_layer_tree jc xw wy dx dy ⟨i,j,same ri,same rj,ij⟩
    (fun _ => third_seam_neighbor jc hn s xs xt yt ys xw wy block sp) odd

#print axioms third_seam_neighbor
#print axioms branching_layer_tree
#print axioms cut_layer_tree
end Minimal180.CutGain
