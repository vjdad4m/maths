import SharedHighSeparation

open private lowLabel FullPair.low FullPair.low_degree FullPair.low_edge FullPair.low_stays
  FullPair.high_side FullPair.degree_three_off singleton_high_adj from SharedHighSeparation
open private pair_low_cases from FourBlockIntegration

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private theorem FullPair.off_opposite_low (P : FullPair G) {x : V} {s : Bool}
    (xp : x ∈ pairPorts P) (xs : G.Adj x (FullPair.low P s)) :
    ¬ G.Adj x (FullPair.low P (!s)) := by
  obtain ⟨t,_,off⟩ := FullPair.high_side P xp
  cases s <;> cases t
  · exact off
  · exact (off xs).elim
  · exact (off xs).elim
  · exact off

private def sevenEdges (b : Bool) : List (Fin 7 × Fin 7) :=
  [(0,1),(1,2),(0,3),(3,4),(2,5),(5,6)] ++ if b then [(0,5)] else []

private def sevenAdj (b : Bool) (i j : Fin 7) : Bool :=
  (sevenEdges b).contains (i,j) || (sevenEdges b).contains (j,i)

private def picked (b : Bool) : Fin 6 → Fin 7 :=
  if b then ![0,1,3,4,5,6] else ![0,1,2,3,4,5]

private theorem picked_inj (b : Bool) : Function.Injective (picked b) := by
  unfold Function.Injective
  revert b
  decide

private theorem picked_earlier :
    ∀ (b : Bool) (i : Fin 6), i ≠ 0 →
      ∃ j : Fin 6, sevenAdj b (picked b i) (picked b j) = true ∧ j < i ∧
        ∀ k : Fin 6, sevenAdj b (picked b i) (picked b k) = true → k < i → k = j := by decide

variable (F : FourBlockPacking G)

set_option maxHeartbeats 3000000 in
/-- If a paired high is shared, a singleton-owned high of that pair
must lie in the same half. The two opposite-half configurations give
different induced six-vertex trees according to the edge between the highs. -/
theorem FourBlockPacking.no_owned_high_opposite_shared_high
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (bound : Catalogue.treeNumber G ≤ 5) {x y : V} (p : Bool)
    (xp : x ∈ pairPorts F.depleted) (xq : x ∈ pairPorts F.terminal)
    (yp : y ∈ pairPorts F.depleted)
    (ys : y ∈ singletonPorts F.first ∪ singletonPorts F.second)
    (xa : G.Adj x (FullPair.low F.depleted p))
    (ya' : G.Adj y (FullPair.low F.depleted (!p))) : False := by
  let P := F.depleted
  let Q := F.terminal
  have triple := F.no_paired_pair_singleton_triple_overlap pHigh bound
  have yNoQ : y ∉ pairPorts Q := fun yq => Set.disjoint_left.mp triple ⟨yp,yq⟩ ys
  have xyNe : x ≠ y := fun e => yNoQ (e ▸ xq)
  have yOutside : y ∉ labelRegion Q.f := by
    rintro ⟨i,eq⟩
    by_cases hi : 2 ≤ i.val
    · exact yNoQ ⟨i,hi,eq⟩
    · rcases pair_low_cases i (by omega) with rfl|rfl
      · exact pHigh y yp (eq ▸ Q.degree 0 (by decide))
      · exact pHigh y yp (eq ▸ Q.degree 1 (by decide))
  have qHigh (v : V) (h : v ∈ pairPorts Q) := F.highDegree v (Or.inr h)
  have zExists : ∃ z : V, G.degree z = 3 ∧ z ∉ labelRegion P.f ∧
      z ∉ labelRegion Q.f ∧ G.Adj y z := by
    rcases ys with ys|ys
    · exact ⟨F.first.f 0,F.first.degree,
        FullPair.degree_three_off P F.first.degree (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 2))
          (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 3)) pHigh,
        FullPair.degree_three_off Q F.first.degree (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 4))
          (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 5)) qHigh,singleton_high_adj F.first ys⟩
    · exact ⟨F.second.f 0,F.second.degree,
        FullPair.degree_three_off P F.second.degree (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 2))
          (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 3)) pHigh,
        FullPair.degree_three_off Q F.second.degree (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 4))
          (F.lowDistinct.ne (by decide : (1 : Fin 6) ≠ 5)) qHigh,singleton_high_adj F.second ys⟩
  obtain ⟨z,zDegree,zOffP,zOffQ,yz⟩ := zExists
  obtain ⟨q,xb,xbOff⟩ := FullPair.high_side Q xq
  have xzOff := F.shared_paired_high_no_outside_neighbor pHigh bound xp xq zOffP zOffQ
  have xaOff := P.off_opposite_low xp xa
  have yaOff : ¬ G.Adj y (FullPair.low P p) := by
    have other := P.off_opposite_low yp ya'
    cases p <;> exact other
  have qLowOutsideP (s : Bool) : FullPair.low Q s ∉ labelRegion P.f := by
    apply FullPair.degree_three_off P (FullPair.low_degree Q s) _ _ pHigh
    · cases s
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 2)
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 2)
    · cases s
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 3)
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 3)
  have crossOff (r s : Bool) : ¬ G.Adj (FullPair.low P r) (FullPair.low Q s) :=
    fun h => qLowOutsideP s (FullPair.low_stays P r h)
  have crossOff' (r s : Bool) : ¬ G.Adj (FullPair.low Q s) (FullPair.low P r) :=
    fun h => crossOff r s h.symm
  have yqOff (s : Bool) : ¬ G.Adj y (FullPair.low Q s) :=
    fun h => yOutside (FullPair.low_stays Q s h.symm)
  have yqOff' (s : Bool) : ¬ G.Adj (FullPair.low Q s) y := fun h => yqOff s h.symm
  have zpOff (s : Bool) : ¬ G.Adj z (FullPair.low P s) :=
    fun h => zOffP (FullPair.low_stays P s h.symm)
  have zpOff' (s : Bool) : ¬ G.Adj (FullPair.low P s) z := fun h => zpOff s h.symm
  have zqOff (s : Bool) : ¬ G.Adj z (FullPair.low Q s) :=
    fun h => zOffQ (FullPair.low_stays Q s h.symm)
  have zqOff' (s : Bool) : ¬ G.Adj (FullPair.low Q s) z := fun h => zqOff s h.symm
  have xNp (s : Bool) : x ≠ FullPair.low P s := fun h => pHigh x xp (h.symm ▸ FullPair.low_degree P s)
  have xNq (s : Bool) : x ≠ FullPair.low Q s := fun h => pHigh x xp (h.symm ▸ FullPair.low_degree Q s)
  have yNp (s : Bool) : FullPair.low P s ≠ y := fun h => pHigh y yp (h ▸ FullPair.low_degree P s)
  have yNq (s : Bool) : FullPair.low Q s ≠ y := fun h => yOutside ⟨lowLabel s,h⟩
  have zNp (s : Bool) : FullPair.low P s ≠ z := fun h => zOffP ⟨lowLabel s,h⟩
  have zNq (s : Bool) : FullPair.low Q s ≠ z := fun h => zOffQ ⟨lowLabel s,h⟩
  have xNz : x ≠ z := fun h => pHigh x xp (h.symm ▸ zDegree)
  have crossNe (r s : Bool) : FullPair.low P r ≠ FullPair.low Q s := fun h =>
    qLowOutsideP s ⟨lowLabel r,h⟩
  have aa := FullPair.low_edge P p
  have bb := FullPair.low_edge Q q
  let L := [x,FullPair.low P p,FullPair.low P (!p),FullPair.low Q q,FullPair.low Q (!q),y,z]
  have nd : L.Nodup := by
    simp [L,xNp,xNq,yNp,yNq,zNp,zNq,xNz,xyNe,yz.ne,crossNe,aa.ne,bb.ne]
  let f : Fin 7 ↪ V := ⟨L.get,fun _ _ e => nd.get_inj_iff.mp e⟩
  have v0 : f 0 = x := rfl
  have v1 : f 1 = FullPair.low P p := rfl
  have v2 : f 2 = FullPair.low P (!p) := rfl
  have v3 : f 3 = FullPair.low Q q := rfl
  have v4 : f 4 = FullPair.low Q (!q) := rfl
  have v5 : f 5 = y := rfl
  have v6 : f 6 = z := rfl
  have xaOff' : ¬ G.Adj (FullPair.low P (!p)) x := fun h => xaOff h.symm
  have xbOff' : ¬ G.Adj (FullPair.low Q (!q)) x := fun h => xbOff h.symm
  have yaOff' : ¬ G.Adj (FullPair.low P p) y := fun h => yaOff h.symm
  have xzOff' : ¬ G.Adj z x := fun h => xzOff h.symm
  have chart (i j : Fin 7) : G.Adj (f i) (f j) ↔ sevenAdj (decide (G.Adj x y)) i j = true := by
    have xys : G.Adj y x ↔ G.Adj x y := G.adj_comm _ _
    by_cases edge : G.Adj x y <;> fin_cases i <;> fin_cases j <;>
      simp [v0,v1,v2,v3,v4,v5,v6,sevenAdj,sevenEdges,xa,xa.symm,xaOff,xaOff',
        xb,xb.symm,xbOff,xbOff',ya',ya'.symm,yaOff,yaOff',yz,yz.symm,xzOff,xzOff',
        aa,aa.symm,bb,bb.symm,crossOff,crossOff',yqOff,yqOff',zpOff,zpOff',zqOff,zqOff',
        xys,edge] <;>
      first | decide | exact xa | exact xa.symm | exact ya' | exact ya'.symm
  let flag := decide (G.Adj x y)
  let g := (⟨picked flag,picked_inj flag⟩ : Fin 6 ↪ Fin 7).trans f
  have six := Catalogue.six_le_treeNumber_of_ordering (G := G) g (by
    intro i hi
    obtain ⟨j,ij,lt,only⟩ := picked_earlier flag i hi
    exact ⟨j,(chart _ _).mpr ij,lt,fun k e l => only k ((chart _ _).mp e) l⟩)
  omega

#print axioms FourBlockPacking.no_owned_high_opposite_shared_high

end Graffiti199Depleted
