import SixSingletonQ2OriginalLabel189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_closed from AdjacentCutFiveActual189
open private Cmp from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000

abbrev Arow (j : Vertex) : Prop := j=7 ∨ j=8 ∨ j=0 ∨ j=3 ∨ j=4 ∨ j=5
abbrev Brow (j : Vertex) : Prop := j=6 ∨ j=8 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5

theorem tag_symm : ∀ i j : Vertex,tag i j=tag j i := by decide
private theorem aRowTag : ∀ j : Vertex,Arow j → tag 6 j=.fixed := by decide
private theorem bRowTag : ∀ j : Vertex,Brow j → tag 7 j=.fixed := by decide
private theorem sRowTag : ∀ j : Vertex,(j=6 ∨ j=7) → tag 8 j=.fixed := by decide
private theorem xRowTag : ∀ j : Vertex, j≠0 →
    (j=6 ∨ j.val< 6 ∨ j=9 ∨ j=10 ∨ j=14 ∨ j=15) → tag 0 j≠.forb := by decide
private theorem yRowTag : ∀ i j : Vertex,(i=1 ∨ i=2) → j≠i →
    (j=7 ∨ j.val< 6 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15) → tag i j≠.forb := by decide
private theorem cRowTag : ∀ i j : Vertex,(i=3 ∨ i=4 ∨ i=5) → j≠i →
    (j=6 ∨ j=7 ∨ j.val< 6 ∨ j=14 ∨ j=15) → tag i j≠.forb := by decide
private theorem darkRowTag : ∀ i j : Vertex,9 ≤ i.val → 9 ≤ j.val → i≠j → tag i j≠.forb := by decide

theorem q2_vis (F : SixVisibleData G D s) (P : OriginalLabel D s) (i : Vertex) :
    P.e i∈Vis D ↔ i.val< 6 := by
  rw [←F.visiblePart]
  simp only [mem_union,P.mA,P.mB,P.mC]
  revert i
  decide

theorem q2_dark (F : SixVisibleData G D s) (P : OriginalLabel D s) (i : Vertex) :
    P.e i∈Dark D ↔ 9 ≤ i.val := by
  rw [←F.darkPart]
  simp only [mem_union,P.mL,P.mR,P.mW]
  revert i
  decide

theorem q2_adj_a (F : SixVisibleData G D s) (P : OriginalLabel D s) {j : Vertex}
    (adj : G.Adj a (P.e j)) : Arow j := by
  rcases F.cover (P.e j) with ja|jb|js|jv|jd
  · exact (adj.ne ja.symm).elim
  · exact .inl (P.e.injective (jb.trans P.bEq.symm))
  · exact .inr (.inl (P.e.injective (js.trans P.sEq.symm)))
  · rw [←F.visiblePart] at jv
    rcases mem_union.mp jv with h|h
    · rcases mem_union.mp h with u|u
      · exact .inr (.inr (.inl ((P.mA j).mp u)))
      exact ((F.eB _ u).2 adj).elim
    exact .inr (.inr (.inr ((P.mC j).mp h)))
  exact ((mem_sdiff.mp jd).2 (mem_filter.mpr ⟨(mem_sdiff.mp jd).1,.inl adj⟩)).elim

theorem q2_adj_b (F : SixVisibleData G D s) (P : OriginalLabel D s) {j : Vertex}
    (adj : G.Adj b (P.e j)) : Brow j := by
  rcases F.cover (P.e j) with ja|jb|js|jv|jd
  · exact .inl (P.e.injective (ja.trans P.aEq.symm))
  · exact (adj.ne jb.symm).elim
  · exact .inr (.inl (P.e.injective (js.trans P.sEq.symm)))
  · rw [←F.visiblePart] at jv
    rcases mem_union.mp jv with h|h
    · rcases mem_union.mp h with u|u
      · exact ((F.eA _ u).2 adj).elim
      rcases (P.mB j).mp u with t|t
      · exact .inr (.inr (.inl t))
      exact .inr (.inr (.inr (.inl t)))
    exact .inr (.inr (.inr (.inr ((P.mC j).mp h))))
  exact ((mem_sdiff.mp jd).2 (mem_filter.mpr ⟨(mem_sdiff.mp jd).1,.inr adj⟩)).elim

theorem q2_adj_s_original (F : SixVisibleData G D s) {u : V} (edge : G.Adj s u) : u=a ∨ u=b := by
  have no (h : u∈Shore D) : False := by
    rcases shore_closed D u h s edge.symm with ja|jb|js
    · exact F.sa.ne ja
    · exact F.sb.ne jb
    exact F.sOff js
  rcases F.cover u with ja|jb|js|jv|jd
  · exact .inl ja
  · exact .inr jb
  · exact (edge.ne js.symm).elim
  · exact (no (vis_sub D jv)).elim
  exact (no (mem_sdiff.mp jd).1).elim

private theorem q2_adj_x_tag (F : SixVisibleData G D s) (P : OriginalLabel D s) {j : Vertex}
    (edge : G.Adj (P.e 0) (P.e j)) : tag 0 j≠.forb := by
  have c := F.aBound _ ((P.mA 0).mpr rfl) ((mem_neighborFinset _ _ _).mpr edge)
  apply xRowTag _ (fun e=>edge.ne (congrArg P.e e.symm))
  rcases mem_insert.mp c with k|h
  · exact .inl (P.e.injective (k.trans P.aEq.symm))
  rcases mem_union.mp h with q|q
  · rcases mem_union.mp q with k|k
    · exact .inr (.inl ((q2_vis F P j).mp (mem_filter.mp k).1))
    have k' := (P.mL j).mp (mem_filter.mp k).1
    exact .inr (.inr (k'.elim Or.inl (fun l=>.inr (.inl l))))
  exact .inr (.inr (.inr (.inr ((P.mW j).mp (mem_filter.mp q).1))))

private theorem q2_adj_y_tag (F : SixVisibleData G D s) (P : OriginalLabel D s) {i j : Vertex}
    (ij : i=1 ∨ i=2) (edge : G.Adj (P.e i) (P.e j)) : tag i j≠.forb := by
  have c := F.bBound _ ((P.mB i).mpr ij) ((mem_neighborFinset _ _ _).mpr edge)
  apply yRowTag _ _ ij (fun e=>edge.ne (congrArg P.e e.symm))
  rcases mem_insert.mp c with k|h
  · exact .inl (P.e.injective (k.trans P.bEq.symm))
  rcases mem_union.mp h with q|q
  · rcases mem_union.mp q with k|k
    · exact .inr (.inl ((q2_vis F P j).mp (mem_filter.mp k).1))
    have k' := (P.mR j).mp (mem_filter.mp k).1
    rcases k' with t|t|t
    · exact .inr (.inr (.inl t))
    · exact .inr (.inr (.inr (.inl t)))
    exact .inr (.inr (.inr (.inr (.inl t))))
  exact .inr (.inr (.inr (.inr (.inr ((P.mW j).mp (mem_filter.mp q).1)))))

private theorem q2_adj_c_tag (F : SixVisibleData G D s) (P : OriginalLabel D s) {i j : Vertex}
    (ij : i=3 ∨ i=4 ∨ i=5) (edge : G.Adj (P.e i) (P.e j)) : tag i j≠.forb := by
  have c := F.commonBound _ ((P.mC i).mpr ij) ((mem_neighborFinset _ _ _).mpr edge)
  apply cRowTag _ _ ij (fun e=>edge.ne (congrArg P.e e.symm))
  rcases mem_insert.mp c with k|h
  · exact .inl (P.e.injective (k.trans P.aEq.symm))
  rcases mem_insert.mp h with k|h
  · exact .inr (.inl (P.e.injective (k.trans P.bEq.symm)))
  rcases mem_union.mp h with k|k
  · exact .inr (.inr (.inl ((q2_vis F P j).mp (mem_filter.mp k).1)))
  exact .inr (.inr (.inr ((P.mW j).mp (mem_filter.mp k).1)))

theorem q2_original_allowed (F : SixVisibleData G D s) (P : OriginalLabel D s) :
    ∀ i j : Vertex, G.Adj (P.e i) (P.e j) → tag i j≠.forb := by
  have prefix_case (i j : Vertex) (p : i.val< 9) (h : G.Adj (P.e i) (P.e j)) : tag i j≠.forb := by
    fin_cases i
    all_goals dsimp at p
    · exact q2_adj_x_tag F P h
    · exact q2_adj_y_tag F P (.inl rfl) h
    · exact q2_adj_y_tag F P (.inr rfl) h
    · exact q2_adj_c_tag F P (.inl rfl) h
    · exact q2_adj_c_tag F P (.inr (.inl rfl)) h
    · exact q2_adj_c_tag F P (.inr (.inr rfl)) h
    · change G.Adj (P.e 6) (P.e j) at h
      change tag 6 j≠.forb
      have e : G.Adj a (P.e j) := by simpa only [P.aEq] using h
      rw [aRowTag _ (q2_adj_a F P e)]
      decide
    · change G.Adj (P.e 7) (P.e j) at h
      change tag 7 j≠.forb
      have e : G.Adj b (P.e j) := by simpa only [P.bEq] using h
      rw [bRowTag _ (q2_adj_b F P e)]
      decide
    · change G.Adj (P.e 8) (P.e j) at h
      change tag 8 j≠.forb
      have e : G.Adj s (P.e j) := by simpa only [P.sEq] using h
      have q := q2_adj_s_original F e
      have j67 : j=6 ∨ j=7 := q.imp (fun ja=>P.e.injective (ja.trans P.aEq.symm))
        (fun jb=>P.e.injective (jb.trans P.bEq.symm))
      rw [sRowTag _ j67]
      decide
    all_goals omega
  intro i j h
  by_cases pi : i.val< 9
  · exact prefix_case i j pi h
  by_cases pj : j.val< 9
  · rw [tag_symm]
    exact prefix_case j i pj h.symm
  exact darkRowTag _ _ (Nat.le_of_not_gt pi) (Nat.le_of_not_gt pj) (fun e=>h.ne (congrArg P.e e))

end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
