import SixSingletonQ2OriginalGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_closed from AdjacentCutFiveActual189
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB bal from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private predecessor_of_positive_dist from AdjacentCutFiveSixteenSingletonDepth189
open FiveAdjacent (depth label_degree label_even)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000

private def fixedDirection (i j : Vertex) : Prop :=
  (i=6 ∧ Arow j) ∨ (i=7 ∧ Brow j)

private instance (i j : Vertex) : Decidable (fixedDirection i j) := by
  unfold fixedDirection
  infer_instance

private theorem fixed_cases : ∀ i j : Vertex,tag i j=.fixed →
    fixedDirection i j ∨ fixedDirection j i := by decide

private theorem dir_graph (F : SixVisibleData G D s) (P : OriginalLabel D s) (ab : G.Adj a b)
    {i j : Vertex} (d : fixedDirection i j) : G.Adj (P.e i) (P.e j) := by
  rcases d with ⟨rfl,d⟩|⟨rfl,d⟩
  · rw [P.aEq]
    rcases d with d|d|d|d
    · rw [d,P.bEq]; exact ab
    · rw [d,P.sEq]; exact F.sa.symm
    · exact (F.eA _ ((P.mA _).mpr d)).1
    exact (F.common _ ((P.mC _).mpr d)).1
  · rw [P.bEq]
    rcases d with d|d|d|d|d
    · rw [d,P.aEq]; exact ab.symm
    · rw [d,P.sEq]; exact F.sb.symm
    · exact (F.eB _ ((P.mB _).mpr (.inl d))).1
    · exact (F.eB _ ((P.mB _).mpr (.inr d))).1
    exact (F.common _ ((P.mC _).mpr d)).2

private theorem q2_terminal_bridge (hc : G.Connected) {u t : V} (ud : u∈Dark D)
    (isTerminal : t=a ∨ t=b) (length : G.dist t u=2) :
    ∃ x∈Vis D,G.Adj t x ∧ G.Adj x u := by
  have d : G.dist u t=2 := by rw [dist_comm,length]
  obtain ⟨x,ux,step⟩ := predecessor_of_positive_dist hc (x:=u) (t:=t) (by omega)
  have xs : x∈Shore D := by
    obtain ⟨us,no⟩ := mem_sdiff.mp ud
    rcases shore_closed D u us x ux with e|e|e
    · exact (no (mem_filter.mpr ⟨us,.inl (e ▸ ux.symm)⟩)).elim
    · exact (no (mem_filter.mpr ⟨us,.inr (e ▸ ux.symm)⟩)).elim
    exact e
  have xt : G.dist t x=1 := by rw [dist_comm]; omega
  have tx := dist_eq_one_iff_adj.mp xt
  refine ⟨x,mem_filter.mpr ⟨xs,?_⟩,tx,ux.symm⟩
  rcases isTerminal with rfl|rfl
  · exact .inl tx
  exact .inr tx

private theorem aRowVis : ∀ j : Vertex,j.val < 6 → Arow j → j∈({0,3,4,5}:Finset Vertex) := by decide
private theorem bRowVis : ∀ j : Vertex,j.val < 6 → Brow j → j∈({1,2,3,4,5}:Finset Vertex) := by decide

theorem data_of_original (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (F : SixVisibleData G D s) (P : OriginalLabel D s) :
    Data (G.comap P.e) := by
  classical
  let H := G.comap P.e
  let iso := SimpleGraph.Iso.comap P.e G
  have degS : G.degree s≤2 := by
    have low : G.neighborFinset s⊆({a,b}:Finset V) := by
      intro u h
      simpa only [mem_insert,mem_singleton] using q2_adj_s_original F ((mem_neighborFinset _ _ _).mp h)
    have bound := card_le_card low
    simpa [card_neighborFinset_eq_degree,card_pair ab.ne] using bound
  have high (j : Vertex) (js : j≠8) : 6≤H.degree j := by
    have ne : P.e j≠s := fun e=>js (P.e.injective (e.trans P.sEq.symm))
    change 6≤(SimpleGraph.comap (⇑P.e.toEmbedding) G).degree j
    rw [label_degree iso]
    exact (degree _ _ ne).resolve_right (by omega)
  have caps (j : Vertex) : (EvenFrom H j).card≤7 := by
    change (EvenFrom (SimpleGraph.comap (⇑P.e.toEmbedding) G) j).card≤7
    rw [label_even iso hc]
    exact even (P.e j)
  have Lroot (j : Vertex) (jl : j=9 ∨ j=10) : H.Adj 0 j := by
    obtain ⟨w,wl,adj⟩ := F.rootsA _ ((P.mL j).mpr jl)
    obtain ⟨i,rfl⟩ := P.e.surjective w
    have e := (P.mA i).mp wl
    change G.Adj (P.e 0) (P.e j)
    exact e ▸ adj
  have Rroot (j : Vertex) (jr : j=11 ∨ j=12 ∨ j=13) : H.Adj 1 j ∨ H.Adj 2 j := by
    obtain ⟨w,wr,adj⟩ := F.rootsB _ ((P.mR j).mpr jr)
    obtain ⟨i,rfl⟩ := P.e.surjective w
    change G.Adj (P.e 1) (P.e j) ∨ G.Adj (P.e 2) (P.e j)
    rcases (P.mB i).mp wr with e|e
    · exact .inl (e ▸ adj)
    exact .inr (e ▸ adj)
  have dst (j : Vertex) (jw : j=14 ∨ j=15) : G.dist a (P.e j)=2 ∧ G.dist b (P.e j)=2 := by
    obtain ⟨h,q⟩ := mem_filter.mp ((P.mW j).mpr jw)
    have e := (mem_filter.mp h).2
    change min (G.dist a (P.e j)) (G.dist b (P.e j))=2 at q
    omega
  have dark (j : Vertex) (h : j=14 ∨ j=15) : P.e j∈Dark D := (q2_dark F P j).mpr (by rcases h with rfl|rfl <;> decide)
  have AP (j : Vertex) (h : j=14 ∨ j=15) : ∃ i∈({0,3,4,5}:Finset Vertex),H.Adj i j := by
    obtain ⟨x,xv,ax,xj⟩ := q2_terminal_bridge hc (dark j h) (.inl rfl) (dst j h).1
    obtain ⟨i,rfl⟩ := P.e.surjective x
    exact ⟨i,aRowVis i ((q2_vis F P i).mp xv) (q2_adj_a F P ax),xj⟩
  have BP (j : Vertex) (h : j=14 ∨ j=15) : ∃ i∈({1,2,3,4,5}:Finset Vertex),H.Adj i j := by
    obtain ⟨x,xv,bx,xj⟩ := q2_terminal_bridge hc (dark j h) (.inr rfl) (dst j h).2
    obtain ⟨i,rfl⟩ := P.e.surjective x
    exact ⟨i,bRowVis i ((q2_vis F P i).mp xv) (q2_adj_b F P bx),xj⟩
  refine ⟨q2_original_allowed F P,?_,high,caps,Lroot 9 (.inl rfl),Lroot 10 (.inr rfl),
    Rroot 11 (.inl rfl),Rroot 12 (.inr (.inl rfl)),Rroot 13 (.inr (.inr rfl)),
    AP 14 (.inl rfl),AP 15 (.inr rfl),BP 14 (.inl rfl),BP 15 (.inr rfl)⟩
  intro i j h
  change G.Adj (P.e i) (P.e j)
  rcases fixed_cases i j h with d|d
  · exact dir_graph F P ab d
  exact (dir_graph F P ab d).symm

#print axioms data_of_original
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
