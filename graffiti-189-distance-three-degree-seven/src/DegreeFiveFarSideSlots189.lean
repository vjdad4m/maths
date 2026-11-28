import DegreeFiveSevenBridgeContext189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private two_walk_middle from DistanceTwoCut189
open private not_common cut_not_adj from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem nonport_a_neighbor (hc : G.Connected) (far : 3≤G.dist a b)
    {x : V} (xl : x∈S.L) (near : x∈DistanceTwo G a) :
    ∃ p∈S.localA,G.Adj p x := by
  have dep : G.dist a x=2 := by simpa [DistanceTwo] using near
  obtain ⟨p,n⟩ := hc.exists_walk_length_eq_dist a x
  obtain ⟨q,aq,qx⟩ := two_walk_middle p (n.trans dep)
  rcases left_boundary S x xl q qx.symm with qa|qb|ql
  · exact (G.loopless a (qa ▸ aq)).elim
  · exact (cut_not_adj far (qb ▸ aq)).elim
  exact ⟨q,mem_filter.mpr ⟨ql,aq⟩,qx⟩

theorem two_charges_force_full_on_a_and_nonports (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6) (foreign : S.foreignA.card=3)
    (visible : farNonports S.L a b G⊆secondA G S.L a)
    {p : V} (pa : p∈S.localA) {W : Finset V} (W2 : W.card=2)
    (wg : W⊆insert b (S.L.filter (G.Adj b))) (charge : W⊆DistanceTwo G p) :
    (∀ q∈S.localA,p≠q → G.Adj p q) ∧ (∀ q∈farNonports S.L a b G,G.Adj p q) := by
  obtain ⟨pl,ap⟩ := mem_filter.mp pa
  have fresh (q : V) (ql : q∈S.L) (qb : ¬G.Adj b q) (q2 : q∈DistanceTwo G p) : False := by
    have qw : q∉W := by
      intro qW
      rcases mem_insert.mp (wg qW) with h|h
      · exact S.leftOff.2 (h ▸ ql)
      exact qb (mem_filter.mp h).2
    have wh : W⊆insert b S.L := by
      intro w ww
      rcases mem_insert.mp (wg ww) with e|e
      · exact mem_insert.mpr (.inl e)
      exact mem_insert_of_mem (mem_filter.mp e).1
    have lead := local_distance_two_at_foreign_three S hc even foreign pl ap
      (insert_subset_iff.mpr ⟨mem_insert_of_mem ql,wh⟩) (insert_subset_iff.mpr ⟨q2,charge⟩)
    rw [card_insert_of_not_mem qw,W2] at lead
    omega
  have clique (q : V) (qa : q∈S.localA) (pq : p≠q) : G.Adj p q := by
    obtain ⟨ql,aq⟩ := mem_filter.mp qa
    apply Classical.byContradiction
    intro no
    exact fresh q ql (not_common far aq) (d2 hc pq no ap.symm aq)
  refine ⟨clique,?_⟩
  intro q qi
  obtain ⟨ql,aq,bq⟩ := mem_filter.mp qi
  apply Classical.byContradiction
  intro no
  have pq : p≠q := fun eq=>aq (eq ▸ ap)
  obtain ⟨r,ra,rq⟩ := nonport_a_neighbor S hc far ql (mem_inter.mp (visible qi)).2
  have pr : p≠r := fun eq=>no (eq.symm ▸ rq)
  exact fresh q ql bq (d2 hc pq no (clique r ra pr) rq)

theorem left_port_partition (_far : 3≤G.dist a b) :
    S.localA∪(S.L.filter (G.Adj b))∪farNonports S.L a b G=S.L := by
  classical
  ext w
  by_cases aa : G.Adj a w <;> by_cases bb : G.Adj b w <;>
    simp [Split.localA,farNonports,aa,bb]

theorem left_port_count (far : 3≤G.dist a b) :
    S.localA.card+(S.L.filter (G.Adj b)).card+(farNonports S.L a b G).card=S.L.card := by
  classical
  have ab : Disjoint S.localA (S.L.filter (G.Adj b)) := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  have all : Disjoint (S.localA∪S.L.filter (G.Adj b)) (farNonports S.L a b G) := by
    apply disjoint_left.mpr
    intro x h n
    obtain ⟨_,aa,bb⟩ := mem_filter.mp n
    exact (mem_union.mp h).elim (fun xa=>aa (mem_filter.mp xa).2)
      (fun xb=>bb (mem_filter.mp xb).2)
  have n := congrArg Finset.card (left_port_partition S far)
  rw [card_union_of_disjoint all,card_union_of_disjoint ab] at n
  exact n

#print axioms two_charges_force_full_on_a_and_nonports
#print axioms left_port_count
end Graffiti189LongestPath.CrossSaturation.Split.Five
