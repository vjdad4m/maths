import DegreeFiveEightBridgeRoutes189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private two_walk_middle from DistanceTwoCut189
open private cut_not_adj not_common distance_to_b_ge_three_at_no_bridge from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem b_gateway_from_a_port_without_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (foreignFour : S.foreignA.card=4)
    (noBridge : ¬portBridge S) {x : V} (xL : x∈S.L) (ax : G.Adj a x) :
    ∃ u∈S.L,∃ z∈S.L,¬G.Adj a u ∧ ¬G.Adj b u ∧ G.Adj b z ∧
      G.Adj x u ∧ G.Adj u z ∧ z∈DistanceTwo G x := by
  classical
  have k := distance_to_b_ge_three_at_no_bridge S hc far noBridge xL ax
  have j := (saturated_at_opposite_four S hc far even foreignFour xL ax).2 b
  have exact3 : G.dist x b=3 := by omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x b
  have len : p.length=3 := pl.trans exact3
  have route {x b : V} (p : G.Walk x b) (len : p.length=3) :
      ∃ u z,G.Adj x u ∧ G.Adj u z ∧ G.Adj z b := by
    cases p with
    | nil => simp at len
    | @cons x u b xu q =>
      have ql : q.length=2 := by simp only [length_cons] at len; omega
      obtain ⟨z,uz,zb⟩ := two_walk_middle q ql
      exact ⟨u,z,xu,uz,zb⟩
  obtain ⟨u,z,xu,uz,zb⟩ := route p len
  have bu : ¬G.Adj b u := by
    intro bu
    have n := G.dist_le (Walk.cons xu (Walk.cons bu.symm Walk.nil))
    simp only [length_cons,length_nil] at n
    omega
  have uL : u∈S.L := by
    rcases left_boundary S x xL u xu with eq|eq|h
    · exact (not_common far (eq ▸ uz) zb.symm).elim
    · exact (not_common far ax (eq ▸ xu).symm).elim
    exact h
  have zL : z∈S.L := by
    rcases left_boundary S u uL z uz with eq|eq|h
    · exact (cut_not_adj far (eq ▸ zb)).elim
    · exact (G.loopless b (eq ▸ zb)).elim
    exact h
  have au : ¬G.Adj a u := fun au=>noBridge ⟨u,uL,z,zL,au,uz,zb.symm⟩
  have ne : x≠z := fun e=>not_common far ax (e.symm ▸ zb.symm)
  have no : ¬G.Adj x z := fun xz=>noBridge ⟨x,xL,z,zL,ax,xz,zb.symm⟩
  exact ⟨u,uL,z,zL,au,bu,zb.symm,xu,uz,d2 hc ne no xu uz⟩

theorem no_bridge_port_nonports_complete (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (foreignFour : S.foreignA.card=4)
    (noBridge : ¬portBridge S)
    (near : ∀ u∈S.L,¬G.Adj a u → ¬G.Adj b u → ∃ x∈S.localA,G.Adj x u) :
    CompleteOn G S.localA ∧
      ∀ p∈S.localA,∀ u∈S.L,¬G.Adj a u → ¬G.Adj b u → G.Adj p u := by
  classical
  have cl : CompleteOn G S.localA := by
    intro p pp q qp pq
    obtain ⟨pL,ap⟩ := mem_filter.mp pp
    obtain ⟨qL,aq⟩ := mem_filter.mp qp
    obtain ⟨u,_,z,zL,_,_,bz,_,_,z2⟩ :=
      b_gateway_from_a_port_without_bridge S hc far even foreignFour noBridge pL ap
    apply Classical.byContradiction
    intro no
    have q2 := d2 hc pq no ap.symm aq
    exact not_common far aq
      ((singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zL qL z2 q2) ▸ bz)
  refine ⟨cl,?_⟩
  intro p pp u uL au bu
  obtain ⟨q,qp,qu⟩ := near u uL au bu
  by_cases pq : p=q
  · exact pq.symm ▸ qu
  obtain ⟨pL,ap⟩ := mem_filter.mp pp
  obtain ⟨_,_,z,zL,_,_,bz,_,_,z2⟩ :=
    b_gateway_from_a_port_without_bridge S hc far even foreignFour noBridge pL ap
  apply Classical.byContradiction
  intro no
  have pu : p≠u := fun e=>au (e ▸ ap)
  have u2 := d2 hc pu no (cl p pp q qp pq) qu
  exact bu
    ((singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zL uL z2 u2) ▸ bz)

#print axioms b_gateway_from_a_port_without_bridge
#print axioms no_bridge_port_nonports_complete
end Graffiti189LongestPath.CrossSaturation.Split.Five
