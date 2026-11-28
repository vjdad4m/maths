import DegreeFiveSevenBridge189
import DegreeFiveSurplus189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary from AdjacentCut189
open private d2 foreign_subset from CrossSaturation189
open private not_common secondA_right_and_left_le_five from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

noncomputable def farNonports (K : Finset V) (a b : V) (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := K.filter (fun x=>¬G.Adj a x ∧ ¬G.Adj b x)

noncomputable def visibleBPorts (K : Finset V) (a b : V) (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := by
  classical
  exact K.filter (fun x=>G.Adj b x ∧ ∃ p∈K,G.Adj a p ∧ G.Adj p x)

theorem local_distance_two_at_foreign_three (hc : G.Connected)
    (even : ∀ z,(EvenFrom G z).card≤6) (three : S.foreignA.card=3)
    {p : V} (pl : p∈S.L) (ap : G.Adj a p) {W : Finset V}
    (whereW : W⊆insert b S.L) (charge : W⊆DistanceTwo G p) : W.card≤2 := by
  classical
  have dis : Disjoint S.foreignA W := by
    apply disjoint_left.mpr
    intro x xf xw
    have xr := (mem_filter.mp xf).1
    exact (mem_insert.mp (whereW xw)).elim (fun e=>S.rightOff.2 (e ▸ xr))
      (fun xl=>disjoint_left.mp S.dis xl xr)
  have near : S.foreignA⊆DistanceTwo G p := fun _ x=>foreign_subset S hc pl ap x
  have n := (card_le_card (union_subset near charge)).trans (distanceTwo_le_of_even 5 p (even p))
  rw [card_union_of_disjoint dis,three] at n
  omega

theorem high_far_port_shore_universal_at_five (far : 3≤G.dist a b)
    (sz : S.L.card=5) {p : V} (pl : p∈S.L) (hp : 5≤G.degree p)
    (port : G.Adj a p ∨ G.Adj b p) :
    ∀ q∈S.L,p≠q → G.Adj p q := by
  classical
  have step (c : V) (sub : G.neighborFinset p⊆insert c (S.L.erase p)) :
      ∀ q∈S.L,p≠q → G.Adj p q := by
    have cap := card_insert_le c (S.L.erase p)
    rw [card_erase_of_mem pl,sz] at cap
    have eq : G.neighborFinset p=insert c (S.L.erase p) :=
      eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; omega)
    intro q ql nq
    exact (mem_neighborFinset G p q).mp
      (eq.symm ▸ mem_insert_of_mem (mem_erase.mpr ⟨nq.symm,ql⟩))
  rcases port with ap|bp
  · apply step a
    intro q qm
    have pq := (mem_neighborFinset G p q).mp qm
    rcases left_boundary S p pl q pq with e|e|ql
    · exact mem_insert.mpr (.inl e)
    · exact (not_common far ap (e ▸ pq.symm)).elim
    exact mem_insert_of_mem (mem_erase.mpr ⟨pq.ne.symm,ql⟩)
  apply step b
  intro q qm
  have pq := (mem_neighborFinset G p q).mp qm
  rcases left_boundary S p pl q pq with e|e|ql
  · exact (not_common far (e ▸ pq.symm) bp).elim
  · exact mem_insert.mpr (.inl e)
  exact mem_insert_of_mem (mem_erase.mpr ⟨pq.ne.symm,ql⟩)

theorem bridge_three_opposite_shell_cap (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (local3 : S.localA.card=3) (foreign4 : S.foreignA.card=4)
    (bridge : portBridge S) :
    farNonports S.R a b G⊆secondA G S.R a ∧
      (farNonports S.R a b G).card+(visibleBPorts S.R a b G).card≤3 ∧
      ((farNonports S.R a b G).card=3 →
        S.L.card=5 ∧ (secondA G S.R b).card≤2) := by
  classical
  let I := farNonports S.R a b G
  let W := visibleBPorts S.R a b G
  let P := S.L\S.localA
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have bridge' : portBridge S := ⟨x,xl,y,yl,ax,xy,by'⟩
  have ub := bridge_four_forces_universal S hc far even foreign4 xl ax xy by'
  have pSub : P⊆secondA G S.L a := by
    intro z zz
    obtain ⟨zl,za⟩ := mem_sdiff.mp zz
    have az : ¬G.Adj a z := fun az=>za (mem_filter.mpr ⟨zl,az⟩)
    have xz := (ub z zl).resolve_left (fun e=>az (e.symm ▸ ax))
    have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
    exact mem_inter.mpr ⟨zl,d2 hc ne az ax xz⟩
  have iSub : I⊆secondA G S.R a := by
    intro z zi
    obtain ⟨zr,az,bz⟩ := mem_filter.mp zi
    have bound := right_cover_of_mixed_opposite_four S hc far even foreign4 bridge' zr
    rcases mem_union.mp bound with pp|p
    · rcases mem_union.mp pp with p|p
      · exact (az (mem_filter.mp p).2).elim
      exact (bz (mem_filter.mp p).2).elim
    exact p
  have wSub : W⊆secondA G S.R a := by
    intro z zw
    obtain ⟨zr,bz,p,pr,ap,pz⟩ := mem_filter.mp zw
    have ne : a≠z := fun h=>S.rightOff.1 (h.symm ▸ zr)
    exact mem_inter.mpr ⟨zr,d2 hc ne (fun az=>not_common far az bz) ap pz⟩
  have dis : Disjoint I W := disjoint_left.mpr (fun v vi vw=>(mem_filter.mp vi).2.2 (mem_filter.mp vw).2.1)
  have iw := card_le_card (union_subset iSub wSub)
  rw [card_union_of_disjoint dis] at iw
  have p2 : 2≤P.card := by
    have count : P.card+S.localA.card=S.L.card := card_sdiff_add_card_eq_card (filter_subset _ _)
    apply Classical.byContradiction
    intro nope
    have low (p : V) (pa : p∈S.localA) : ¬5≤G.degree p := by
      obtain ⟨pl,ap⟩ := mem_filter.mp pa
      have sub : G.neighborFinset p⊆insert a (S.L.erase p) := by
        intro q qm
        have pq := (mem_neighborFinset G p q).mp qm
        rcases left_boundary S p pl q pq with e|e|ql
        · exact mem_insert.mpr (.inl e)
        · exact (not_common far ap (e ▸ pq.symm)).elim
        exact mem_insert_of_mem (mem_erase.mpr ⟨pq.ne.symm,ql⟩)
      have n := (card_le_card sub).trans (card_insert_le a (S.L.erase p))
      rw [card_neighborFinset_eq_degree,card_erase_of_mem pl] at n
      omega
    obtain ⟨u,up,v,vp,uv⟩ := one_lt_card.mp (show 1<S.localA.card by omega)
    exact (degree u v uv).elim (low u up) (low v vp)
  have sem := secondA_right_and_left_le_five S even
  have pm := card_le_card pSub
  refine ⟨iSub,?_,?_⟩
  · change I.card+W.card≤3
    omega
  intro e
  change I.card=3 at e
  have pEq : P.card=2 := by omega
  have sum : P.card+S.localA.card=S.L.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have sz : S.L.card=5 := by omega
  have lowB : S.localA⊆secondA G S.L b := by
    intro p pp
    obtain ⟨pl,ap⟩ := mem_filter.mp pp
    have ne : p≠y := fun h=>not_common far (h ▸ ap) by'
    have py : G.Adj p y := (degree p y ne).elim
      (fun h=>high_far_port_shore_universal_at_five S far sz pl h (.inl ap) y yl ne)
      (fun h=>(high_far_port_shore_universal_at_five S far sz yl h (.inr by') p pl ne.symm).symm)
    have bp : b≠p := fun h=>S.leftOff.2 (h.symm ▸ pl)
    exact mem_inter.mpr ⟨pl,d2 hc bp (not_common far ap) by' py.symm⟩
  have db := card_le_card lowB
  have semB := secondA_right_and_left_le_five S.flip even
  change (secondA G S.L b).card+(secondA G S.R b).card≤5 at semB
  exact ⟨sz,by omega⟩

#print axioms local_distance_two_at_foreign_three
#print axioms bridge_three_opposite_shell_cap
end Graffiti189LongestPath.CrossSaturation.Split.Five
