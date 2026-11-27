import DegreeFiveBalancedUniform189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common high_a_port_cost secondA_right_and_left_le_five from DegreeFiveFourPort189
open private any_internal_neighbor left_high_inside from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

/-- A singleton a-attachment opposite four a-attachments cannot be
on an unmixed shore if the opposite side has at least two b-ports. -/
theorem singleton_opposite_four_forces_bridge (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (p1 : S.localA.card=1) (p4 : S.foreignA.card=4)
    (q2 : 2≤(S.R.filter (G.Adj b)).card) : portBridge S := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨x,xl,ax⟩ := S.leftA
  have xp : x∈S.localA := mem_filter.mpr ⟨xl,ax⟩
  have uniq : S.localA={x} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr xp) (by simp [p1])).symm
  let E := secondA G S.L a
  have opp : (S.R.filter (G.Adj b))⊆secondA G S.R a := by
    intro y yy
    obtain ⟨yr,by'⟩ := mem_filter.mp yy
    have cv := no_bridge_four_foreign_cover S hc far even p4 no yr
    rcases mem_union.mp cv with ap|sh
    · exact (not_common far (mem_filter.mp ap).2 by').elim
    exact sh
  have rho := (card_le_card opp)
  have sum := secondA_right_and_left_le_five S even
  have E3 : E.card≤3 := by change (secondA G S.L a).card≤3; omega
  have low : ¬5≤G.degree x := by
    intro hi
    have n := high_a_port_cost S hc far xp hi
    change 5≤S.localA.card+E.card at n
    omega
  obtain ⟨u,ul,xu⟩ := any_internal_neighbor S xl far
  let X := S.L.filter (G.Adj x)
  let Y := S.L∩DistanceTwo G x
  have xu' : u∈X := mem_filter.mpr ⟨ul,xu⟩
  have no_a {z : V} (zl : z∈S.L) (xz : G.Adj x z) : ¬G.Adj a z := by
    intro az
    have zp : z∈S.localA := mem_filter.mpr ⟨zl,az⟩
    rw [uniq] at zp
    exact xz.ne (mem_singleton.mp zp).symm
  have no_b {z : V} (zl : z∈S.L) (xz : G.Adj x z) : ¬G.Adj b z :=
    fun bz=>no ⟨x,xl,z,zl,ax,xz,bz⟩
  have X3 : X.card≤3 := by
    have sub : X⊆E := by
      intro z zz
      obtain ⟨zl,xz⟩ := mem_filter.mp zz
      exact mem_inter.mpr ⟨zl,d2 hc (fun h=>S.leftOff.1 (h.symm ▸ zl)) (no_a zl xz) ax xz⟩
    exact (card_le_card sub).trans E3
  have Y1 : Y.card≤1 := by
    have sub : S.foreignA∪Y⊆DistanceTwo G x := union_subset (foreign_subset S hc xl ax) inter_subset_right
    have dis : Disjoint S.foreignA Y := S.dis.symm.mono (filter_subset _ _) inter_subset_left
    have n := card_le_card sub
    rw [card_union_of_disjoint dis,p4] at n
    have b := distanceTwo_le_of_even 5 x (even x)
    omega
  have high := (degree u x xu.ne.symm).resolve_right low
  have sub : G.neighborFinset u⊆insert x (X.erase u∪Y) := by
    intro z zz
    have uz := (mem_neighborFinset G u z).mp zz
    rcases left_boundary S u ul z uz with rfl|rfl|zl
    · exact (no_a ul xu uz.symm).elim
    · exact (no_b ul xu uz.symm).elim
    by_cases zx : z=x
    · simp [zx]
    apply mem_insert_of_mem
    by_cases xz : G.Adj x z
    · exact mem_union_left _ (mem_erase.mpr ⟨uz.ne.symm,mem_filter.mpr ⟨zl,xz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zl,d2 hc (Ne.symm zx) xz xu uz⟩)
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  have d := card_insert_le x (X.erase u∪Y)
  have e := card_union_le (X.erase u) Y
  rw [card_erase_of_mem xu'] at e
  have pos := card_pos.mpr ⟨u,xu'⟩
  omega

/-- Given opposing singleton/four a-ports, at most three b-ports on the
singleton shore, and at least two opposite b-ports, the singleton shore
has five vertices and at least three b-ports. All other vertices are high. -/
theorem singleton_mixed_shore_size (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (p1 : S.localA.card=1) (p4 : S.foreignA.card=4)
    (qL : (S.L.filter (G.Adj b)).card≤3) (qR : 2≤(S.R.filter (G.Adj b)).card) :
    S.L.card=5 ∧ (S.L.filter (G.Adj b)).card=3 ∧
      (∀ u∈S.R,5≤G.degree u) ∧
      S.R.card≤5+(S.R.filter (G.Adj b)).card := by
  classical
  have br := singleton_opposite_four_forces_bridge S hc far even degree p1 p4 qR
  have Lupper := bound_bridge_side_of_opposite_four S hc far even rightConnected rightA rightB p4 br
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := br
  have Llower : 5≤S.L.card := by
    have h : ∃ z∈S.L,5≤G.degree z := (degree x y xy.ne).elim
      (fun h=>⟨x,xl,h⟩) (fun h=>⟨y,yl,h⟩)
    obtain ⟨z,zl,zh⟩ := h
    have c := left_high_inside S far zl zh
    have s : ArticulationPair.inside G S.L z ⊆ S.L.erase z := by
      intro w ww
      obtain ⟨wl,zw⟩ := mem_filter.mp ww
      exact mem_erase.mpr ⟨zw.ne.symm,wl⟩
    have m := card_le_card s
    rw [card_erase_of_mem zl] at m
    omega
  have L5 : S.L.card=5 := by omega
  let B := S.L.filter (G.Adj b)
  let I := inner G S.L a b
  have lo (z : V) (zi : z∈I) : ¬5≤G.degree z := by
    obtain ⟨zl,az,bz⟩ := mem_filter.mp zi
    have sub : G.neighborFinset z⊆S.L.erase z := by
      intro w ww
      have zw := (mem_neighborFinset G z w).mp ww
      rcases left_boundary S z zl w zw with rfl|rfl|wl
      · exact (az zw.symm).elim
      · exact (bz zw.symm).elim
      exact mem_erase.mpr ⟨zw.ne.symm,wl⟩
    have c := card_le_card sub
    rw [card_erase_of_mem zl,L5,card_neighborFinset_eq_degree] at c
    omega
  have i1 : I.card≤1 := by
    apply Nat.le_of_not_gt
    intro too
    obtain ⟨u,ui,v,vi,uv⟩ := one_lt_card.mp too
    exact (lo _ vi ((degree u v uv).resolve_left (lo _ ui))).elim
  have cov : S.L⊆(S.localA∪B)∪I := by
    intro z zl
    by_cases az : G.Adj a z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zl,az⟩))
    by_cases bz : G.Adj b z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zl,bz⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zl,az,bz⟩)
  have n := (card_le_card cov).trans (card_union_le _ _)
  have e := card_union_le S.localA B
  change B.card≤3 at qL
  have B3 : B.card=3 := by omega
  have lone : I.card=1 := by omega
  obtain ⟨u,ui⟩ := card_pos.mp (by omega : 0<I.card)
  have ulo := lo _ ui
  have ul := (mem_filter.mp ui).1
  have rh (z : V) (zr : z∈S.R) : 5≤G.degree z :=
    (degree u z (fun h=>disjoint_left.mp S.dis (h ▸ ul) zr)).resolve_left ulo
  refine ⟨L5,B3,rh,?_⟩
  have univ := bridge_four_forces_universal S hc far even p4 xl ax xy by'
  have eL : (secondA G S.L a).card≥4 := by
    have sub : S.L.erase x ⊆ secondA G S.L a := by
      intro z zz
      obtain ⟨zx,zl⟩ := mem_erase.mp zz
      have xz := (univ _ zl).resolve_left zx
      have uniq : S.localA={x} := (eq_of_subset_of_card_le
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨xl,ax⟩ : x∈S.localA)) (by simpa only [card_singleton] using p1.le)).symm
      have az : ¬G.Adj a z := by
        intro az
        have zp : z∈S.localA := mem_filter.mpr ⟨zl,az⟩
        rw [uniq] at zp
        exact zx (mem_singleton.mp zp)
      exact mem_inter.mpr ⟨zl,d2 hc (fun h=>S.leftOff.1 (h.symm ▸ zl)) az ax xz⟩
    have c := card_le_card sub
    rw [card_erase_of_mem xl,L5] at c
    exact c
  have sum := secondA_right_and_left_le_five S even
  have b2 : G.dist x b=2 := by
    have ne : x≠b := fun h=>S.leftOff.2 (h ▸ xl)
    exact (mem_filter.mp (d2 hc ne (fun h=>not_common far ax h.symm) xy by'.symm)).2
  have a1 := dist_eq_one_iff_adj.mpr ax.symm
  have rad := (saturated_at_opposite_four S hc far even p4 xl ax).2
  let Q := S.R.filter (G.Adj b)
  have cov : S.R⊆(S.foreignA∪Q)∪secondA G S.R a := by
    intro z zr
    by_cases az : G.Adj a z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zr,az⟩))
    by_cases bz : G.Adj b z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zr,bz⟩))
    have m := cross_metric S.L hc xl (fun h=>disjoint_left.mp S.dis h zr) (left_boundary S)
    have a2 := hc.one_lt_dist_of_ne_of_not_adj (show a≠z from fun h=>S.rightOff.1 (h.symm ▸ zr)) az
    have b2' := hc.one_lt_dist_of_ne_of_not_adj (show b≠z from fun h=>S.rightOff.2 (h.symm ▸ zr)) bz
    have d3 := rad z
    exact mem_union_right _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,show G.dist a z=2 by omega]⟩)
  have z := (card_le_card cov).trans (card_union_le _ _)
  have q := card_union_le S.foreignA Q
  change S.R.card≤5+Q.card
  omega

#print axioms singleton_opposite_four_forces_bridge
#print axioms singleton_mixed_shore_size
end Graffiti189LongestPath.CrossSaturation.Split.Five
