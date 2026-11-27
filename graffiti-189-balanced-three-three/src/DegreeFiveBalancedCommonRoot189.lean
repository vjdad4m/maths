import DegreeFiveActualCut189
import DegreeFiveRouteBasic189
import DegreeFiveFourPort189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveDistanceTwoSingletonClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveFourForeign189
import DegreeFiveUniquePortClosureTest189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two charge_at_high_port from DegreeFiveDistanceTwoThreeClose189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private boundary_permuted from DegreeFiveExclusiveGateway189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private lift_side_path from DegreeFiveSmallSides189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private noncomputable def sharedPortSet (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V := by
  classical
  exact (Shore C).filter (fun z=>G.Adj a z ∧ G.Adj b z)

private theorem common_shore_count_by_charges_general
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (near : ∀ z∈Shore C,G.dist x z≤2) :
    (Shore C).card≤(sharedPortSet C).card+(secondShore C a).card+(secondShore C b).card+
      (secondShore C x).card := by
  classical
  let A := secondShore C a
  let B := secondShore C b
  let X := secondShore C x
  let K := sharedPortSet C
  have cover : Shore C⊆K∪(A∪B∪X) := by
    intro z zC
    by_cases common : G.Adj a z ∧ G.Adj b z
    · exact mem_union_left _ (mem_filter.mpr ⟨zC,common⟩)
    have zx : z≠x := fun e=>common (e.symm ▸ ⟨ax,bx⟩)
    apply mem_union_right
    by_cases adj : G.Adj x z
    · apply mem_union_left
      by_cases az : G.Adj a z
      · have nb : ¬G.Adj b z := fun bz=>common ⟨az,bz⟩
        exact mem_union_right _ (mem_inter.mpr ⟨zC,
          d2 hc (fun e=>(shore_off C).2 (e.symm ▸ zC)) nb bx adj⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨zC,
        d2 hc (fun e=>(shore_off C).1 (e.symm ▸ zC)) az ax adj⟩)
    have lo := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm zx) adj
    have hi := near z zC
    exact mem_union_right _ (mem_inter.mpr ⟨zC,by simp [DistanceTwo,show G.dist x z=2 by omega]⟩)
  have c := (card_le_card cover).trans (card_union_le K (A∪B∪X))
  have q := card_union_le (A∪B) X
  have r := card_union_le A B
  change _≤K.card+A.card+B.card+X.card
  omega


private theorem inside_high_at_least_three {C : Cmp (G:=G) (a:=a) (b:=b)}
    {z : V} (zC : z∈Shore C) (z5 : 5≤G.degree z) :
    3≤(inside G (Shore C) z).card := by
  classical
  let N := inside G (Shore C) z
  have h := card_le_card (shore_neighbor_cover C zC)
  rw [card_neighborFinset_eq_degree] at h
  have p := card_insert_le a (insert b N)
  have q := card_insert_le b N
  change G.degree z ≤ (insert a (insert b N)).card at h
  change 3≤N.card
  omega

private theorem inside_high_at_least_four_if_exclusive {C : Cmp (G:=G) (a:=a) (b:=b)}
    {z : V} (zC : z∈Shore C) (z5 : 5≤G.degree z) (exclusive : ¬(G.Adj a z ∧ G.Adj b z)) :
    4≤(inside G (Shore C) z).card := by
  classical
  let N := inside G (Shore C) z
  have cover (c d : V) (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (off : ¬G.Adj d z) :
      G.neighborFinset z⊆insert c N := by
    intro w wn
    have e := (mem_neighborFinset G z w).mp wn
    rcases boundary_permuted perm z zC w e with rfl|rfl|wC
    · exact mem_insert_self _ _
    · exact (off e.symm).elim
    exact mem_insert_of_mem (mem_filter.mpr ⟨wC,e⟩)
  have size (c : V) (s : G.neighborFinset z⊆insert c N) : 4≤N.card := by
    have m := (card_le_card s).trans (card_insert_le c N)
    rw [card_neighborFinset_eq_degree] at m
    omega
  by_cases az : G.Adj a z
  · exact size a (cover a b (.inl ⟨rfl,rfl⟩) (fun bz=>exclusive ⟨az,bz⟩))
  exact size b (cover b a (.inr ⟨rfl,rfl⟩) az)

theorem rooted_common_side_when_exclusive_contacts_balanced
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : 2≤(portColor D a).card) (pB : 2≤(portColor D b).card) :
    (Shore C).card≤7 ∧ ∃ x∈Shore C,G.Adj a x ∧ G.Adj b x ∧
      ∃ t,RouteOn G (Shore C) x t := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have two' : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uC v e with rfl|rfl|vh
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp (shore_disjoint cd) vh vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  have da := shore_hit_a ab conn D
  have db := shore_hit_b ab conn D
  let T := Split.Five.switch S (shore_connected D) da db
  let P := portColor D a
  let Q := portColor D b
  let K := sharedPortSet C
  have union : P∪Q=cutPorts D := by
    ext z
    change z∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      z∈(Shore D).filter (fun z=>G.Adj a z ∨ G.Adj b z)
    simp [and_or_left]
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z zp zq
    exact none _ (mem_filter.mp zp).1 ⟨(mem_filter.mp zp).2,(mem_filter.mp zq).2⟩
  have tally := congrArg Finset.card union
  rw [card_union_of_disjoint dis] at tally
  change 2≤P.card at pA
  change 2≤Q.card at pB
  have four : 4≤S.foreignPorts.card := by
    change 4≤(cutPorts D).card
    omega
  have nz : K.Nonempty := card_pos.mp (show 0<K.card by exact lt_of_lt_of_le (by decide) shared)
  obtain ⟨x,xK⟩ := nz
  obtain ⟨xC,ax,bx⟩ := mem_filter.mp xK
  obtain ⟨u,uP,u5⟩ := anywhere_high_of_two degree pA
  obtain ⟨v,vP,v5⟩ := anywhere_high_of_two degree pB
  obtain ⟨uD,au⟩ := mem_filter.mp uP
  obtain ⟨vD,bv⟩ := mem_filter.mp vP
  have bu : ¬G.Adj b u := fun e=>none u uD ⟨au,e⟩
  have av : ¬G.Adj a v := fun e=>none v vD ⟨e,bv⟩
  have cf := opposite_ports_at_exclusive_le_four T hc even uD au bu
  have k4 : K.card≤4 := (card_le_card (show K⊆T.foreignA from fun z zh=>by
    obtain ⟨zc,az,_⟩ := mem_filter.mp zh
    exact mem_filter.mpr ⟨zc,az⟩)).trans cf
  have chargeA := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc uD au u5
  rw [if_neg bu] at chargeA
  have chargeB := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vD bv v5
  rw [if_neg av] at chargeB
  change 5≤P.card+(secondShore D a).card at chargeA
  change 5≤Q.card+(secondShore D b).card at chargeB
  have shellA := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have shellB := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ two' even
  have near := Split.Five.near_universal_at_four_foreign S hc even conn xC ax bx four
  have leftbound := common_shore_count_by_charges_general hc xC ax bx near.2
  let X := secondShore C x
  have px : X.card+(cutPorts D).card≤5 := by
    have far : cutPorts D⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zD,az|bz⟩ := mem_filter.mp zp
      all_goals
        have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xC (e.symm ▸ zD)
        have no := cross x xC z zD
      · exact d2 hc ne no ax.symm az
      exact d2 hc ne no bx.symm bz
    have dd : Disjoint X (cutPorts D) :=
      (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
    have h := card_le_card (union_subset (show X⊆DistanceTwo G x from inter_subset_right) far)
    rw [card_union_of_disjoint dd] at h
    exact h.trans (distanceTwo_le_of_even 5 x (even x))
  change (Shore C).card≤K.card+(secondShore C a).card+(secondShore C b).card+X.card at leftbound
  have c7 : (Shore C).card≤7 := by omega
  refine ⟨c7,?_⟩
  let L := Shore C
  let U := ↑(↑L : Set V)
  let J := G.induce (↑L : Set V)
  have sizeU : Fintype.card U=L.card := Fintype.card_coe L
  have large (u : V) (ul : u∈L) (u5 : 5≤G.degree u) (size : L.card=7) :
      4≤(inside G L u).card := by
    by_cases same : G.Adj a u ∧ G.Adj b u
    · have n := Split.Five.near_universal_at_four_foreign S hc even conn ul same.1 same.2 four
      let N := inside G L u
      let E := secondShore C u
      have o : L⊆insert u (N∪E) := by
        intro z zl
        by_cases e : z=u
        · exact mem_insert.mpr (.inl e)
        apply mem_insert_of_mem
        by_cases uz : G.Adj u z
        · exact mem_union_left _ (mem_filter.mpr ⟨zl,uz⟩)
        have h := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm e) uz
        have q := n.2 z zl
        exact mem_union_right _ (mem_inter.mpr ⟨zl,by simp [DistanceTwo,show G.dist u z=2 by omega]⟩)
      have c := (card_le_card o).trans (card_insert_le u _)
      have q := card_union_le N E
      have s := n.1
      change E.card≤1 at s
      change 4≤N.card
      omega
    exact inside_high_at_least_four_if_exclusive ul u5 same
  let ore : RootedClosureAPI := by
    intro W _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  have cap {A : Finset U} (high : ∀ u∈A,5≤G.degree u.val) :
      ∀ u∈A,∀ v∈A,Fintype.card U≤J.degree u+J.degree v := by
    intro u um v vm
    rw [sizeU,←inside_card_eq_degree_induce (G:=G) L u,
      ←inside_card_eq_degree_induce (G:=G) L v]
    by_cases seven : L.card=7
    · have uu := large u.val u.property (high u um) seven
      have vv := large v.val v.property (high v vm) seven
      omega
    have uu := inside_high_at_least_three u.property (high u um)
    have vv := inside_high_at_least_three v.property (high v vm)
    change 3≤(inside G L u.val).card at uu
    change 3≤(inside G L v.val).card at vv
    change L.card≤7 at c7
    omega
  have pack (r : U) (ar : G.Adj a r.val) (br : G.Adj b r.val) (path : RootedSpan J r) :
      ∃ x∈Shore C,G.Adj a x ∧ G.Adj b x ∧ ∃ t,RouteOn G (Shore C) x t := by
    obtain ⟨t,q,qp,qs⟩ := path
    obtain ⟨p,pp,ps⟩ := lift_side_path L q qp qs
    exact ⟨r.val,r.property,ar,br,t.val,p,pp,ps⟩
  by_cases bad : ∃ z∈L,¬5≤G.degree z
  · obtain ⟨z,zl,zlow⟩ := bad
    let zz : U := ⟨z,zl⟩
    let A : Finset U := univ.erase zz
    let K' := completeWith J A
    have hh (u : U) (ua : u∈A) : 5≤G.degree u.val :=
      (degree u.val z (fun e=>(mem_erase.mp ua).1 (Subtype.ext e))).resolve_right zlow
    have other : ∃ t∈L,t≠z := by
      apply Classical.byContradiction
      intro no
      have pp : K⊆{z} := by
        intro t hm
        apply mem_singleton.mpr
        exact Classical.byContradiction (fun e=>no ⟨t,(mem_filter.mp hm).1,e⟩)
      have h := card_le_card pp
      rw [card_singleton] at h
      change 2≤K.card at shared
      omega
    obtain ⟨t,tl,tz⟩ := other
    have witness : ∃ w∈L,G.Adj z w := by
      let W := ↑(↑L : Set V)
      obtain ⟨p⟩ := (shore_connected C).preconnected (⟨z,zl⟩ : W) ⟨t,tl⟩
      cases p with
      | nil => exact (tz rfl).elim
      | @cons _ w _ e p => exact ⟨w.val,w.property,e⟩
    obtain ⟨w,wl,zw⟩ := witness
    let ww : U := ⟨w,wl⟩
    have edge := completeWith_mono J A (show J.Adj zz ww from zw)
    by_cases hit : G.Adj a z ∧ G.Adj b z
    · apply pack zz hit.1 hit.2
      refine close_completed_class ore A zz (cap hh) ?_
      exact rooted_path_from_root_into_clique K' edge (completeWith_of_mem J A)
    have choose : ∃ r∈K,r≠w := by
      apply Classical.byContradiction
      intro no
      have p : K⊆{w} := by
        intro r rK
        apply mem_singleton.mpr
        exact Classical.byContradiction (fun e=>no ⟨r,rK,e⟩)
      have h := card_le_card p
      rw [card_singleton] at h
      change 2≤K.card at shared
      omega
    obtain ⟨r,rK,rw'⟩ := choose
    obtain ⟨rl,ar,br⟩ := mem_filter.mp rK
    let rr : U := ⟨r,rl⟩
    have rz : rr≠zz := by
      intro e
      have v : r=z := congrArg Subtype.val e
      exact hit (v ▸ ⟨ar,br⟩)
    have wz : ww≠zz := fun e=>zw.ne.symm (congrArg Subtype.val e)
    have rwn : rr≠ww := fun e=>rw' (congrArg Subtype.val e)
    apply pack rr ar br
    refine close_completed_class ore A rr (cap hh) ?_
    exact rooted_path_of_clique_and_outlier K' rz wz rwn edge.symm (completeWith_of_mem J A)
  have hh (u : U) (_ : u∈(univ : Finset U)) : 5≤G.degree u.val :=
    Classical.byContradiction (fun e=>bad ⟨u.val,u.property,e⟩)
  let xx : U := ⟨x,xC⟩
  apply pack xx ax bx
  refine close_completed_class ore univ xx (cap hh) ?_
  obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique univ (completeWith_of_mem J univ) (mem_univ xx)
  exact ⟨y,p,pp,fun u=>(ps u).mpr (mem_univ _)⟩

#print axioms rooted_common_side_when_exclusive_contacts_balanced
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
