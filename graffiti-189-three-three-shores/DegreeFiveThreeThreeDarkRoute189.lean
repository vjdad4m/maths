import DegreeFiveThreeThreeDegreeHelpers189







namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

open private boundary_has_at_least_two dark dark_boundary_is_visible visible_in_nonports
  from DegreeFiveTwoThreeBase189

open private firstDark firstDark_iff_distance_three dark_dist_ge_three cross_ports_at_distance_two
  distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189

open ArticulationPair
open private visible_touches_some_port all_high_port_neighborhood high_visible_neighborhood
  from DegreeFiveThreeThreeDegreeHelpers189

private theorem visible_dark_degree_cap
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    {v : V} (vv : v∈secondShore C a) : ((dark C).filter (G.Adj v)).card≤2 := by
  classical
  obtain ⟨p,pp,pv⟩ := visible_touches_some_port hc allC vv
  let K := (dark C).filter (G.Adj v)
  have sub : K⊆DistanceTwo G p := by
    intro z zm
    obtain ⟨zq,vz⟩ := mem_filter.mp zm
    obtain ⟨zf,za⟩ := mem_sdiff.mp zq
    obtain ⟨zc,zp⟩ := mem_sdiff.mp zf
    have no : ¬G.Adj p z := fun e=>za
      ((nonport_mem_second_iff_neighbor_port hc zc zp (.inl rfl)).mpr
        ⟨p,mem_filter.mpr ⟨(mem_filter.mp pp).1,allC p pp⟩,e.symm⟩)
    exact d2 hc (fun e=>zp (e ▸ pp)) no pv vz
  have dis : Disjoint K (cutPorts D) := (shore_disjoint cd).mono
    (fun _ h=>(mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp h).1).1).1) (filter_subset _ _)
  have t := cross_ports_at_distance_two hc cd (mem_filter.mp pp).1 (allC p pp) allD
  have h := (card_le_card (union_subset sub t)).trans (distanceTwo_le_of_even 5 p (even p))
  rw [card_union_of_disjoint dis,D3] at h
  change K.card≤2
  omega

/-- If three pairs cover five or six elements, a common element of the
three pairs is impossible; at order six even a pairwise overlap is impossible. -/
private theorem triple_pair_union_restricts_memberships
    (X Y Z Q : Finset V) (eq : X∪Y∪Z=Q)
    (x2 : X.card=2) (y2 : Y.card=2) (z2 : Z.card=2) (q5 : 5≤Q.card)
    (_q6 : Q.card≤6) (r : V) :
    ¬(r∈X ∧ r∈Y ∧ r∈Z) ∧
    (Q.card=6 → ¬(r∈X ∧ r∈Y) ∧ ¬(r∈X ∧ r∈Z) ∧ ¬(r∈Y ∧ r∈Z)) := by
  classical
  have forbid {A B C : Finset V} (eq : A∪B∪C=Q) (a2 : A.card=2) (b2 : B.card=2)
      (c2 : C.card=2) (ar : r∈A) (br : r∈B) :
      (r∈C → False) ∧ Q.card≤5 := by
    have pos : 0<(A∩B).card := card_pos.mpr ⟨r,mem_inter.mpr ⟨ar,br⟩⟩
    have h := card_union_add_card_inter A B
    have t := card_union_le (A∪B) C
    rw [eq] at t
    refine ⟨?_,by omega⟩
    intro cr
    have c : 0<((A∪B)∩C).card := card_pos.mpr
      ⟨r,mem_inter.mpr ⟨mem_union_left _ ar,cr⟩⟩
    have p := card_union_add_card_inter (A∪B) C
    rw [eq] at p
    omega
  have eq' : X∪Z∪Y=Q := by rw [←eq]; ext w; simp [or_comm,or_left_comm,or_assoc]
  have eq'' : Y∪Z∪X=Q := by rw [←eq]; ext w; simp [or_comm,or_left_comm,or_assoc]
  refine ⟨fun h=>(forbid eq x2 y2 z2 h.1 h.2.1).1 h.2.2,?_⟩
  intro six
  exact ⟨fun h=>by have q := (forbid eq x2 y2 z2 h.1 h.2).2; omega,
    fun h=>by have q := (forbid eq' x2 z2 y2 h.1 h.2).2; omega,
    fun h=>by have q := (forbid eq'' y2 z2 x2 h.1 h.2).2; omega⟩

theorem terminal_of_three_visible_and_dark_nonempty
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card) (A3 : (secondShore C a).card=3)
    (high : ∀ z∈Shore C,5≤G.degree z) (positive : (dark C).Nonempty) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let A := secondShore C a
  let Q := dark C
  let P := cutPorts C
  have a3 : A.card=3 := A3
  have p3 : P.card=3 := C3
  obtain ⟨q5,q6,once⟩ := three_visible_dark_orders_and_port_limit hc two even cd
    D3 allC allD Dpos A3 high positive
  have q5' : 5≤Q.card := q5
  have q6' : Q.card≤6 := q6
  obtain ⟨u,v,w,uv,uw,vw,e⟩ := card_eq_three.mp a3
  have uA : u∈A := by simp [e]
  have vA : v∈A := by simp [e]
  have wA : w∈A := by simp [e]
  obtain ⟨p,pP,pu⟩ := visible_touches_some_port hc allC uA
  obtain ⟨r,rP,rv⟩ := visible_touches_some_port hc allC vA
  obtain ⟨s,sP,sw⟩ := visible_touches_some_port hc allC wA
  have pr : p≠r := fun h=>uv (once p pP u uA v vA pu (h.symm ▸ rv))
  have ps : p≠s := fun h=>uw (once p pP u uA w wA pu (h.symm ▸ sw))
  have rs : r≠s := fun h=>vw (once r rP v vA w wA rv (h.symm ▸ sw))
  have pe : P={p,r,s} := by
    have h : ({p,r,s} : Finset V)⊆P := insert_subset_iff.mpr ⟨pP,insert_subset_iff.mpr
      ⟨rP,singleton_subset_iff.mpr sP⟩⟩
    have k : ({p,r,s} : Finset V).card=3 := by simp [pr,ps,rs]
    exact (eq_of_subset_of_card_le h (by omega)).symm
  have onceU (q : V) (qp : q∈P) (uq : G.Adj u q) : q=p := by
    have cases' : q=p ∨ q=r ∨ q=s := by simpa [pe] using qp
    rcases cases' with h|h|h
    · exact h
    · exact (uv (once r rP u uA v vA (h ▸ uq.symm) rv)).elim
    exact (uw (once s sP u uA w wA (h ▸ uq.symm) sw)).elim
  have onceV (q : V) (qp : q∈P) (vq : G.Adj v q) : q=r := by
    have cases' : q=p ∨ q=r ∨ q=s := by simpa [pe] using qp
    rcases cases' with h|h|h
    · exact (uv (once p pP u uA v vA pu (h ▸ vq.symm))).elim
    · exact h
    exact (vw (once s sP v vA w wA (h ▸ vq.symm) sw)).elim
  have onceW (q : V) (qp : q∈P) (wq : G.Adj w q) : q=s := by
    have cases' : q=p ∨ q=r ∨ q=s := by simpa [pe] using qp
    rcases cases' with h|h|h
    · exact (uw (once p pP u uA w wA pu (h ▸ wq.symm))).elim
    · exact (vw (once r rP v vA w wA rv (h ▸ wq.symm))).elim
    exact h
  have pEq := all_high_port_neighborhood hc C3 allC pP (high p (mem_filter.mp pP).1) uA pu
    (fun z za pz=>once p pP z za u uA pz pu)
  have sEq := all_high_port_neighborhood hc C3 allC sP (high s (mem_filter.mp sP).1) wA sw
    (fun z za sz=>once s sP z za w wA sz sw)
  have bs : G.Adj b s := ((mem_neighborFinset G s b).mp (sEq.symm ▸ (by simp))).symm
  have prAdj : G.Adj r p := ((mem_neighborFinset G p r).mp
    (pEq.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_erase.mpr ⟨pr.symm,rP⟩))))).symm
  obtain ⟨u2,_⟩ := high_visible_neighborhood allC A3 high uA pP onceU
    (visible_dark_degree_cap hc even cd D3 allC allD uA)
  obtain ⟨v2,vAdj⟩ := high_visible_neighborhood allC A3 high vA rP onceV
    (visible_dark_degree_cap hc even cd D3 allC allD vA)
  obtain ⟨w2,_⟩ := high_visible_neighborhood allC A3 high wA sP onceW
    (visible_dark_degree_cap hc even cd D3 allC allD wA)
  let X := Q.filter (G.Adj u)
  let Y := Q.filter (G.Adj v)
  let Z := Q.filter (G.Adj w)
  have xc : X.card=2 := u2
  have yc : Y.card=2 := v2
  have zc : Z.card=2 := w2
  have nearCount := distance_two_at_cut_lower two cd
  have full := distanceTwo_le_of_even 5 a (even a)
  have sat : (DistanceTwo G a).card=5 := by omega
  have qU : X∪Y∪Z=Q := by
    apply Subset.antisymm (union_subset (union_subset (filter_subset _ _) (filter_subset _ _)) (filter_subset _ _))
    intro z zq
    have eq : G.dist a z=3 := by
      have lo := dark_dist_ge_three hc zq
      apply Classical.byContradiction
      intro h
      have hi := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist a z by omega)
      have lim := even a
      omega
    obtain ⟨t,ta,zt⟩ := (mem_filter.mp ((firstDark_iff_distance_three hc zq).mpr eq)).2
    have ta' : t∈A := ta
    have ts : t=u ∨ t=v ∨ t=w := by simpa [e] using ta'
    rcases ts with h|h|h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zq,(h ▸ zt).symm⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zq,(h ▸ zt).symm⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zq,(h ▸ zt).symm⟩)
  have dense (t : V) (tQ : t∈Q) : Q.card+1≤2*(Q.filter (G.Adj t)).card := by
    have cap := triple_pair_union_restricts_memberships X Y Z Q qU xc yc zc q5' q6' t
    let N := A.filter (G.Adj t)
    have lim : N.card≤2 := by
      by_cases ut : G.Adj t u
      · by_cases vt : G.Adj t v
        · have wt : ¬G.Adj t w := fun h=>cap.1 ⟨mem_filter.mpr ⟨tQ,ut.symm⟩,
            mem_filter.mpr ⟨tQ,vt.symm⟩,mem_filter.mpr ⟨tQ,h.symm⟩⟩
          have sub : N⊆A.erase w := by
            intro d dn
            obtain ⟨da,td⟩ := mem_filter.mp dn
            exact mem_erase.mpr ⟨fun e=>wt (e ▸ td),da⟩
          have h := card_le_card sub
          rw [card_erase_of_mem wA,a3] at h
          omega
        have sub : N⊆A.erase v := by
          intro d dn
          obtain ⟨da,td⟩ := mem_filter.mp dn
          exact mem_erase.mpr ⟨fun e=>vt (e ▸ td),da⟩
        have h := card_le_card sub
        rw [card_erase_of_mem vA,a3] at h
        omega
      have sub : N⊆A.erase u := by
        intro d dn
        obtain ⟨da,td⟩ := mem_filter.mp dn
        exact mem_erase.mpr ⟨fun e=>ut (e ▸ td),da⟩
      have h := card_le_card sub
      rw [card_erase_of_mem uA,a3] at h
      omega
    have lim6 : Q.card=6 → N.card≤1 := by
      intro six
      obtain ⟨huv,huw,hvw⟩ := cap.2 six
      have nep {x y : V} (xn : x∈N) (yn : y∈N) (ne : x≠y) : False := by
        obtain ⟨xa,tx⟩ := mem_filter.mp xn
        obtain ⟨ya,ty⟩ := mem_filter.mp yn
        have h : x=u ∨ x=v ∨ x=w := by simpa [e] using xa
        have k : y=u ∨ y=v ∨ y=w := by simpa [e] using ya
        rcases h with h|h|h <;> rcases k with k|k|k
        · exact ne (h.trans k.symm)
        · exact huv ⟨mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩,mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩⟩
        · exact huw ⟨mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩,mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩⟩
        · exact huv ⟨mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩,mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩⟩
        · exact ne (h.trans k.symm)
        · exact hvw ⟨mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩,mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩⟩
        · exact huw ⟨mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩,mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩⟩
        · exact hvw ⟨mem_filter.mpr ⟨tQ,(k ▸ ty).symm⟩,mem_filter.mpr ⟨tQ,(h ▸ tx).symm⟩⟩
        exact ne (h.trans k.symm)
      apply Classical.byContradiction
      intro h
      obtain ⟨x,xn,y,yn,xy⟩ := one_lt_card.mp (by omega : 1<N.card)
      exact nep xn yn xy
    have sub : G.neighborFinset t⊆(Q.filter (G.Adj t))∪N := by
      intro y yn
      have h := (mem_neighborFinset G t y).mp yn
      by_cases yq : y∈Q
      · exact mem_union_left _ (mem_filter.mpr ⟨yq,h⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨dark_boundary_is_visible hc allC tQ h yq,h⟩)
    have d := (card_le_card sub).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree] at d
    have tC := (mem_sdiff.mp (mem_sdiff.mp tQ).1).1
    have h := high t tC
    by_cases six : Q.card=6
    · have low := lim6 six
      omega
    omega
  obtain ⟨x,xX⟩ := card_pos.mp (show 0<X.card by omega)
  have ychoice : ∃ y∈Y,x≠y := by
    apply Classical.byContradiction
    intro no
    have sub : Y⊆{x} := fun z zy=>mem_singleton.mpr
      (Classical.byContradiction (fun n=>no ⟨z,zy,fun e=>n e.symm⟩))
    have cap := card_le_card sub
    rw [card_singleton] at cap
    omega
  obtain ⟨y,yY,xy⟩ := ychoice
  obtain ⟨xQ,ux⟩ := mem_filter.mp xX
  obtain ⟨yQ,vy⟩ := mem_filter.mp yY
  have path := terminal_route_of_dense_finset Q xQ yQ xy dense
  have noP (t : V) (tp : t∈P) : t∉Q := fun h=>(mem_sdiff.mp (mem_sdiff.mp h).1).2 tp
  have noA (t : V) (ta : t∈A) : t∉Q := fun h=>(mem_sdiff.mp h).2 ta
  have noPA (t : V) (tp : t∈P) : t∉A := fun h=>(mem_sdiff.mp (visible_in_nonports allC h)).2 tp
  have ur : u≠r := fun h=>noPA r rP (h ▸ uA)
  have up : u≠p := fun h=>noPA p pP (h ▸ uA)
  have vr : v≠r := fun h=>noPA r rP (h ▸ vA)
  have vp : v≠p := fun h=>noPA p pP (h ▸ vA)
  have wr : w≠r := fun h=>noPA r rP (h ▸ wA)
  have wp : w≠p := fun h=>noPA p pP (h ▸ wA)
  have su : s≠u := fun h=>noPA s sP (h.symm ▸ uA)
  have sv : s≠v := fun h=>noPA s sP (h.symm ▸ vA)
  have sw' : s≠w := fun h=>noPA s sP (h.symm ▸ wA)
  have t1 := path.prefix ux (noA u uA)
  have t2 := t1.prefix pu (by simp [up.symm,noP p pP])
  have t3 := t2.prefix prAdj (by simp [pr.symm,ur.symm,noP r rP])
  have t4 := t3.suffix vy.symm (by simp [vr,vp,uv.symm,noA v vA])
  have t5 := t4.suffix (vAdj w wA vw) (by simp [vw.symm,wr,wp,uw.symm,noA w wA])
  have t6 := t5.suffix sw.symm (by simp [sw',sv,rs.symm,ps.symm,su,noP s sP])
  have union : P∪A∪Q=Shore C := by
    have h : A∪Q=Shore C\P := union_sdiff_of_subset (visible_in_nonports allC)
    rw [union_assoc,h,union_sdiff_of_subset (show P⊆Shore C from filter_subset _ _)]
  have support : insert s (insert w (insert v (insert r (insert p (insert u Q)))))=Shore C := by
    rw [←union,pe,e]
    ext t
    simp [or_comm,or_left_comm,or_assoc]
  exact ⟨r,s,allC r rP,bs,support ▸ t6⟩

#print axioms terminal_of_three_visible_and_dark_nonempty
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
