import DegreeFiveRouteBasic189
import DegreeFiveUniquePortHighShore189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open ArticulationPair
open private left_boundary from AdjacentCut189
open private d2 from CrossSaturation189
open private lift_side_path from DegreeFiveSmallSides189
open private inside_at_least_three_at_high inside_at_least_four_at_exclusive_high
  from DegreeFiveUniquePortHighShore189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

private theorem neighbor_in_connected_shore {z q : V} (zl : z∈S.L) (ql : q∈S.L)
    (zq : z≠q) : ∃ w∈S.L,G.Adj z w := by
  let W := ↑(↑S.L : Set V)
  obtain ⟨p⟩ := S.leftConnected.preconnected (⟨z,zl⟩ : W) ⟨q,ql⟩
  cases p with
  | nil => exact (zq rfl).elim
  | @cons _ w _ e p => exact ⟨w.val,w.property,e⟩

theorem root_at_a_port_of_shore_with_one_low_and_one_common
    (small : S.L.card≤8)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {x z : V} (xL : x∈S.L) (zL : z∈S.L) (ax : G.Adj a x)
    (unique : ∀ w∈S.L,G.Adj a w → G.Adj b w → w=x)
    (high : ∀ w∈S.L,w≠z → 5≤G.degree w) :
    ∃ u∈S.L, (G.Adj a u ∨ G.Adj b u) ∧ ∃ t,RouteOn G S.L u t := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let xx : U := ⟨x,xL⟩
  let zz : U := ⟨z,zL⟩
  let A : Finset U := (univ.erase xx).erase zz
  let K := completeWith J A
  have cv (w : U) : w∈A ↔ w≠zz ∧ w≠xx := by simp [A]
  have cnt : Fintype.card U≤8 := by
    change Fintype.card {v : V // v∈S.L}≤8
    rwa [Fintype.card_coe]
  have clique : CompleteOn K A := completeWith_of_mem J A
  have ge (v : U) (va : v∈A) : 4≤J.degree v := by
    have e := inside_card_eq_degree_induce (G:=G) S.L v
    rw [←e]
    have vne : v.val≠z := fun e=>(cv v).mp va |>.1 (Subtype.ext e)
    apply inside_at_least_four_at_exclusive_high S v.property _ (high _ v.property vne)
    intro h
    exact ((cv v).mp va).2 (Subtype.ext (unique _ v.property h.1 h.2))
  have cap (u : U) (ua : u∈A) (v : U) (va : v∈A) :
      Fintype.card U≤J.degree u+J.degree v := by
    have h := ge u ua
    have k := ge v va
    omega
  let ore : RootedClosureAPI := by
    intro W _ _ J' K' _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  have pack (u : U) (hit : G.Adj a u.val ∨ G.Adj b u.val)
      (path : RootedSpan K u) :
      ∃ u∈S.L,(G.Adj a u ∨ G.Adj b u) ∧ ∃ t,RouteOn G S.L u t := by
    obtain ⟨y,p,pp,ps⟩ := close_completed_class ore A u cap path
    obtain ⟨q,qp,qs⟩ := lift_side_path S.L p pp ps
    exact ⟨u.val,u.property,hit,y.val,q,qp,qs⟩
  by_cases same : x=z
  · have e : xx=zz := Subtype.ext same
    have a' : A=(univ : Finset U).erase xx := by simp [A,←e]
    apply pack xx (.inl ax)
    by_cases small' : ∀ y∈S.L,y=x
    · exact ⟨xx,.nil,by simp,fun v=>by
        have h : v=xx := Subtype.ext (small' _ v.property)
        simp [h]⟩
    have ex : ∃ y∈S.L,y≠x := by
      by_contra! nope
      exact small' nope
    obtain ⟨q,ql,qx⟩ := ex
    obtain ⟨w,wl,xw⟩ := neighbor_in_connected_shore S xL ql qx.symm
    rw [a'] at clique
    exact rooted_path_from_root_into_clique K
      (completeWith_mono J A (show J.Adj xx ⟨w,wl⟩ from xw)) clique
  have x3 : 3≤J.degree xx := by
    change 3≤(G.induce (↑S.L : Set V)).degree xx
    rw [←inside_card_eq_degree_induce (G:=G) S.L xx]
    exact inside_at_least_three_at_high S xL (high x xL same)
  have xChoose (u : U) : ∃ v∈A,J.Adj xx v ∧ v≠u := by
    apply Classical.byContradiction
    intro no
    have sub : J.neighborFinset xx⊆({zz,u} : Finset U) := by
      intro v vm
      have xV := (mem_neighborFinset J xx v).mp vm
      by_cases vz : v=zz
      · simp [vz]
      by_cases vu : v=u
      · simp [vu]
      exact (no ⟨v,(cv v).mpr ⟨vz,xV.ne.symm⟩,xV,vu⟩).elim
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree] at h
    have t := card_insert_le zz ({u} : Finset U)
    simp only [card_singleton] at t
    omega
  have fin (u : U) {v : U} (r : RouteOn K (insert xx (insert zz A)) u v) : RootedSpan K u := by
    obtain ⟨p,pp,ps⟩ := r
    refine ⟨v,p,pp,fun w=>(ps w).mpr ?_⟩
    by_cases wx : w=xx
    · simp [wx]
    by_cases wz : w=zz
    · simp [wz]
    exact mem_insert_of_mem (mem_insert_of_mem ((cv w).mpr ⟨wz,wx⟩))
  have xOff : xx∉A := fun h=>((cv xx).mp h).2 rfl
  have zOff : zz∉A := fun h=>((cv zz).mp h).1 rfl
  have xz : xx≠zz := fun h=>same (congrArg Subtype.val h)
  have run (u : U) (uA : u∈A) (zu : J.Adj zz u) (flip : Bool) :
      ∃ v,RouteOn K (insert xx (insert zz A)) (if flip then xx else zz) v := by
    obtain ⟨v,va,xv,vu⟩ := xChoose u
    obtain ⟨q,qp,qs⟩ := path_between_in_clique A clique uA va vu.symm
    have p : RouteOn K A u v := ⟨q,qp,qs⟩
    have start := p.prefix (completeWith_mono J A zu) zOff
    have done := start.suffix (completeWith_mono J A xv.symm)
      (fun h=>(mem_insert.mp h).elim xz xOff)
    cases flip
    · exact ⟨xx,done⟩
    exact ⟨zz,done.reverse⟩
  by_cases hit : G.Adj a z ∨ G.Adj b z
  · apply pack zz hit
    obtain ⟨w,wl,zw⟩ := neighbor_in_connected_shore S zL xL (Ne.symm same)
    let ww : U := ⟨w,wl⟩
    by_cases wx : w=x
    · have zx : J.Adj zz xx := by
        change G.Adj z x
        rwa [←wx]
      obtain ⟨v,vA,xv,_⟩ := xChoose zz
      obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique A clique vA
      have pc : RouteOn K A v y := ⟨p,pp,ps⟩
      have h := (pc.prefix (completeWith_mono J A xv) xOff).prefix
        (completeWith_mono J A zx) (fun h=>(mem_insert.mp h).elim xz.symm zOff)
      rw [insert_comm] at h
      exact fin zz h
    have wa : ww∈A := (cv ww).mpr ⟨fun e=>zw.ne.symm (congrArg Subtype.val e),
      fun e=>wx (congrArg Subtype.val e)⟩
    obtain ⟨v,h⟩ := run ww wa zw false
    exact fin zz h
  have extra : ∃ w∈S.L,w≠x ∧ G.Adj z w := by
    apply Classical.byContradiction
    intro no
    let W := (↑({x} : Finset V) : Set V)ᶜ
    let zr : W := ⟨z,by simpa [W] using (Ne.symm same)⟩
    let ar : W := ⟨a,by simpa [W] using ax.ne⟩
    have step {u v : W} (p : (G.induce W).Walk u v) :
        u=v ∨ ∃ w : W,(G.induce W).Adj u w := by
      cases p with
      | nil => exact .inl rfl
      | @cons _ w _ e p => exact .inr ⟨w,e⟩
    obtain ⟨p⟩ := (conn {x} (by simp)).preconnected zr ar
    have h : zr≠ar := by
      intro e
      have h : z=a := congrArg Subtype.val e
      exact S.leftOff.1 (h ▸ zL)
    obtain ⟨w,e⟩ := (step p).resolve_left h
    change G.Adj z w.val at e
    rcases left_boundary S z zL w.val e with h|h|wL
    · exact hit (.inl (h ▸ e.symm))
    · exact hit (.inr (h ▸ e.symm))
    exact no ⟨w.val,wL,(by simpa [W] using w.property),e⟩
  obtain ⟨w,wl,wx,zw⟩ := extra
  let ww : U := ⟨w,wl⟩
  have wa : ww∈A := (cv ww).mpr ⟨fun e=>zw.ne.symm (congrArg Subtype.val e),
    fun e=>wx (congrArg Subtype.val e)⟩
  obtain ⟨v,h⟩ := run ww wa zw true
  exact pack xx (.inl ax) (fin xx h)

theorem traceable_unique_common_test_with_low_on_common_shore (hc : G.Connected)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (rightConn : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {low : V} (lowL : low∈S.L)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (below : ¬5≤G.degree low) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let T := switch S rightConn rightA rightB
  have n15 := order_le_fifteen_of_unique_common_closure_test S hc two even
    rightConn rightA rightB xL ax bx one test
  have maxInner := (degree_sum_threshold_iff_at_unique_common two one).mp test
  have unique {z : V} (az : G.Adj a z) (bz : G.Adj b z) : z=x := by
    have xm : x∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr bx⟩
    have zm : z∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a z).mpr az,(mem_neighborFinset G b z).mpr bz⟩
    exact card_le_one.mp one.le z zm x xm
  have none {z : V} (zr : z∈S.R) : ¬(G.Adj a z ∧ G.Adj b z) := by
    intro h
    exact disjoint_left.mp S.dis xL (unique h.1 h.2 ▸ zr)
  have highR (v : V) (vR : v∈S.R) : 5≤G.degree v := by
    exact (degree low v (fun e=>disjoint_left.mp S.dis lowL (e.symm ▸ vR))).resolve_left below
  have highL (v : V) (_ : v∈S.L) (vl : v≠low) : 5≤G.degree v :=
    (degree v low vl).resolve_right below
  have r5 : 5≤S.R.card := by
    obtain ⟨u,ur,au⟩ := rightA
    have h := inside_at_least_four_at_exclusive_high T ur (none ur) (highR _ ur)
    have sub : inside G S.R u ⊆ S.R.erase u := by
      intro v vm
      obtain ⟨vr,uv⟩ := mem_filter.mp vm
      exact mem_erase.mpr ⟨uv.ne.symm,vr⟩
    have k := card_le_card sub
    rw [card_erase_of_mem ur] at k
    change 4≤(inside G S.R u).card at h
    omega
  have sizeL : S.L.card≤8 := by
    have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
    have aa : a∉S.L∪S.R := by simp [S.leftOff.1,S.rightOff.1]
    have bb : b∉S.L∪S.R := by simp [S.leftOff.2,S.rightOff.2]
    have nb : a∉insert b (S.L∪S.R) := by simp [ab,aa]
    have c := card_le_univ (insert a (insert b (S.L∪S.R)))
    rw [card_insert_of_not_mem nb,card_insert_of_not_mem bb,card_union_of_disjoint S.dis] at c
    omega
  have sizeR : S.R.card≤6 := by
    have fl : S.foreignPorts⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zr,az|bz⟩ := mem_filter.mp zp
      all_goals
        have ne : x≠z := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ zr)
        have no := S.cross x xL z zr
      · exact d2 hc ne no ax.symm az
      exact d2 hc ne no bx.symm bz
    have fc := (card_le_card fl).trans (distanceTwo_le_of_even 5 x (even x))
    have sub : S.R ⊆ S.foreignPorts∪Nonports G a b := by
      intro z zr
      by_cases h : G.Adj a z ∨ G.Adj b z
      · exact mem_union_left _ (mem_filter.mpr ⟨zr,h⟩)
      apply mem_union_right
      apply mem_sdiff.mpr
      refine ⟨mem_erase.mpr ⟨fun e=>S.rightOff.2 (e ▸ zr),
        mem_erase.mpr ⟨fun e=>S.rightOff.1 (e ▸ zr),mem_univ _⟩⟩,?_⟩
      intro nm
      exact h ((mem_union.mp nm).imp ((mem_neighborFinset G a z).mp) ((mem_neighborFinset G b z).mp))
    have c := (card_le_card sub).trans (card_union_le S.foreignPorts (Nonports G a b))
    omega
  obtain ⟨u,ur,au⟩ := rightA
  obtain ⟨v,vr,bv⟩ := rightB
  have uv : u≠v := fun e=>none ur ⟨au,e.symm ▸ bv⟩
  let U := ↑(↑S.R : Set V)
  let J := G.induce (↑S.R : Set V)
  let uu : U := ⟨u,ur⟩
  let vv : U := ⟨v,vr⟩
  have cnt : Fintype.card U≤6 := by
    change Fintype.card {w : V // w∈S.R}≤6
    rwa [Fintype.card_coe]
  have inner4 (w : U) : 4≤J.degree w := by
    rw [←inside_card_eq_degree_induce (G:=G) S.R w]
    exact inside_at_least_four_at_exclusive_high T w.property (none w.property)
      (highR _ w.property)
  have h := hamilton_connected_of_ore
    (G:=J) (by
      intro y z _ _
      change Fintype.card U + 1 ≤ J.degree y + J.degree z
      have a := inner4 y
      have b := inner4 z
      omega)
    (show uu≠vv from fun e=>uv (congrArg Subtype.val e))
  obtain ⟨p,pp,ps⟩ := h
  obtain ⟨qr,qpr,qs⟩ := lift_side_path S.R p pp ps
  have m : RouteOn G ((insert a (insert b S.R))) a b := by
    have q : RouteOn G S.R u v := ⟨qr,qpr,qs⟩
    have r := q.suffix bv.symm S.rightOff.2
    exact r.prefix au (by simp [S.rightOff.1,show a≠b by
      intro e; rw [e,SimpleGraph.dist_self] at two; omega])
  obtain ⟨s,sL,hit,w,l⟩ := root_at_a_port_of_shore_with_one_low_and_one_common S sizeL conn
    xL lowL ax (fun z _ az bz=>unique az bz) highL
  have dis : Disjoint (insert a (insert b S.R)) S.L := by
    apply disjoint_left.mpr
    intro z zm zl
    simp only [mem_insert] at zm
    rcases zm with rfl|rfl|zr
    · exact S.leftOff.1 zl
    · exact S.leftOff.2 zl
    exact disjoint_left.mp S.dis zl zr
  have finish {c d : V} (route : RouteOn G (insert a (insert b S.R)) c d)
      (edge : G.Adj d s) : ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨p,pp,ps⟩ := route.join l dis edge
    refine ⟨c,w,p,pp,fun z=>(ps z).mpr ?_⟩
    rcases S.cover z with rfl|rfl|zl|zr
    · simp
    · simp
    · exact mem_union_right _ zl
    exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zr))
  exact hit.elim (finish m.reverse) (finish m)

#print axioms root_at_a_port_of_shore_with_one_low_and_one_common
#print axioms traceable_unique_common_test_with_low_on_common_shore
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_of_actual_unique_common_test_low_in_common_component {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (exception : ∃ C : (CutGraph (G:=G) a b).ConnectedComponent,
      (∃ u∈Shore C,G.Adj a u ∧ G.Adj b u) ∧ ∃ low∈Shore C,¬5≤G.degree low) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  obtain ⟨E,⟨y,yE,ay,by'⟩,low,lowE,lowdeg⟩ := exception
  have yx : y=x := by
    have ym : y∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a y).mpr ay,(mem_neighborFinset G b y).mpr by'⟩
    have xm : x∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr xb.symm⟩
    exact card_le_one.mp one.le y ym x xm
  have ec : E=C := by
    apply Classical.byContradiction
    intro e
    exact disjoint_left.mp (shore_disjoint e) yE (yx.symm ▸ xC)
  have lowC : low∈Shore C := ec ▸ lowE
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  exact Split.Five.traceable_unique_common_test_with_low_on_common_shore S hc two even
    (shore_connected D) (shore_hit_a ab conn D) (shore_hit_b ab conn D)
    xC ax xb.symm one test conn lowC degree lowdeg

#print axioms traceable_of_actual_unique_common_test_low_in_common_component
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
