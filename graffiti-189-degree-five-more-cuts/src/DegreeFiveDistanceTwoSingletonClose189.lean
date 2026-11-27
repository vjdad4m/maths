import DegreeFiveActualCut189
import DegreeFiveDistanceTwoComponents189
import DegreeFiveDistanceTwoSingleton189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_nonempty
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private singleton_shore_is_low from DegreeFiveDistanceTwoComponents189
open private d2 from CrossSaturation189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem shore_neighbor_cover (D : (CutGraph (G:=G) a b).ConnectedComponent)
    {u : V} (ud : u∈Shore D) :
    G.neighborFinset u ⊆ insert a (insert b (inside G (Shore D) u)) := by
  classical
  intro z zn
  have uz := (mem_neighborFinset G u z).mp zn
  rcases shore_closed D u ud z uz with rfl|rfl|zd
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_insert_self _ _)
  exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨zd,uz⟩))

private theorem inside_le_erase (D : (CutGraph (G:=G) a b).ConnectedComponent)
    {u : V} (ud : u∈Shore D) :
    (inside G (Shore D) u).card≤(Shore D).card-1 := by
  classical
  have sub : inside G (Shore D) u ⊆ (Shore D).erase u := by
    intro z h
    obtain ⟨zs,uz⟩ := mem_filter.mp h
    exact mem_erase.mpr ⟨uz.ne.symm,zs⟩
  simpa only [card_erase_of_mem ud] using card_le_card sub

private theorem non_singleton_shore_least_six (D : (CutGraph (G:=G) a b).ConnectedComponent)
    (hi : ∀ u∈Shore D,5≤G.degree u)
    (hp : (cutPorts D).card≤3) :
    6≤(Shore D).card := by
  classical
  apply Classical.byContradiction
  intro bad
  have incl : Shore D ⊆ cutPorts D := by
    intro u us
    apply mem_filter.mpr
    refine ⟨us,?_⟩
    apply Classical.byContradiction
    intro h
    have sub : G.neighborFinset u⊆inside G (Shore D) u := by
      intro z hz
      have uz := (mem_neighborFinset G u z).mp hz
      rcases shore_closed D u us z uz with rfl|rfl|zs
      · exact (h (.inl uz.symm)).elim
      · exact (h (.inr uz.symm)).elim
      exact mem_filter.mpr ⟨zs,uz⟩
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree] at c
    have l := inside_le_erase D us
    have ge := hi u us
    omega
  have m := (card_le_card incl).trans hp
  obtain ⟨u,us⟩ := shore_nonempty D
  let N := inside G (Shore D) u
  have c := card_le_card (shore_neighbor_cover D us)
  rw [card_neighborFinset_eq_degree] at c
  have l := inside_le_erase D us
  have ge := hi u us
  have c1 := card_insert_le a (insert b N)
  have c2 := card_insert_le b N
  change #N≤_ at l
  change G.degree u≤#(insert a (insert b N)) at c
  omega

private theorem root_on_small_high_shore (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {C D E : (CutGraph (G:=G) a b).ConnectedComponent}
    (DC : D≠C) (ED : E≠D) (EC : E≠C)
    {r : V} (rs : Shore C={r}) (ra : G.Adj r a) (rb : G.Adj r b)
    (small : (Shore D).card≤7) (hi : ∀ u∈Shore D,5≤G.degree u)
    (other : 2≤(cutPorts E).card) {x : V} (xd : x∈Shore D) :
    ∃ z,RouteOn G (Shore D) x z := by
  classical
  let L := Shore D
  let U := ↑(↑L : Set V)
  let J := G.induce (↑L : Set V)
  have cnt : Fintype.card U=L.card := Fintype.card_coe L
  have inside3 (u : V) (us : u∈L) : 3≤(inside G L u).card := by
    let N := inside G L u
    have h := card_le_card (shore_neighbor_cover D us)
    rw [card_neighborFinset_eq_degree] at h
    change G.degree u≤#(insert a (insert b N)) at h
    have c1 := card_insert_le a (insert b N)
    have c2 := card_insert_le b N
    have h5 := hi u us
    change 3≤N.card
    omega
  have inside4 (seven : L.card=7) (u : V) (us : u∈L) : 4≤(inside G L u).card := by
    let N := inside G L u
    have u3 := inside3 u us
    change 3≤N.card at u3
    change 4≤N.card
    apply Classical.byContradiction
    intro n4
    have ax : G.Adj a u := by
      apply Classical.byContradiction
      intro no
      have sub : G.neighborFinset u⊆insert b N := by
        intro v vn
        have e := (mem_neighborFinset G u v).mp vn
        rcases shore_closed D u us v e with rfl|rfl|vs
        · exact (no e.symm).elim
        · exact mem_insert_self _ _
        exact mem_insert_of_mem (mem_filter.mpr ⟨vs,e⟩)
      have c := (card_le_card sub).trans (card_insert_le b N)
      rw [card_neighborFinset_eq_degree] at c
      have h := hi u us
      omega
    have bx : G.Adj b u := by
      apply Classical.byContradiction
      intro no
      have sub : G.neighborFinset u⊆insert a N := by
        intro v vn
        have e := (mem_neighborFinset G u v).mp vn
        rcases shore_closed D u us v e with rfl|rfl|vs
        · exact mem_insert_self _ _
        · exact (no e.symm).elim
        exact mem_insert_of_mem (mem_filter.mpr ⟨vs,e⟩)
      have c := (card_le_card sub).trans (card_insert_le a N)
      rw [card_neighborFinset_eq_degree] at c
      have h := hi u us
      omega
    let Q := L.erase u \ N
    have size : Q.card=3 := by
      have sub : N⊆L.erase u := by
        intro v vn
        obtain ⟨vl,uv⟩ := mem_filter.mp vn
        exact mem_erase.mpr ⟨uv.ne.symm,vl⟩
      dsimp [Q]
      rw [card_sdiff sub,card_erase_of_mem us,seven]
      omega
    have Dtwo {v : V} (vq : v∈Q) : v∈DistanceTwo G u := by
      have ⟨ve,vn⟩ := mem_sdiff.mp vq
      obtain ⟨vu,vl⟩ := mem_erase.mp ve
      have uv : ¬G.Adj u v := fun e=>vn (mem_filter.mpr ⟨vl,e⟩)
      let M := inside G L v
      have m3 := inside3 v vl
      change 3≤M.card at m3
      have inter : ∃ w∈N,w∈M := by
        apply Classical.byContradiction
        intro no
        have dis : Disjoint N M := disjoint_left.mpr (fun w wn wm=>no ⟨w,wn,wm⟩)
        have sub : N∪M ⊆ (L.erase u).erase v := by
          intro w wm
          rcases mem_union.mp wm with wn|wm
          · obtain ⟨wl,uw⟩ := mem_filter.mp wn
            exact mem_erase.mpr ⟨fun e=>uv (e ▸ uw),mem_erase.mpr ⟨uw.ne.symm,wl⟩⟩
          · obtain ⟨wl,vw⟩ := mem_filter.mp wm
            exact mem_erase.mpr ⟨vw.ne.symm,mem_erase.mpr ⟨fun e=>uv (e ▸ vw).symm,wl⟩⟩
        have h := card_le_card sub
        rw [card_union_of_disjoint dis,card_erase_of_mem ve,card_erase_of_mem us,seven] at h
        omega
      obtain ⟨w,wn,wm⟩ := inter
      exact d2 hc vu.symm uv (mem_filter.mp wn).2 (mem_filter.mp wm).2.symm
    have rm : r∈Shore C := by simp [rs]
    have ur : u≠r := fun e=>disjoint_left.mp (shore_disjoint DC) us (e.symm ▸ rm)
    have unr : ¬G.Adj u r := by
      intro e
      rcases shore_closed D u us r e with h|h|h
      · exact ra.ne h
      · exact rb.ne h
      exact disjoint_left.mp (shore_disjoint DC) h rm
    have rd : r∈DistanceTwo G u := d2 hc ur unr ax.symm ra.symm
    let P := cutPorts (G:=G) E
    have pd : P⊆DistanceTwo G u := by
      intro v vp
      obtain ⟨vs,h⟩ := mem_filter.mp vp
      have ne : u≠v := fun e=>disjoint_left.mp (shore_disjoint ED) vs (e ▸ us)
      have no : ¬G.Adj u v := by
        intro e
        rcases shore_closed D u us v e with rfl|rfl|vd
        · exact (shore_off E).1 vs
        · exact (shore_off E).2 vs
        exact disjoint_left.mp (shore_disjoint ED) vs vd
      exact h.elim (fun e=>d2 hc ne no ax.symm e) (fun e=>d2 hc ne no bx.symm e)
    have dis : Disjoint Q P := by
      apply disjoint_left.mpr
      intro v vq vp
      exact disjoint_left.mp (shore_disjoint ED) (mem_filter.mp vp).1
        (mem_erase.mp (mem_sdiff.mp vq).1).2
    have rn : r∉Q∪P := by
      intro h
      rcases mem_union.mp h with q|p
      · exact disjoint_left.mp (shore_disjoint DC) (mem_erase.mp (mem_sdiff.mp q).1).2 rm
      exact disjoint_left.mp (shore_disjoint EC) (mem_filter.mp p).1 rm
    have sub : insert r (Q∪P)⊆DistanceTwo G u := by
      intro v vm
      rcases mem_insert.mp vm with rfl|h
      · exact rd
      exact (mem_union.mp h).elim Dtwo (fun p=>pd p)
    have c := card_le_card sub
    rw [card_insert_of_not_mem rn,card_union_of_disjoint dis,size] at c
    have cap := distanceTwo_le_of_even 5 u (even u)
    change 2≤P.card at other
    omega
  let ore : RootedClosureAPI := by
    intro W _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  let xx : U := ⟨x,xd⟩
  have path : RootedSpan J xx := by
    refine close_completed_class ore univ xx ?_ ?_
    · intro v _ w _
      rw [cnt,←inside_card_eq_degree_induce (G:=G) L v,
        ←inside_card_eq_degree_induce (G:=G) L w]
      by_cases seven : L.card=7
      · have hv := inside4 seven v.val v.property
        have hw := inside4 seven w.val w.property
        omega
      have hv := inside3 v.val v.property
      have hw := inside3 w.val w.property
      change L.card≤7 at small
      omega
    obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique univ (completeWith_of_mem J univ) (mem_univ xx)
    exact ⟨y,p,pp,fun v=>(ps v).mpr (mem_univ _)⟩
  obtain ⟨y,p,pp,pa⟩ := path
  obtain ⟨q,qp,qs⟩ := lift_side_path L p pp pa
  exact ⟨y.val,q,qp,qs⟩

theorem traceable_of_three_shores_one_singleton
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (three : 3≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent)
    (singleton : ∃ C : (CutGraph (G:=G) a b).ConnectedComponent,(Shore C).card=1) :
    ∃ x y : V,∃ q : G.Walk x y,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have upper := component_card_le_three_at_five_distance_two hc two even conn degree
  have total := order_le_sixteen_of_three_shores_one_singleton hc two even conn degree three singleton
  change _≤Nat.card J.ConnectedComponent at three
  change Nat.card J.ConnectedComponent≤_ at upper
  rw [Nat.card_eq_fintype_card] at three upper
  obtain ⟨C,cs⟩ := singleton
  obtain ⟨r,rs⟩ := card_eq_one.mp cs
  have off := shore_off C
  have rm : r∈Shore C := by simp [rs]
  have ra0 : r≠a := fun e=>off.1 (e ▸ rm)
  have rb0 : r≠b := fun e=>off.2 (e ▸ rm)
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=2 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ]
    omega
  obtain ⟨D,dt,E,et,de⟩ := one_lt_card.mp (show 1<T.card by omega)
  have dc : D≠C := (mem_erase.mp dt).1
  have ec : E≠C := (mem_erase.mp et).1
  have Teq : T={D,E} := by
    symm
    apply eq_of_subset_of_card_le
    · intro F h
      simp only [mem_insert,mem_singleton] at h
      exact h.elim (· ▸ dt) (· ▸ et)
    simp [tc,de]
  have pa := shore_hit_a ab conn C
  have pb := shore_hit_b ab conn C
  obtain ⟨x,xm,ax⟩ := pa
  obtain ⟨y,ym,by'⟩ := pb
  have ra : G.Adj r a := (show x=r by simpa [rs] using xm) ▸ ax.symm
  have rb : G.Adj r b := (show y=r by simpa [rs] using ym) ▸ by'.symm
  have rlow : G.degree r≤2 := singleton_shore_is_low rs
  have high {F : J.ConnectedComponent} (fc : F≠C) (u : V) (uf : u∈Shore F) :
      5≤G.degree u := by
    have ru : r≠u := fun e=>disjoint_left.mp (shore_disjoint fc) uf (e ▸ rm)
    exact (degree r u ru).resolve_left (by omega)
  have ports {F : J.ConnectedComponent} (fc : F≠C) : 2≤(cutPorts F).card := by
    apply two_ports_of_nonsingleton ab conn
    apply Classical.byContradiction
    intro no
    have hp := card_pos.mpr (shore_nonempty F)
    obtain ⟨w,ws⟩ := card_eq_one.mp (show (Shore F).card=1 by omega)
    have hw := high fc w (by simp [ws])
    have wl := singleton_shore_is_low ws
    omega
  have cap := foreign_ports_le_five_at_common hc even rm ra.symm rb.symm (T:=T) (by simp [T])
  have d2 := ports dc
  have e2 := ports ec
  have pcap : (cutPorts D).card+(cutPorts E).card≤5 := by
    rw [Teq,sum_insert (by simp [de]),sum_singleton] at cap
    exact cap
  have d6 := non_singleton_shore_least_six D (high dc) (by omega)
  have e6 := non_singleton_shore_least_six E (high ec) (by omega)
  let M := ({a,r,b} : Finset V)
  have m3 : M.card=3 := by simp [M,ab,ra0,ra0.symm,rb0]
  have dDis : Disjoint M (Shore D) := by
    apply disjoint_left.mpr
    intro u um ud
    simp only [M,mem_insert,mem_singleton] at um
    rcases um with rfl|rfl|rfl
    · exact (shore_off D).1 ud
    · exact disjoint_left.mp (shore_disjoint dc) ud rm
    exact (shore_off D).2 ud
  have eDis : Disjoint M (Shore E) := by
    apply disjoint_left.mpr
    intro u um ue
    simp only [M,mem_insert,mem_singleton] at um
    rcases um with rfl|rfl|rfl
    · exact (shore_off E).1 ue
    · exact disjoint_left.mp (shore_disjoint ec) ue rm
    exact (shore_off E).2 ue
  have sum : (Shore D).card+(Shore E).card+3≤Fintype.card V := by
    have dis : Disjoint (Shore D∪Shore E) M :=
      disjoint_union_left.mpr ⟨dDis.symm,eDis.symm⟩
    have c := card_le_univ ((Shore D∪Shore E)∪M)
    rwa [card_union_of_disjoint dis,card_union_of_disjoint (shore_disjoint de),m3] at c
  obtain ⟨u,ud,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,ve,bv⟩ := shore_hit_b ab conn E
  obtain ⟨s,p⟩ := root_on_small_high_shore hc even dc de.symm ec rs ra rb (by omega) (high dc) e2 ud
  obtain ⟨t,q⟩ := root_on_small_high_shore hc even ec de dc rs ra rb (by omega) (high ec) d2 ve
  have left : RouteOn G (Shore D∪M) s b :=
    p.reverse.join (RouteOn.three ra.symm rb ab) dDis.symm au.symm
  have dis : Disjoint (Shore D∪M) (Shore E) :=
    disjoint_union_left.mpr ⟨shore_disjoint de,eDis⟩
  obtain ⟨path,pp,ps⟩ := left.join q dis bv
  refine ⟨s,t,path,pp,fun z=>(ps z).mpr ?_⟩
  by_cases za : z=a
  · simp [M,za]
  by_cases zb : z=b
  · simp [M,zb]
  have zC : z∈Shore (J.connectedComponentMk ⟨z,za,zb⟩) :=
    mem_shore.mpr ⟨⟨za,zb⟩,rfl⟩
  by_cases eq : J.connectedComponentMk ⟨z,za,zb⟩=C
  · rw [eq,rs] at zC
    simp [M,mem_singleton.mp zC]
  have h : J.connectedComponentMk ⟨z,za,zb⟩∈T := mem_erase.mpr ⟨eq,mem_univ _⟩
  rw [Teq] at h
  simp only [mem_insert,mem_singleton] at h
  rcases h with h|h
  · exact mem_union_left _ (mem_union_left _ (h ▸ zC))
  exact mem_union_right _ (h ▸ zC)

#print axioms traceable_of_three_shores_one_singleton
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
