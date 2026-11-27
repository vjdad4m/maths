import DegreeFiveActualCut189
import DegreeFiveFourPort189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveNoUniqueCommon189
import DegreeFiveUniquePortClosureTest189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget count_cut_degree_on_two_shores
  all_common_side_adjacent_when_high_lonely foreign_exclusive_subset_at_port
  universal_if_no_own_second from DegreeFiveThreeForeignImpossible189
open private low_lonely_impossible_against_four from DegreeFiveNoUniqueCommon189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem boundary_permuted {D : Cmp (G:=G) (a:=a) (b:=b)} {c d : V}
    (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (u : V) (uD : u∈Shore D)
    (z : V) (uz : G.Adj u z) : z=c ∨ z=d ∨ z∈Shore D := by
  rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact shore_closed D u uD z uz
  rcases shore_closed D u uD z uz with h|h|h
  · exact .inr (.inl h)
  · exact .inl h
  exact .inr (.inr h)

private theorem nonport_is_low_on_small_shore
    {D : Cmp (G:=G) (a:=a) (b:=b)} (five : (Shore D).card≤5)
    {t : V} (tD : t∈Shore D) (ta : ¬G.Adj a t) (tb : ¬G.Adj b t) :
    ¬5≤G.degree t := by
  classical
  have sub : G.neighborFinset t⊆(Shore D).erase t := by
    intro z zn
    have tz := (mem_neighborFinset G t z).mp zn
    rcases shore_closed D t tD z tz with rfl|rfl|zD
    · exact (ta tz.symm).elim
    · exact (tb tz.symm).elim
    exact mem_erase.mpr ⟨tz.ne.symm,zD⟩
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree,card_erase_of_mem tD] at c
  omega

private theorem lonely_opposite_high_and_common_size_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (Ccap : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {c d x u v : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (xC : x∈Shore C) (cx : G.Adj c x)
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u)
    (vD : v∈Shore D) (dv : G.Adj d v) (cv : ¬G.Adj c v)
    (one : (portColor D c).card=1)
    (leftCap : (portColor C c).card≤4) :
    5≤G.degree u ∧ (portColor C c).card=4 ∧ (Shore C).card=4 := by
  classical
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have cOff : c∉Shore C ∧ c∉Shore D := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact ⟨(shore_off C).1,(shore_off D).1⟩
    exact ⟨(shore_off C).2,(shore_off D).2⟩
  have dOff : d∉Shore C ∧ d∉Shore D := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have step : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have cl := count_cut_degree_on_two_shores cd Ccap two ct
  have uh : 5≤G.degree u := by
    apply Classical.byContradiction
    intro no
    have ch := (degree u c (fun eq=>cOff.2 (eq ▸ uD))).resolve_left no
    exact low_lonely_impossible_against_four hc even degree cd perm uD cu du no vD dv cv
      one (by omega)
  have all := all_common_side_adjacent_when_high_lonely hc cd perm step even
    cOff.1 dOff ⟨x,xC,cx⟩ uD cu du uh one
  have eq : portColor C c=Shore C := by
    ext z
    change z∈(Shore C).filter (G.Adj c) ↔ z∈Shore C
    exact ⟨fun h=>(mem_filter.mp h).1,fun h=>mem_filter.mpr ⟨h,all z h⟩⟩
  have Cfour : 4≤(Shore C).card := by
    apply Classical.byContradiction
    intro nope
    have low (z : V) (zc : z∈Shore C) : ¬5≤G.degree z := by
      have sub : G.neighborFinset z⊆insert a (insert b ((Shore C).erase z)) := by
        intro k kn
        have zk := (mem_neighborFinset G z k).mp kn
        rcases shore_closed C z zc k zk with rfl|rfl|kl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_insert_self _ _)
        exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨zk.ne.symm,kl⟩))
      have m := card_le_card sub
      rw [card_neighborFinset_eq_degree] at m
      have ca := card_insert_le a (insert b ((Shore C).erase z))
      have cb := card_insert_le b ((Shore C).erase z)
      rw [card_erase_of_mem zc] at cb
      omega
    have xno := low x xC
    have ch := (degree x c (fun e=>cOff.1 (e ▸ xC))).resolve_left xno
    rw [eq,one] at cl
    omega
  rw [eq] at leftCap
  exact ⟨uh,by rw [eq]; omega,by omega⟩

private theorem walk_three_data {x y : V} (p : G.Walk x y) (n : p.length=3) :
    ∃ i j,G.Adj x i ∧ G.Adj i j ∧ G.Adj j y := by
  cases p with
  | nil => simp at n
  | cons a q =>
    cases q with
    | nil => simp at n
    | cons b r =>
      cases r with
      | nil => simp at n
      | cons c s =>
        cases s with
        | nil => exact ⟨_,_,a,b,c⟩
        | cons d t => simp at n

private theorem opposite_shore_le_ten_at_lonely_high_port
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) (four : (portColor C c).card=4)
    (p3 : (cutPorts D).card≤3) :
    (Shore D).card≤10 := by
  classical
  let O := Shore D
  let N := inside G O u
  let Q := secondShore D u
  let F := portColor C c
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have cOff : c∉Shore C ∧ c∉O := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact ⟨(shore_off C).1,(shore_off D).1⟩
    exact ⟨(shore_off C).2,(shore_off D).2⟩
  have dOff : d∉Shore C ∧ d∉O := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have cdNo : ¬G.Adj c d := by intro h; have := dist_eq_one_iff_adj.mpr h; omega
  have onlyC (z : V) (zl : z∈O) (cz : G.Adj c z) : z=u := by
    have h : z∈portColor D c := mem_filter.mpr ⟨zl,cz⟩
    exact card_le_one.mp one.le z h u (mem_filter.mpr ⟨uD,cu⟩)
  have N4 : N.card=4 := by
    have d := two_shore_budget cd dOff dist even
    have sub : N⊆secondShore D c := by
      intro z zn
      obtain ⟨zl,uz⟩ := mem_filter.mp zn
      have ne : c≠z := fun e=>cOff.2 (e.symm ▸ zl)
      exact mem_inter.mpr ⟨zl,d2 hc ne (fun e=>uz.ne.symm (onlyC z zl e)) cu uz⟩
    have l := card_le_card sub
    have nc : G.neighborFinset u⊆insert c N := by
      intro z hz
      have uz := (mem_neighborFinset G u z).mp hz
      rcases boundary_permuted perm u uD z uz with rfl|rfl|zl
      · exact mem_insert_self _ _
      · exact (du uz.symm).elim
      exact mem_insert_of_mem (mem_filter.mpr ⟨zl,uz⟩)
    have r := (card_le_card nc).trans (card_insert_le c N)
    rw [card_neighborFinset_eq_degree] at r
    omega
  have foreign : F⊆DistanceTwo G u := foreign_exclusive_subset_at_port hc cd ct uD cu
  have qf : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have sub : Q∪F⊆DistanceTwo G u := union_subset inter_subset_right foreign
  have s := card_le_card sub
  rw [card_union_of_disjoint qf] at s
  change F.card=4 at four
  have budget := distanceTwo_le_of_even 5 u (even u)
  have Q1 : Q.card≤1 := by omega
  have noB {z : V} (zl : z∈O) (dz : G.Adj d z) : ¬G.Adj u z := by
    intro uz
    have h := d2 hc (show u≠d from fun e=>dOff.2 (e ▸ uD)) (fun e=>du e.symm) uz dz.symm
    have off : d∉Q∪F := by
      intro e
      exact (mem_union.mp e).elim (fun e=>dOff.2 (mem_inter.mp e).1)
        (fun e=>dOff.1 (mem_filter.mp e).1)
    have s' : insert d (Q∪F)⊆DistanceTwo G u := by
      intro z hz
      exact (mem_insert.mp hz).elim (fun e=>e.symm ▸ h) (fun e=>sub e)
    have s1 := card_le_card s'
    rw [card_insert_of_not_mem off,card_union_of_disjoint qf] at s1
    have all := universal_if_no_own_second hc uD (by change Q.card=0; omega)
    have sub' : O⊆insert u N := by
      intro z zs
      exact (all z zs).elim (fun e=>mem_insert.mpr (.inl e))
        (fun e=>mem_insert_of_mem (mem_filter.mpr ⟨zs,e⟩))
    have le5 := (card_le_card sub').trans (card_insert_le u N)
    have uN : u∉N := fun e=>G.loopless u (mem_filter.mp e).2
    have five : O.card=5 := by
      have n := card_le_card (show insert u N⊆O from fun _ h=>
        (mem_insert.mp h).elim (fun e=>e.symm ▸ uD) (fun e=>(mem_filter.mp e).1))
      rw [card_insert_of_not_mem uN,N4] at n
      omega
    let I := O \ cutPorts D
    have psub : cutPorts D⊆O := filter_subset _ _
    have c := card_sdiff_add_card_eq_card psub
    change I.card+(cutPorts D).card=O.card at c
    obtain ⟨x,xI,y,yI,xy⟩ := one_lt_card.mp (show 1<I.card by omega)
    have lo (t : V) (tt : t∈I) : ¬5≤G.degree t := by
      obtain ⟨tD,tOff⟩ := mem_sdiff.mp tt
      exact nonport_is_low_on_small_shore five.le tD
        (fun e=>tOff (mem_filter.mpr ⟨tD,.inl e⟩))
        (fun e=>tOff (mem_filter.mpr ⟨tD,.inr e⟩))
    exact (degree x y xy).elim (lo x xI) (lo y yI)
  obtain ⟨t,tN,t5⟩ := anywhere_high_of_two degree (show 2≤N.card by omega)
  obtain ⟨tO,ut⟩ := mem_filter.mp tN
  have tc : ¬G.Adj c t := fun e=>ut.ne.symm (onlyC t tO e)
  have td : ¬G.Adj d t := fun e=>noB tO e ut
  let Z := insert u (N.erase t∪Q)
  have tsub : G.neighborFinset t⊆Z := by
    intro z hz
    have tz := (mem_neighborFinset G t z).mp hz
    rcases boundary_permuted perm t tO z tz with rfl|rfl|zo
    · exact (tc tz.symm).elim
    · exact (td tz.symm).elim
    by_cases zu : z=u
    · exact mem_insert.mpr (.inl zu)
    apply mem_insert_of_mem
    by_cases uz : G.Adj u z
    · exact mem_union_left _ (mem_erase.mpr ⟨tz.ne.symm,mem_filter.mpr ⟨zo,uz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zo,d2 hc (Ne.symm zu) uz ut tz⟩)
  have zCap := card_insert_le u (N.erase t∪Q)
  change Z.card≤_ at zCap
  have zCap' := card_union_le (N.erase t) Q
  rw [card_erase_of_mem tN] at zCap'
  have zCount := card_le_card tsub
  rw [card_neighborFinset_eq_degree] at zCount
  have Qeq1 : Q.card=1 := by omega
  obtain ⟨w,wEq⟩ := card_eq_one.mp Qeq1
  have wQ : w∈Q := by simp [wEq]
  have zEq := eq_of_subset_of_card_le tsub (by rw [card_neighborFinset_eq_degree]; omega)
  have tw : G.Adj t w := (mem_neighborFinset G t w).mp
    (zEq.symm ▸ mem_insert_of_mem (mem_union_right _ wQ))
  have uRad (z : V) : G.dist u z≤3 := by
    apply Classical.byContradiction
    intro no
    have far : 4≤G.dist u z := by omega
    have lo := distanceTwo_add_two_le_even_of_far hc far
    have b := even u
    omega
  let H := insert u (N∪Q)
  let J := O \ H
  have far (z : V) (zj : z∈J) : G.Adj w z := by
    obtain ⟨zo,nH⟩ := mem_sdiff.mp zj
    have ne : u≠z := fun e=>nH (mem_insert.mpr (.inl e.symm))
    have nu : ¬G.Adj u z := fun e=>nH
      (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨zo,e⟩)))
    have n2 : z∉DistanceTwo G u := fun e=>nH
      (mem_insert_of_mem (mem_union_right _ (mem_inter.mpr ⟨zo,e⟩)))
    have ge := hc.one_lt_dist_of_ne_of_not_adj ne nu
    have hi := uRad z
    have d3 : G.dist u z=3 := by
      by_cases h : G.dist u z=2
      · exact (n2 (by simp [DistanceTwo,h])).elim
      omega
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist u z
    obtain ⟨i,j,ui,ij,jz⟩ := walk_three_data p (pl.trans d3)
    have io : i∈O := by
      rcases boundary_permuted perm u uD i ui with rfl|rfl|io
      · rcases boundary_permuted perm z zo j jz.symm with rfl|rfl|jo
        · exact (G.loopless _ ij).elim
        · exact (cdNo ij).elim
        have ju := onlyC j jo ij
        exact (nu (ju ▸ jz)).elim
      · exact (du ui.symm).elim
      exact io
    have jo : j∈O := by
      rcases boundary_permuted perm i io j ij with rfl|rfl|jO
      · exact (ne (onlyC z zo jz).symm).elim
      · exact (noB io ij.symm ui).elim
      exact jO
    have uj : ¬G.Adj u j := by
      intro e
      have l := G.dist_le (Walk.cons e (Walk.cons jz .nil))
      simp at l
      omega
    have ujne : u≠j := fun e=>nu (e.symm ▸ jz)
    have jq : j∈Q := mem_inter.mpr ⟨jo,d2 hc ujne uj ui ij⟩
    have jw : j=w := by simpa [wEq] using jq
    exact jw ▸ jz
  have Jtwo : J⊆DistanceTwo G t := by
    intro z zj
    obtain ⟨zo,nh⟩ := mem_sdiff.mp zj
    have ne : t≠z := fun e=>nh (mem_insert_of_mem (mem_union_left _ (e ▸ tN)))
    have no : ¬G.Adj t z := by
      intro tz
      have h := tsub ((mem_neighborFinset G t z).mpr tz)
      apply nh
      rcases mem_insert.mp h with rfl|h
      · exact mem_insert_self _ _
      exact mem_insert_of_mem (mem_union.mpr ((mem_union.mp h).imp (fun e=>(mem_erase.mp e).2) id))
    exact d2 hc ne no tw (far z zj)
  have c2 : c∈DistanceTwo G t := d2 hc
    (show t≠c from fun e=>cOff.2 (e ▸ tO)) (fun e=>tc e.symm) ut.symm cu.symm
  have sub' : insert c J⊆DistanceTwo G t := by
    intro z zm
    exact (mem_insert.mp zm).elim (fun e=>e.symm ▸ c2) (fun e=>Jtwo e)
  have Jc := card_le_card sub'
  rw [card_insert_of_not_mem (fun e=>cOff.2 (mem_sdiff.mp e).1)] at Jc
  change J.card+1≤(DistanceTwo G t).card at Jc
  have tBudget := distanceTwo_le_of_even 5 t (even t)
  have hcap := card_insert_le u (N∪Q)
  change H.card≤_ at hcap
  have hcap' := card_union_le N Q
  have oCap : O.card≤(H∪J).card := card_le_card (by
    intro z zo
    by_cases zh : z∈H
    · exact mem_union_left _ zh
    exact mem_union_right _ (mem_sdiff.mpr ⟨zo,zh⟩))
  have q := card_union_le H J
  change O.card≤10
  omega

theorem order_le_sixteen_at_three_or_fewer_exclusive_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (p3 : (cutPorts D).card≤3) :
    Fintype.card V≤16 := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have hA := shore_hit_a ab conn D
  have hB := shore_hit_b ab conn D
  let T : Split G a b :=
    ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,shore_connected D,
      (fun u ud v vc e=>by
        rcases shore_closed D u ud v e with rfl|rfl|vD
        · exact (shore_off C).1 vc
        · exact (shore_off C).2 vc
        exact disjoint_left.mp (shore_disjoint cd) vc vD),
      hA,hB,(fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  obtain ⟨u,uD,au⟩ := hA
  obtain ⟨v,vD,bv⟩ := hB
  have bu : ¬G.Adj b u := fun e=>none _ uD ⟨au,e⟩
  have av : ¬G.Adj a v := fun e=>none _ vD ⟨e,bv⟩
  let P := portColor D a
  let Q := portColor D b
  have P1 := card_pos.mpr (show P.Nonempty from ⟨u,mem_filter.mpr ⟨uD,au⟩⟩)
  have Q1 := card_pos.mpr (show Q.Nonempty from ⟨v,mem_filter.mpr ⟨vD,bv⟩⟩)
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z zp zq
    exact none _ (mem_filter.mp zp).1 ⟨(mem_filter.mp zp).2,(mem_filter.mp zq).2⟩
  have union : P∪Q=cutPorts D := by
    ext z
    change z∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      z∈(Shore D).filter (fun z=>G.Adj a z ∨ G.Adj b z)
    simp [and_or_left]
  have cnt := congrArg Finset.card union
  rw [card_union_of_disjoint dis] at cnt
  have good : (Shore C).card=4 ∧ (Shore D).card≤10 := by
    by_cases a1 : P.card=1
    · have cap := opposite_ports_at_exclusive_le_four T hc even uD au bu
      change (portColor C a).card≤4 at cap
      obtain ⟨u5,four,ss⟩ := lonely_opposite_high_and_common_size_four hc two even
        degree cd cover (.inl ⟨rfl,rfl⟩) xC ax uD au bu vD bv av a1 cap
      exact ⟨ss,opposite_shore_le_ten_at_lonely_high_port hc two even degree cd
        (.inl ⟨rfl,rfl⟩) uD au bu u5 a1 four p3⟩
    have b1 : Q.card=1 := by omega
    have cap := opposite_ports_at_exclusive_le_four T.flip hc even vD bv av
    change (portColor C b).card≤4 at cap
    obtain ⟨v5,four,ss⟩ := lonely_opposite_high_and_common_size_four hc two even
      degree cd cover (.inr ⟨rfl,rfl⟩) xC bx vD bv av uD au bu b1 cap
    exact ⟨ss,opposite_shore_le_ten_at_lonely_high_port hc two even degree cd
      (.inr ⟨rfl,rfl⟩) vD bv av v5 b1 four p3⟩
  let Z := insert a (insert b (Shore C∪Shore D))
  have sub : (univ : Finset V)⊆Z := by
    intro z _
    rcases cover z with rfl|rfl|zc|zd
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ zc))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ zd))
  have k := card_le_card sub
  rw [card_univ] at k
  have c1 := card_insert_le a (insert b (Shore C∪Shore D))
  have c2 := card_insert_le b (Shore C∪Shore D)
  have c3 := card_union_le (Shore C) (Shore D)
  change Z.card≤_ at c1
  have h := good.1
  have l := good.2
  omega

#print axioms order_le_sixteen_at_three_or_fewer_exclusive_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
