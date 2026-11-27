import DegreeFiveActualCut189
import DegreeFiveFourPort189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveDistanceTwoSingletonClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveFourForeign189
import DegreeFiveUniquePortClosureTest189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private Cmp portColor two_shore_budget all_adj_of_no_second count_cut_degree_on_two_shores
  color_one_of_all_other other_cut_has_three_from_high_common all_common_side_adjacent_when_high_lonely
  foreign_exclusive_subset_at_port universal_if_no_own_second from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem lonely_port_low_if_other_at_most_three
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x c d u v : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (xC : x∈Shore C) (cx : G.Adj c x) (dx : G.Adj d x)
    (only : ∀ q∈Shore C,G.Adj c q → G.Adj d q → q=x)
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u)
    (vD : v∈Shore D) (dv : G.Adj d v) (cv : ¬G.Adj c v)
    (one : (portColor D c).card=1) (le3 : (portColor D d).card≤3) :
    ¬5≤G.degree u := by
  classical
  intro uh
  have cOff : c∉Shore C ∧ c∉Shore D := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact ⟨(shore_off C).1,(shore_off D).1⟩
    exact ⟨(shore_off C).2,(shore_off D).2⟩
  have dOff : d∉Shore C ∧ d∉Shore D := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have revDist : G.dist d c=2 := by rwa [SimpleGraph.dist_comm]
  have other : d=a ∨ d=b := perm.elim (fun e=>.inr e.2) (fun e=>.inl e.2)
  have swap : (d=a ∧ c=b) ∨ (d=b ∧ c=a) :=
    perm.elim (fun e=>.inr ⟨e.2,e.1⟩) (fun e=>.inl ⟨e.2,e.1⟩)
  have all := all_common_side_adjacent_when_high_lonely hc cd perm dist even
    cOff.1 dOff ⟨x,xC,cx⟩ uD cu du uh one
  have dC := color_one_of_all_other xC dx only all
  have dSum := count_cut_degree_on_two_shores cd cover two other
  have dlow : ¬5≤G.degree d := by omega
  have vHigh := (degree d v (fun e=>dOff.2 (e.symm ▸ vD))).resolve_left dlow
  have xHigh := (degree d x (fun e=>dOff.1 (e.symm ▸ xC))).resolve_left dlow
  have r := charge_at_high_port swap hc vD dv vHigh
  rw [if_neg cv] at r
  change 5≤(portColor D d).card+(secondShore D d).card at r
  have l := other_cut_has_three_from_high_common hc xC dx xHigh dOff.1 only all
  have cap := two_shore_budget cd cOff revDist even
  omega

private theorem low_lonely_impossible_against_four
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u v : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (low : ¬5≤G.degree u)
    (vD : v∈Shore D) (dv : G.Adj d v) (cv : ¬G.Adj c v)
    (one : (portColor D c).card=1) (four : 4≤(portColor C c).card) : False := by
  classical
  let F := portColor C c
  let Q := secondShore D u
  let O := Shore D
  have cOff : c∉O := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact (shore_off D).1
    exact (shore_off D).2
  have dOff : d∉Shore C ∧ d∉O := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have uv : u≠v := fun e=>du (e.symm ▸ dv)
  have vh := (degree u v uv).resolve_left low
  have onlyC (z : V) (zl : z∈O) (cz : G.Adj c z) : z=u := by
    have h : z∈portColor D c := mem_filter.mpr ⟨zl,cz⟩
    exact card_le_one.mp one.le z h u (mem_filter.mpr ⟨uD,cu⟩)
  have bdy (t : V) (tO : t∈O) (z : V) (tz : G.Adj t z) :
      z=c ∨ z=d ∨ z∈O := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact shore_closed D t tO z tz
    rcases shore_closed D t tO z tz with h|h|h
    · exact .inr (.inl h)
    · exact .inl h
    exact .inr (.inr h)
  have O5 : 5≤O.card := by
    have sub : G.neighborFinset v⊆insert d (O.erase v) := by
      intro y yn
      have e := (mem_neighborFinset G v y).mp yn
      rcases bdy v vD y e with rfl|rfl|ys
      · exact (cv e.symm).elim
      · exact mem_insert_self _ _
      exact mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,ys⟩)
    have out := (card_le_card sub).trans (card_insert_le d (O.erase v))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem vD] at out
    change G.degree v≤O.card-1+1 at out
    omega
  have foreign : F⊆DistanceTwo G u := foreign_exclusive_subset_at_port hc cd
    (perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)) uD cu
  have qf : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have sub : Q∪F⊆DistanceTwo G u := union_subset inter_subset_right foreign
  have s := card_le_card sub
  rw [card_union_of_disjoint qf] at s
  change 4≤F.card at four
  have budget := distanceTwo_le_of_even 5 u (even u)
  have Q1 : Q.card≤1 := by omega
  have noB {t : V} (tl : t∈O) (dt : G.Adj d t) : ¬G.Adj u t := by
    intro ut
    have du2 := d2 hc (show u≠d from fun e=>dOff.2 (e ▸ uD)) (fun e=>du e.symm) ut dt.symm
    have dn : d∉Q∪F := by
      intro h
      exact (mem_union.mp h).elim (fun h=>dOff.2 (mem_inter.mp h).1)
        (fun h=>dOff.1 (mem_filter.mp h).1)
    have sum : insert d (Q∪F)⊆DistanceTwo G u := by
      intro y ym
      exact (mem_insert.mp ym).elim (fun e=>e.symm ▸ du2) (fun e=>sub e)
    have n := card_le_card sum
    rw [card_insert_of_not_mem dn,card_union_of_disjoint qf] at n
    have all := universal_if_no_own_second hc uD (by change Q.card=0; omega)
    have sub' : insert c (O.erase u)⊆G.neighborFinset u := by
      intro y ym
      rcases mem_insert.mp ym with rfl|h
      · exact (mem_neighborFinset G u _).mpr cu.symm
      obtain ⟨ne,yl⟩ := mem_erase.mp h
      exact (mem_neighborFinset G u y).mpr ((all y yl).resolve_left ne)
    have l := card_le_card sub'
    rw [card_insert_of_not_mem (fun h=>cOff (mem_erase.mp h).2),
      card_erase_of_mem uD,card_neighborFinset_eq_degree] at l
    change O.card-1+1≤G.degree u at l
    omega
  have nbr : ∃ t∈O,G.Adj u t := by
    let Z := ↑(↑O : Set V)
    obtain ⟨p⟩ := (shore_connected D).preconnected (⟨u,uD⟩ : Z) ⟨v,vD⟩
    cases p with
    | nil => exact (uv rfl).elim
    | @cons _ t _ e q => exact ⟨t.val,t.property,e⟩
  obtain ⟨t,tO,ut⟩ := nbr
  have tc : ¬G.Adj c t := fun e=>ut.ne.symm (onlyC t tO e)
  have td : ¬G.Adj d t := fun e=>noB tO e ut
  let N := inside G O u
  have tN : t∈N := mem_filter.mpr ⟨tO,ut⟩
  have N3 : N.card≤3 := by
    have off : c∉N := fun e=>cOff (mem_filter.mp e).1
    have sub : insert c N⊆G.neighborFinset u := by
      intro z h
      exact (mem_neighborFinset G u z).mpr
        ((mem_insert.mp h).elim (fun e=>e.symm ▸ cu.symm) (fun e=>(mem_filter.mp e).2))
    have m := card_le_card sub
    rw [card_insert_of_not_mem off,card_neighborFinset_eq_degree] at m
    omega
  have sub : G.neighborFinset t ⊆ insert u (N.erase t∪Q) := by
    intro z zn
    have tz := (mem_neighborFinset G t z).mp zn
    rcases bdy t tO z tz with rfl|rfl|zD
    · exact (tc tz.symm).elim
    · exact (td tz.symm).elim
    by_cases ze : z=u
    · exact mem_insert.mpr (.inl ze)
    apply mem_insert_of_mem
    by_cases uz : G.Adj u z
    · exact mem_union_left _ (mem_erase.mpr ⟨tz.ne.symm,mem_filter.mpr ⟨zD,uz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zD,d2 hc (Ne.symm ze) uz ut tz⟩)
  have count := (card_le_card sub).trans (card_insert_le u (N.erase t∪Q))
  rw [card_neighborFinset_eq_degree] at count
  have j := card_union_le (N.erase t) Q
  rw [card_erase_of_mem tN] at j
  have t5 := (degree u t ut.ne).resolve_left low
  have pos := card_pos.mpr ⟨t,tN⟩
  omega

private theorem common_shore_cannot_be_small
    (two : G.dist a b=2)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C)
    (only : ∀ z∈Shore C,G.Adj a z → G.Adj b z → z=x)
    (foreign : (portColor D a).card+(portColor D b).card≤5)
    (small : (Shore C).card≤4) : False := by
  classical
  let L := Shore C
  have cardPos : 0<L.card := card_pos.mpr ⟨x,xC⟩
  have exclusiveLow {z : V} (zL : z∈L) (zx : z≠x) : ¬5≤G.degree z := by
    have one (c d : V) (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (dz : ¬G.Adj d z) :
        G.neighborFinset z⊆insert c (L.erase z) := by
      intro w wn
      have zw := (mem_neighborFinset G z w).mp wn
      have h : w=c ∨ w=d ∨ w∈L := by
        rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact shore_closed C z zL w zw
        rcases shore_closed C z zL w zw with q|q|q
        · exact .inr (.inl q)
        · exact .inl q
        exact .inr (.inr q)
      rcases h with rfl|rfl|wl
      · exact mem_insert_self _ _
      · exact (dz zw.symm).elim
      exact mem_insert_of_mem (mem_erase.mpr ⟨zw.ne.symm,wl⟩)
    have bound (c : V) (s : G.neighborFinset z⊆insert c (L.erase z)) :
        ¬5≤G.degree z := by
      have k := (card_le_card s).trans (card_insert_le c _)
      rw [card_neighborFinset_eq_degree,card_erase_of_mem zL] at k
      change L.card≤4 at small
      omega
    by_cases az : G.Adj a z
    · exact bound a (one a b (.inl ⟨rfl,rfl⟩) (fun bz=>zx (only z zL az bz)))
    exact bound b (one b a (.inr ⟨rfl,rfl⟩) az)
  have allLow (h : L.card≤3) (z : V) (zl : z∈L) : ¬5≤G.degree z := by
    have sub : G.neighborFinset z⊆insert a (insert b (L.erase z)) := by
      intro y yn
      have zy := (mem_neighborFinset G z y).mp yn
      rcases shore_closed C z zl y zy with rfl|rfl|yl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)
      exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨zy.ne.symm,yl⟩))
    have k := card_le_card sub
    rw [card_neighborFinset_eq_degree] at k
    have ca := card_insert_le a (insert b (L.erase z))
    have cb := card_insert_le b (L.erase z)
    rw [card_erase_of_mem zl] at cb
    omega
  by_cases le3 : 3≤L.card
  · have cnt : 1<(L.erase x).card := by
      rw [show (L.erase x).card=L.card-1 from card_erase_of_mem (show x∈L from xC)]
      omega
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp cnt
    obtain ⟨ux,ul⟩ := mem_erase.mp um
    obtain ⟨vx,vl⟩ := mem_erase.mp vm
    exact (degree u v uv).elim (exclusiveLow ul ux) (exclusiveLow vl vx)
  by_cases l1 : L.card=1
  · have al := (degree x a (fun e=>(shore_off C).1 (e ▸ xC))).resolve_left
      (allLow (by omega) x xC)
    have bl := (degree x b (fun e=>(shore_off C).2 (e ▸ xC))).resolve_left
      (allLow (by omega) x xC)
    have ca := count_cut_degree_on_two_shores cd cover two (.inl rfl)
    have cb := count_cut_degree_on_two_shores cd cover two (.inr rfl)
    have h1 := card_le_card (filter_subset (G.Adj a) L)
    have h2 := card_le_card (filter_subset (G.Adj b) L)
    change (portColor C a).card≤L.card at h1
    change (portColor C b).card≤L.card at h2
    omega
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<L.card by omega)
  exact (degree u v uv).elim (allLow (by omega) u um) (allLow (by omega) v vm)

private theorem common_shore_count_by_charges
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (only : ∀ z∈Shore C,G.Adj a z → G.Adj b z → z=x)
    (near : ∀ z∈Shore C,G.dist x z≤2) :
    (Shore C).card≤1+(secondShore C a).card+(secondShore C b).card+
      (secondShore C x).card := by
  classical
  let A := secondShore C a
  let B := secondShore C b
  let X := secondShore C x
  have cover : Shore C⊆insert x (A∪B∪X) := by
    intro z zC
    by_cases zx : z=x
    · exact mem_insert.mpr (.inl zx)
    apply mem_insert_of_mem
    by_cases adj : G.Adj x z
    · apply mem_union_left
      by_cases az : G.Adj a z
      · have nb : ¬G.Adj b z := fun bz=>zx (only z zC az bz)
        exact mem_union_right _ (mem_inter.mpr ⟨zC,
          d2 hc (fun e=>(shore_off C).2 (e.symm ▸ zC)) nb bx adj⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨zC,
        d2 hc (fun e=>(shore_off C).1 (e.symm ▸ zC)) az ax adj⟩)
    have lo := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm zx) adj
    have hi := near z zC
    exact mem_union_right _ (mem_inter.mpr ⟨zC,by simp [DistanceTwo,show G.dist x z=2 by omega]⟩)
  have c := (card_le_card cover).trans (card_insert_le x _)
  have q := card_union_le (A∪B) X
  have r := card_union_le A B
  change _≤1+A.card+B.card+X.card
  omega

/-- Under the original degree-five hypotheses, a two-component
distance-two separator cannot have exactly one common neighbor. -/
theorem no_unique_common_across_two_components
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (only : ∀ z∈Shore C,G.Adj a z → G.Adj b z → z=x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z)) : False := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have two' : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have aOff : a∉Shore C ∧ a∉Shore D := ⟨(shore_off C).1,(shore_off D).1⟩
  have bOff : b∉Shore C ∧ b∉Shore D := ⟨(shore_off C).2,(shore_off D).2⟩
  let S : Split G a b :=
    ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,shore_connected C,
      (fun u uc v vd e=>by
        rcases shore_closed C u uc v e with rfl|rfl|vC
        · exact (shore_off D).1 vd
        · exact (shore_off D).2 vd
        exact disjoint_left.mp (shore_disjoint cd) vC vd),
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  have p4 := more_than_three_foreign_exclusive_ports hc two even conn degree cd cover xC ax bx only none
  have near := (Split.Five.near_universal_at_four_foreign S hc even conn xC ax bx p4).2
  have leftCount := common_shore_count_by_charges hc xC ax bx only near
  let PA := portColor D a
  let PB := portColor D b
  let X := secondShore C x
  have eq : PA∪PB=cutPorts D := by
    ext q
    change q∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      q∈(Shore D).filter (fun q=>G.Adj a q ∨ G.Adj b q)
    simp [and_or_left]
  have dis : Disjoint PA PB := by
    apply disjoint_left.mpr
    intro q h k
    exact none q (mem_filter.mp h).1 ⟨(mem_filter.mp h).2,(mem_filter.mp k).2⟩
  have tally := congrArg Finset.card eq
  rw [card_union_of_disjoint dis] at tally
  have total := foreign_ports_le_five_at_common hc even xC ax bx
    (T:=({D} : Finset (Cmp (G:=G) (a:=a) (b:=b)))) (by simpa using cd)
  rw [sum_singleton] at total
  have pt : PA.card+PB.card≤5 := by omega
  have NX : X.card+PA.card+PB.card≤5 := by
    have no : Disjoint X (cutPorts D) :=
      (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
    have inD : (cutPorts D)⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zD,hit⟩ := mem_filter.mp zp
      have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xC (e.symm ▸ zD)
      have n : ¬G.Adj x z := by
        intro e
        rcases shore_closed C x xC z e with rfl|rfl|zl
        · exact (shore_off D).1 zD
        · exact (shore_off D).2 zD
        exact disjoint_left.mp (shore_disjoint cd) zl zD
      exact hit.elim (fun e=>d2 hc ne n ax.symm e) (fun e=>d2 hc ne n bx.symm e)
    have u := card_le_card (union_subset (show X⊆DistanceTwo G x from inter_subset_right) inD)
    rw [card_union_of_disjoint no] at u
    have budget := distanceTwo_le_of_even 5 x (even x)
    omega
  have aE := two_shore_budget cd bOff two even
  have bE := two_shore_budget cd aOff two' even
  have small (sh : (Shore C).card≤4) : False :=
    common_shore_cannot_be_small two degree cd cover xC only pt sh
  obtain ⟨u,uD,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vD,bv⟩ := shore_hit_b ab conn D
  have auP : u∈PA := mem_filter.mpr ⟨uD,au⟩
  have bvP : v∈PB := mem_filter.mpr ⟨vD,bv⟩
  have ap := card_pos.mpr ⟨u,auP⟩
  have bp := card_pos.mpr ⟨v,bvP⟩
  have lonely {c d v w : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
      (cx : G.Adj c x) (dx : G.Adj d x)
      (vD : v∈Shore D) (cv : G.Adj c v) (wD : w∈Shore D) (dw : G.Adj d w)
      (cv1 : (portColor D c).card=1) :
      False := by
    have oo : ∀ z∈Shore C,G.Adj c z → G.Adj d z → z=x := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact only
      exact fun z zm h k=>only z zm k h
    have nn : ∀ z∈Shore D,¬(G.Adj c z ∧ G.Adj d z) := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact none
      exact fun z zm h=>none z zm ⟨h.2,h.1⟩
    have dv : ¬G.Adj d v := fun h=>nn v vD ⟨cv,h⟩
    have cw : ¬G.Adj c w := fun h=>nn w wD ⟨h,dw⟩
    have cOff : c∉Shore C ∧ c∉Shore D := by
      rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact aOff
      exact bOff
    have dOff : d∉Shore C ∧ d∉Shore D := by
      rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
      · exact bOff
      exact aOff
    have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
    have cs : G.dist c d=2 := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact two
      exact two'
    have ds : G.dist d c=2 := by rwa [SimpleGraph.dist_comm]
    have swap : (d=a ∧ c=b) ∨ (d=b ∧ c=a) :=
      perm.elim (fun e=>.inr ⟨e.2,e.1⟩) (fun e=>.inl ⟨e.2,e.1⟩)
    have sums : (portColor D c).card+(portColor D d).card≤5 ∧
        X.card+(portColor D c).card+(portColor D d).card≤5 := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨pt,NX⟩
      change PB.card+PA.card≤5 ∧ X.card+PB.card+PA.card≤5
      exact ⟨by omega,by omega⟩
    by_cases v5 : 5≤G.degree v
    · by_cases d3 : (portColor D d).card≤3
      · exact lonely_port_low_if_other_at_most_three hc two even degree cd cover perm
          xC cx dx oo vD cv dv wD dw cw cv1 d3 v5
      have d4 : (portColor D d).card=4 := by have := sums.1; omega
      have Xzero : X.card=0 := by have := sums.2; omega
      have all := all_common_side_adjacent_when_high_lonely hc cd perm cs even
        cOff.1 dOff ⟨x,xC,cx⟩ vD cv dv v5 cv1
      have leftZero : (secondShore C c).card=0 := by
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_not_mem.mpr
        intro z hz
        have h1 := dist_eq_one_iff_adj.mpr (all z (mem_inter.mp hz).1)
        have h2 : G.dist c z=2 := by simpa [DistanceTwo] using (mem_inter.mp hz).2
        omega
      obtain ⟨t,td,th⟩ := anywhere_high_of_two degree (show 2≤(portColor D d).card by omega)
      obtain ⟨tD,dt⟩ := mem_filter.mp td
      have k := charge_at_high_port swap hc tD dt th
      rw [if_neg (fun e=>nn _ tD ⟨e,dt⟩)] at k
      change 5≤(portColor D d).card+(secondShore D d).card at k
      have cap := two_shore_budget cd cOff ds even
      have z := leftCount
      change (Shore C).card≤1+(secondShore C a).card+(secondShore C b).card+X.card at z
      have leftsum : (secondShore C a).card+(secondShore C b).card≤3 := by
        rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
      exact small (by omega)
    have ch := (degree v c (fun e=>cOff.2 (e ▸ vD))).resolve_left v5
    have deg := count_cut_degree_on_two_shores cd cover two ct
    have four : 4≤(portColor C c).card := by omega
    exact low_lonely_impossible_against_four hc even degree cd perm vD cv dv v5 wD dw cw cv1 four
  by_cases a1 : PA.card=1
  · exact lonely (.inl ⟨rfl,rfl⟩) ax bx uD au vD bv a1
  by_cases b1 : PB.card=1
  · exact lonely (.inr ⟨rfl,rfl⟩) bx ax vD bv uD au b1
  obtain ⟨u,up,u5⟩ := anywhere_high_of_two degree (show 2≤PA.card by omega)
  obtain ⟨v,vp,v5⟩ := anywhere_high_of_two degree (show 2≤PB.card by omega)
  obtain ⟨uD,au⟩ := mem_filter.mp up
  obtain ⟨vD,bv⟩ := mem_filter.mp vp
  have ka := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc uD au u5
  rw [if_neg (fun e=>none _ uD ⟨au,e⟩)] at ka
  change 5≤PA.card+(secondShore D a).card at ka
  have kb := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vD bv v5
  rw [if_neg (fun e=>none _ vD ⟨e,bv⟩)] at kb
  change 5≤PB.card+(secondShore D b).card at kb
  change (Shore C).card≤1+(secondShore C a).card+(secondShore C b).card+X.card at leftCount
  exact small (by omega)

#print axioms no_unique_common_across_two_components
end Graffiti189LongestPath.CrossSaturation.FiveActualCut

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem no_unique_common_at_actual_five_distance_two {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (one : (CommonPorts G a b).card=1)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    False := by
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
  have sole {z : V} (az : G.Adj a z) (bz : G.Adj b z) : z=x := by
    have hm : z∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a z).mpr az,(mem_neighborFinset G b z).mpr bz⟩
    have hx : x∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr xb.symm⟩
    exact card_le_one.mp one.le z hm x hx
  have none (z : V) (zD : z∈Shore D) : ¬(G.Adj a z ∧ G.Adj b z) := by
    intro h
    exact disjoint_left.mp dis xC (sole h.1 h.2 ▸ zD)
  exact no_unique_common_across_two_components hc two even conn degree DC.symm cover
    xC ax xb.symm (fun z _ az bz=>sole az bz) none

#print axioms no_unique_common_at_actual_five_distance_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
