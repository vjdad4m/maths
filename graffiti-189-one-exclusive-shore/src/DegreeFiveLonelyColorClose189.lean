import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveSmallExclusiveFull189
import DegreeFiveTwoExclusivePath189
import DegreeFiveRouteBasic189
import DegreeFiveUniquePortClosureTest189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget foreign_exclusive_subset_at_port
  from DegreeFiveThreeForeignImpossible189
open private boundary_permuted walk_three_data
  from DegreeFiveExclusiveGateway189
open private common_four_is_clique from DegreeFiveTwoExclusivePath189
open private lonely_opposite_high_and_common_size_four from DegreeFiveExclusiveGateway189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private universal_if_no_own_second from DegreeFiveThreeForeignImpossible189
open private other_color_at_least_three_on_four_shore from DegreeFiveSmallExclusiveFull189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem lonely_high_port_geometry_of_no_mixed
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) (four : (portColor C c).card=4)
    (noB : ∀ {z : V}, z∈Shore D → G.Adj d z → ¬G.Adj u z) :
    ∃ q∈Shore D, (inside G (Shore D) u).card=4 ∧ secondShore D u={q} ∧
      (∀ z∈Shore D,G.Adj d z → ¬G.Adj u z) ∧
      (∀ t∈inside G (Shore D) u, 5≤G.degree t →
        G.Adj t q ∧ ∀ z∈inside G (Shore D) u,z≠t → G.Adj t z) ∧
      (∀ z∈Shore D,z≠u → ¬ G.Adj u z → z≠q → G.Adj q z) := by
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
  obtain ⟨t,tN,t5⟩ := anywhere_high_of_two degree (show 2≤N.card by omega)
  have allSub (t : V) (tN : t∈N) :
      G.neighborFinset t⊆insert u (N.erase t∪Q) := by
    obtain ⟨tO,ut⟩ := mem_filter.mp tN
    have tc : ¬G.Adj c t := fun e=>ut.ne.symm (onlyC t tO e)
    have td : ¬G.Adj d t := fun e=>noB tO e ut
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
  let Z := insert u (N.erase t∪Q)
  have tsub : G.neighborFinset t⊆Z := allSub t tN
  have zCap := card_insert_le u (N.erase t∪Q)
  change Z.card≤_ at zCap
  have zCap' := card_union_le (N.erase t) Q
  rw [card_erase_of_mem tN] at zCap'
  have zCount := card_le_card tsub
  rw [card_neighborFinset_eq_degree] at zCount
  have Qeq1 : Q.card=1 := by omega
  obtain ⟨w,wEq⟩ := card_eq_one.mp Qeq1
  have wQ : w∈Q := by simp [wEq]
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
  refine ⟨w,(mem_inter.mp wQ).1,N4,wEq,fun z zl dz=>noB zl dz,?_,?_⟩
  · intro v vN v5
    have vc := allSub v vN
    have bp := card_insert_le u (N.erase v∪Q)
    have bq := card_union_le (N.erase v) Q
    have erased : (N.erase v).card=3 := by rw [card_erase_of_mem vN,N4]
    rw [erased,Qeq1] at bq
    have bp' : (insert u (N.erase v∪Q)).card≤5 :=
      bp.trans (Nat.add_le_add_right bq 1)
    have eq := eq_of_subset_of_card_le vc (by
      rw [card_neighborFinset_eq_degree]
      exact bp'.trans v5)
    refine ⟨(mem_neighborFinset G v w).mp
      (eq.symm ▸ mem_insert_of_mem (mem_union_right _ wQ)),?_⟩
    intro z zN zv
    exact (mem_neighborFinset G v z).mp
      (eq.symm ▸ mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨zv,zN⟩)))
  intro z zD zu no zw
  apply far z
  refine mem_sdiff.mpr ⟨zD,?_⟩
  intro hz
  rcases mem_insert.mp hz with rfl|h
  · exact zu rfl
  rcases mem_union.mp h with zN|zQ
  · exact no (mem_filter.mp zN).2
  exact zw (by simpa [wEq] using zQ)

private theorem lonely_must_touch_other_color
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) (dbl : 2≤(portColor D d).card)
    (four : (portColor C c).card=4) (size : (Shore C).card=4)
    (noB : ∀ {z : V},z∈Shore D → G.Adj d z → ¬G.Adj u z) : False := by
  classical
  let N := inside G (Shore D) u
  let H := N.filter (fun z=>5≤G.degree z)
  obtain ⟨q,qD,n4,qe,notB,near,far⟩ := lonely_high_port_geometry_of_no_mixed hc two even degree cd perm
    uD cu du u5 one four noB
  change N.card=4 at n4
  have lo : (N.filter (fun z=>¬5≤G.degree z)).card≤1 := by
    apply card_le_one.mpr
    intro t tm w wm
    apply Classical.byContradiction
    intro ne
    exact (degree t w ne).elim (mem_filter.mp tm).2 (mem_filter.mp wm).2
  have eq := filter_card_add_filter_neg_card_eq_card (s:=N) (fun z=>5≤G.degree z)
  change H.card+_=N.card at eq
  have h3 : 3≤H.card := by omega
  have exists_other : ∃ v∈portColor D d,v≠q := by
    apply Classical.byContradiction
    intro bad
    have small : portColor D d⊆{q} := by
      intro v vv
      apply mem_singleton.mpr
      exact Classical.byContradiction (fun h=>bad ⟨v,vv,h⟩)
    have h := card_le_card small
    rw [card_singleton] at h
    omega
  obtain ⟨v,vP,vq⟩ := exists_other
  obtain ⟨vD,dv⟩ := mem_filter.mp vP
  have vu : v≠u := fun e=>du (e ▸ dv)
  have uv := notB v vD dv
  have qv := far v vD vu uv vq
  have local2 : H⊆DistanceTwo G v := by
    intro t tm
    obtain ⟨tn,th⟩ := mem_filter.mp tm
    have ut := (mem_filter.mp tn).2
    have tq := (near t tn th).1
    have vt : v≠t := fun e=>uv (e.symm ▸ ut)
    have nvt : ¬G.Adj v t := by
      intro e
      have v2 := d2 hc vu.symm uv ut e.symm
      have h : v∈secondShore D u := mem_inter.mpr ⟨vD,v2⟩
      exact vq (by simpa [qe] using h)
    exact d2 hc vt nvt qv.symm tq.symm
  let P := portColor C d
  have f3 : 3≤P.card := other_color_at_least_three_on_four_shore degree size perm
  have foreign : P⊆DistanceTwo G v := foreign_exclusive_subset_at_port hc cd
    (perm.elim (fun e=>.inr e.2) (fun e=>.inl e.2)) vD dv
  have dis : Disjoint H P := by
    apply disjoint_left.mpr
    intro z zh zp
    exact disjoint_left.mp (shore_disjoint cd) (mem_filter.mp zp).1
      (mem_filter.mp (mem_filter.mp zh).1).1
  have h := card_le_card (union_subset local2 foreign)
  rw [card_union_of_disjoint dis] at h
  have b := distanceTwo_le_of_even 5 v (even v)
  omega


private theorem size_five_of_lonely_mixed_port
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {u v c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (_vD : v∈Shore D) (dv : G.Adj d v) (uv : G.Adj u v)
    (one : (portColor D c).card=1) (four : (portColor C c).card=4) :
    (Shore D).card=5 := by
  classical
  let F := portColor C c
  let Q := secondShore D u
  have cOff : c∉Shore D := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact (shore_off D).1
    exact (shore_off D).2
  have dOff : d∉Shore C ∧ d∉Shore D := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have bg : d∈DistanceTwo G u :=
    d2 hc (fun e=>dOff.2 (e ▸ uD)) (fun e=>du e.symm) uv dv.symm
  have f := foreign_exclusive_subset_at_port hc cd ct uD cu
  change F⊆DistanceTwo G u at f
  have offs : d∉Q∪F := fun h=>(mem_union.mp h).elim (fun h=>dOff.2 (mem_inter.mp h).1)
    (fun h=>dOff.1 (mem_filter.mp h).1)
  have dis : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have sub : insert d (Q∪F)⊆DistanceTwo G u := by
    intro z h
    rcases mem_insert.mp h with rfl|h
    · exact bg
    exact (mem_union.mp h).elim (fun q=>(mem_inter.mp q).2) (fun q=>f q)
  have k := card_le_card sub
  rw [card_insert_of_not_mem offs,card_union_of_disjoint dis] at k
  have cap := distanceTwo_le_of_even 5 u (even u)
  change F.card=4 at four
  have zero : Q.card=0 := by omega
  have all := universal_if_no_own_second hc uD zero
  have ch : (Shore D).erase u ⊆ secondShore D c := by
    intro z p
    obtain ⟨zu,zD⟩ := mem_erase.mp p
    have nz : ¬G.Adj c z := by
      intro cz
      have em := card_le_one.mp one.le z (show z∈portColor D c from mem_filter.mpr ⟨zD,cz⟩)
        u (mem_filter.mpr ⟨uD,cu⟩)
      exact zu em
    exact mem_inter.mpr ⟨zD,d2 hc (fun e=>cOff (e.symm ▸ zD)) nz cu ((all z zD).resolve_left zu)⟩
  have l := card_le_card ch
  rw [card_erase_of_mem uD] at l
  have budget := two_shore_budget cd dOff dist even
  have nc : G.neighborFinset u⊆insert c ((Shore D).erase u) := by
    intro z h
    have e := (mem_neighborFinset G u z).mp h
    rcases boundary_permuted perm u uD z e with rfl|rfl|zD
    · exact mem_insert_self _ _
    · exact (du e.symm).elim
    exact mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,zD⟩)
  have high := (card_le_card nc).trans (card_insert_le c _)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem uD] at high
  omega

private theorem exclusive_five_is_clique
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {D : Cmp (G:=G) (a:=a) (b:=b)} (five : (Shore D).card=5)
    (none : ∀ u∈Shore D,¬(G.Adj a u ∧ G.Adj b u)) :
    CompleteOn G (Shore D) := by
  classical
  have upper {u v : V} (uD : u∈Shore D) (vD : v∈Shore D) (uv : u≠v)
      (no : ¬G.Adj u v) : ¬5≤G.degree u := by
    have one {c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (du : ¬G.Adj d u) :
        G.neighborFinset u⊆insert c (((Shore D).erase u).erase v) := by
      intro z hz
      have uz := (mem_neighborFinset G u z).mp hz
      rcases boundary_permuted perm u uD z uz with rfl|rfl|zl
      · exact mem_insert_self _ _
      · exact (du uz.symm).elim
      exact mem_insert_of_mem (mem_erase.mpr ⟨fun e=>no (e ▸ uz),
        mem_erase.mpr ⟨uz.ne.symm,zl⟩⟩)
    have bound (c : V) (sub : G.neighborFinset u⊆insert c (((Shore D).erase u).erase v)) :
        ¬5≤G.degree u := by
      have v' : v∈(Shore D).erase u := mem_erase.mpr ⟨uv.symm,vD⟩
      have h := (card_le_card sub).trans (card_insert_le c _)
      rw [card_neighborFinset_eq_degree,card_erase_of_mem v',card_erase_of_mem uD,five] at h
      omega
    by_cases au : G.Adj a u
    · exact bound a (one (.inl ⟨rfl,rfl⟩) (fun bu=>none _ uD ⟨au,bu⟩))
    exact bound b (one (.inr ⟨rfl,rfl⟩) au)
  intro u uD v vD uv
  apply Classical.byContradiction
  intro no
  exact (degree u v uv).elim (upper uD vD uv no) (upper vD uD uv.symm (fun e=>no e.symm))

theorem traceable_of_lonely_color_in_exclusive_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (p : ((portColor D a).card=1 ∧ 2≤(portColor D b).card) ∨
         ((portColor D b).card=1 ∧ 2≤(portColor D a).card)) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
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
  have uv : u≠v := fun e=>av (e ▸ au)
  have make {c d s t : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
      (cx : G.Adj c x) (sD : s∈Shore D) (cs : G.Adj c s) (ds : ¬ G.Adj d s)
      (tD : t∈Shore D) (dt : G.Adj d t) (ct : ¬ G.Adj c t)
      (one : (portColor D c).card=1) (other : 2≤(portColor D d).card)
      (cap : (portColor C c).card≤4) :
      (Shore C).card=4 ∧ (Shore D).card=5 := by
    obtain ⟨s5,four,ss⟩ := lonely_opposite_high_and_common_size_four hc two even degree cd
      cover perm xC cx sD cs ds tD dt ct one cap
    have exists_mixed : ∃ w∈Shore D,G.Adj d w ∧ G.Adj s w := by
      apply Classical.byContradiction
      intro no
      exact lonely_must_touch_other_color hc two even degree cd perm sD cs ds s5 one other
        four ss (fun wD dw sw=>no ⟨_,wD,dw,sw⟩)
    obtain ⟨w,wD,dw,sw⟩ := exists_mixed
    exact ⟨ss,size_five_of_lonely_mixed_port hc two even cd perm sD cs ds s5 wD dw sw one four⟩
  have sizes : (Shore C).card=4 ∧ (Shore D).card=5 := by
    rcases p with ⟨one,n⟩|⟨one,n⟩
    · exact make (.inl ⟨rfl,rfl⟩) ax uD au bu vD bv av one n
        (opposite_ports_at_exclusive_le_four T hc even uD au bu)
    exact make (.inr ⟨rfl,rfl⟩) bx vD bv av uD au bu one n
      (opposite_ports_at_exclusive_le_four T.flip hc even vD bv av)
  obtain ⟨r,rp,rs⟩ := path_between_in_clique (Shore D)
    (exclusive_five_is_clique degree sizes.2 none) uD vD uv
  have middle : RouteOn G (insert b (insert a (Shore D))) a b := by
    have q : RouteOn G (Shore D) u v := ⟨r,rp,rs⟩
    have p := q.prefix au (shore_off D).1
    exact p.suffix bv.symm (fun h=>(mem_insert.mp h).elim ab.symm (shore_off D).2)
  obtain ⟨y,q,qp,qs⟩ := rooted_path_in_clique (Shore C) (common_four_is_clique degree sizes.1) xC
  have wing : RouteOn G (Shore C) x y := ⟨q,qp,qs⟩
  have off : Disjoint (insert b (insert a (Shore D))) (Shore C) := by
    apply disjoint_left.mpr
    intro z h zC
    rcases mem_insert.mp h with rfl|h
    · exact (shore_off C).2 zC
    rcases mem_insert.mp h with rfl|h
    · exact (shore_off C).1 zC
    exact disjoint_left.mp (shore_disjoint cd) zC h
  obtain ⟨w,wp,ws⟩ := middle.join wing off bx
  refine ⟨a,y,w,wp,fun z=>(ws z).mpr ?_⟩
  rcases cover z with rfl|rfl|zC|zD
  · simp
  · simp
  · exact mem_union_right _ zC
  exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zD))

#print axioms traceable_of_lonely_color_in_exclusive_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
