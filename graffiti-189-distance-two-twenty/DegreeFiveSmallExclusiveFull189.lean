import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveLonelyPortGeometry189
import DegreeFiveTwoExclusivePath189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor foreign_exclusive_subset_at_port from DegreeFiveThreeForeignImpossible189
open private boundary_permuted lonely_opposite_high_and_common_size_four from DegreeFiveExclusiveGateway189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private two_walk_middle from DistanceTwoCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem other_color_at_least_three_on_four_shore
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (size : (Shore C).card=4)
    {c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) :
    3≤(portColor C d).card := by
  classical
  have bad (z : V) (zC : z∈Shore C) (no : ¬G.Adj d z) : ¬5≤G.degree z := by
    have sub : G.neighborFinset z⊆insert c ((Shore C).erase z) := by
      intro w wm
      have zw := (mem_neighborFinset G z w).mp wm
      rcases boundary_permuted perm z zC w zw with rfl|rfl|wC
      · exact mem_insert_self _ _
      · exact (no zw.symm).elim
      exact mem_insert_of_mem (mem_erase.mpr ⟨zw.ne.symm,wC⟩)
    have h := (card_le_card sub).trans (card_insert_le c _)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zC,size] at h
    omega
  have lo : ((Shore C).filter (fun z=>¬G.Adj d z)).card≤1 := by
    apply card_le_one.mpr
    intro u um v vm
    apply Classical.byContradiction
    intro ne
    obtain ⟨ul,un⟩ := mem_filter.mp um
    obtain ⟨vl,vn⟩ := mem_filter.mp vm
    exact (degree u v ne).elim (bad u ul un) (bad v vl vn)
  have cnt := filter_card_add_filter_neg_card_eq_card (s:=Shore C) (G.Adj d)
  change _≤(portColor C d).card
  change (portColor C d).card+_= _ at cnt
  omega

private theorem no_three_exclusive_ports_oriented
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) (dbl : (portColor D d).card=2)
    (four : (portColor C c).card=4) (size : (Shore C).card=4)
    (p3 : (cutPorts D).card=3) : False := by
  classical
  let N := inside G (Shore D) u
  let H := N.filter (fun z=>5≤G.degree z)
  obtain ⟨q,qD,n4,qe,noB,near,far⟩ := lonely_high_port_geometry hc two even degree cd perm
    uD cu du u5 one four p3.le
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
  have uv := noB v vD dv
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

theorem no_three_exclusive_foreign_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (p3 : (cutPorts D).card=3) : False := by
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
  have posP := card_pos.mpr (show P.Nonempty from ⟨u,mem_filter.mpr ⟨uD,au⟩⟩)
  have posQ := card_pos.mpr (show Q.Nonempty from ⟨v,mem_filter.mpr ⟨vD,bv⟩⟩)
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
  by_cases a1 : P.card=1
  · have b2 : Q.card=2 := by omega
    have cap := opposite_ports_at_exclusive_le_four T hc even uD au bu
    change (portColor C a).card≤4 at cap
    obtain ⟨u5,four,ss⟩ := lonely_opposite_high_and_common_size_four hc two even
      degree cd cover (.inl ⟨rfl,rfl⟩) xC ax uD au bu vD bv av a1 cap
    exact no_three_exclusive_ports_oriented hc two even degree cd
      (.inl ⟨rfl,rfl⟩) uD au bu u5 a1 b2 four ss p3
  have b1 : Q.card=1 := by omega
  have a2 : P.card=2 := by omega
  have cap := opposite_ports_at_exclusive_le_four T.flip hc even vD bv av
  change (portColor C b).card≤4 at cap
  obtain ⟨v5,four,ss⟩ := lonely_opposite_high_and_common_size_four hc two even
    degree cd cover (.inr ⟨rfl,rfl⟩) xC bx vD bv av uD au bu b1 cap
  exact no_three_exclusive_ports_oriented hc two even degree cd
    (.inr ⟨rfl,rfl⟩) vD bv av v5 b1 a2 four ss p3


theorem traceable_of_at_most_three_exclusive_foreign_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (p : (cutPorts D).card≤3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  obtain ⟨u,uD,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vD,bv⟩ := shore_hit_b ab conn D
  have uv : u≠v := fun e=>none u uD ⟨au,e.symm ▸ bv⟩
  have lo : 2≤(cutPorts D).card := one_lt_card.mpr
    ⟨u,mem_filter.mpr ⟨uD,.inl au⟩,v,mem_filter.mpr ⟨vD,.inr bv⟩,uv⟩
  have no3 : (cutPorts D).card≠3 := no_three_exclusive_foreign_ports hc two even conn degree
    cd cover xC ax bx none
  exact traceable_of_two_exclusive_foreign_ports hc two even conn degree cd cover
    xC ax bx none (by omega)

#print axioms no_three_exclusive_foreign_ports
#print axioms traceable_of_at_most_three_exclusive_foreign_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_of_actual_five_distance_two_with_small_exclusive_side {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (profile : ∃ D : (CutGraph (G:=G) a b).ConnectedComponent,
      (∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z)) ∧ (cutPorts D).card≤3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
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
  obtain ⟨E,none,ports⟩ := profile
  have ec : E≠C := fun e=>none x (e.symm ▸ xC) ⟨ax,xb.symm⟩
  have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
  rw [hD] at et
  have ed := mem_singleton.mp et
  exact traceable_of_at_most_three_exclusive_foreign_ports hc two even conn degree DC.symm
    cover xC ax xb.symm (ed ▸ none) (ed ▸ ports)

#print axioms traceable_of_actual_five_distance_two_with_small_exclusive_side
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
