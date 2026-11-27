import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveDistanceTwoSingletonClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private abbrev Cmp := (CutGraph (G:=G) a b).ConnectedComponent
private noncomputable abbrev portColor (C : Cmp (G:=G) (a:=a) (b:=b)) (c : V) :=
  (Shore C).filter (G.Adj c)

private theorem two_shore_budget {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d : V} (dOff : d∉Shore C ∧ d∉Shore D)
    (two : G.dist c d=2) (even : ∀ x,(EvenFrom G x).card≤6) :
    (secondShore C c).card+(secondShore D c).card≤4 := by
  classical
  let A := secondShore C c
  let B := secondShore D c
  have d2 : d∈DistanceTwo G c := by simp [DistanceTwo,two]
  have dn : d∉A∪B := by
    intro h
    exact (mem_union.mp h).elim (fun h=>dOff.1 (mem_inter.mp h).1)
      (fun h=>dOff.2 (mem_inter.mp h).1)
  have sub : insert d (A∪B)⊆DistanceTwo G c := by
    intro z hz
    rcases mem_insert.mp hz with rfl|h
    · exact d2
    exact (mem_union.mp h).elim (fun h=>(mem_inter.mp h).2) (fun h=>(mem_inter.mp h).2)
  have dis : Disjoint A B := (shore_disjoint cd).mono inter_subset_left inter_subset_left
  have h := card_le_card sub
  rw [card_insert_of_not_mem dn,card_union_of_disjoint dis] at h
  have cap := distanceTwo_le_of_even 5 c (even c)
  change A.card+B.card≤4
  omega

private theorem all_adj_of_no_second (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {c : V}
    (off : c∉Shore C) (hit : ∃ x∈Shore C,G.Adj c x)
    (zero : (secondShore C c).card=0) :
    ∀ z∈Shore C,G.Adj c z := by
  classical
  obtain ⟨x,xC,cx⟩ := hit
  intro z zC
  let W := ↑(↑(Shore C) : Set V)
  have step {u v : W} (p : (G.induce (↑(Shore C) : Set V)).Walk u v) :
      G.Adj c u.val → G.Adj c v.val := by
    induction p with
    | nil => exact id
    | @cons u w v uw p ih =>
      intro cu
      apply ih
      apply Classical.byContradiction
      intro no
      have w2 := d2 hc (show c≠w.val from fun e=>off (e.symm ▸ w.property)) no cu uw
      have h : w.val∈secondShore C c := mem_inter.mpr ⟨w.property,w2⟩
      have pos := card_pos.mpr ⟨_,h⟩
      omega
  obtain ⟨p⟩ := (shore_connected C).preconnected (⟨x,xC⟩ : W) ⟨z,zC⟩
  exact step p cx

private theorem count_cut_degree_on_two_shores
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (two : G.dist a b=2) {c : V} (cut : c=a ∨ c=b) :
    G.degree c=(portColor C c).card+(portColor D c).card := by
  classical
  have eq : G.neighborFinset c=portColor C c∪portColor D c := by
    ext z
    constructor
    · intro q
      have e := (mem_neighborFinset G c z).mp q
      rcases cover z with rfl|rfl|zC|zD
      · rcases cut with rfl|rfl
        · exact (G.loopless _ e).elim
        · have d := dist_eq_one_iff_adj.mpr e.symm
          omega
      · rcases cut with rfl|rfl
        · have d := dist_eq_one_iff_adj.mpr e
          omega
        · exact (G.loopless _ e).elim
      · exact mem_union_left _ (mem_filter.mpr ⟨zC,e⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨zD,e⟩)
    intro q
    exact (mem_neighborFinset G c z).mpr
      ((mem_union.mp q).elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2))
  have dis := (shore_disjoint cd).mono
    (filter_subset (G.Adj c) (Shore C)) (filter_subset (G.Adj c) (Shore D))
  have h := congrArg Finset.card eq
  rwa [card_neighborFinset_eq_degree,card_union_of_disjoint dis] at h

private theorem color_one_of_all_other {C : Cmp (G:=G) (a:=a) (b:=b)}
    {x c d : V} (xC : x∈Shore C) (dx : G.Adj d x)
    (unique : ∀ z∈Shore C,G.Adj c z → G.Adj d z → z=x)
    (all : ∀ z∈Shore C,G.Adj c z) :
    (portColor C d).card=1 := by
  classical
  have eq : portColor C d={x} := by
    ext z
    rw [mem_singleton]
    constructor
    · intro hz
      obtain ⟨zs,dz⟩ := mem_filter.mp hz
      exact unique z zs (all z zs) dz
    intro h
    subst z
    exact mem_filter.mpr ⟨xC,dx⟩
  simp [eq]

private theorem other_cut_has_three_from_high_common
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)} {x c d : V}
    (xC : x∈Shore C) (dx : G.Adj d x) (x5 : 5≤G.degree x)
    (dOff : d∉Shore C)
    (unique : ∀ z∈Shore C,G.Adj c z → G.Adj d z → z=x)
    (all : ∀ z∈Shore C,G.Adj c z) :
    3≤(secondShore C d).card := by
  classical
  let I := inside G (Shore C) x
  have sub : I⊆secondShore C d := by
    intro z hz
    obtain ⟨zs,xz⟩ := mem_filter.mp hz
    have nd : ¬G.Adj d z := fun e=>xz.ne.symm (unique z zs (all z zs) e)
    exact mem_inter.mpr ⟨zs,d2 hc (fun e=>dOff (e.symm ▸ zs)) nd dx xz⟩
  have cost := card_le_card (shore_neighbor_cover C xC)
  rw [card_neighborFinset_eq_degree] at cost
  change G.degree x≤(insert a (insert b I)).card at cost
  have c1 := card_insert_le a (insert b I)
  have c2 := card_insert_le b I
  have m := card_le_card sub
  omega

private theorem all_common_side_adjacent_when_high_lonely
    (hc : G.Connected) {C D : Cmp (G:=G) (a:=a) (b:=b)}
    (cd : C≠D) {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (two : G.dist c d=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (offC : c∉Shore C) (offD : d∉Shore C ∧ d∉Shore D)
    (hit : ∃ x∈Shore C,G.Adj c x)
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) :
    ∀ z∈Shore C,G.Adj c z := by
  have charge := charge_at_high_port perm hc uD cu u5
  rw [if_neg du] at charge
  change 5≤(portColor D c).card+(secondShore D c).card at charge
  have cap := two_shore_budget cd offD two even
  exact all_adj_of_no_second hc offC hit (by omega)

private theorem lonely_port_low_if_other_at_most_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x c d u v : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (xC : x∈Shore C) (cx : G.Adj c x) (dx : G.Adj d x)
    (only : ∀ q∈Shore C,G.Adj c q → G.Adj d q → q=x)
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u)
    (vD : v∈Shore D) (dv : G.Adj d v) (cv : ¬G.Adj c v)
    (one : (portColor D c).card=1) (le2 : (portColor D d).card≤2) :
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

/-- With a unique common port, an opposite component with at most three
ports must have exactly three, in a 1+2 split; its singleton-color
porter is the unique possible degree-below-five vertex. -/
theorem few_exclusive_ports_force_three_and_low
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (only : ∀ q∈Shore C,G.Adj a q → G.Adj b q → q=x)
    (none : ∀ q∈Shore D,¬(G.Adj a q ∧ G.Adj b q))
    (p : (cutPorts D).card≤3) :
    ((portColor D a).card=1 ∧ (portColor D b).card=2 ∧
      ∀ u∈portColor D a, ¬5≤G.degree u) ∨
    ((portColor D a).card=2 ∧ (portColor D b).card=1 ∧
      ∀ u∈portColor D b, ¬5≤G.degree u) := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  obtain ⟨u,uD,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vD,bv⟩ := shore_hit_b ab conn D
  have bu : ¬G.Adj b u := fun e=>none u uD ⟨au,e⟩
  have av : ¬G.Adj a v := fun e=>none v vD ⟨e,bv⟩
  have uv : u≠v := fun e=>av (e ▸ au)
  have dis : Disjoint (portColor D a) (portColor D b) := by
    apply disjoint_left.mpr
    intro q ha hb
    exact none q (mem_filter.mp ha).1 ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩
  have eq : portColor D a∪portColor D b=cutPorts D := by
    ext q
    change q∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      q∈(Shore D).filter (fun q=>G.Adj a q ∨ G.Adj b q)
    simp [and_or_left]
  have h := congrArg Finset.card eq
  rw [card_union_of_disjoint dis] at h
  have ap : 1≤(portColor D a).card := card_pos.mpr ⟨u,mem_filter.mpr ⟨uD,au⟩⟩
  have bp : 1≤(portColor D b).card := card_pos.mpr ⟨v,mem_filter.mpr ⟨vD,bv⟩⟩
  have alow (a1 : (portColor D a).card=1) (q : V) (qa : q∈portColor D a) :
      ¬5≤G.degree q := by
    obtain ⟨qD,aq⟩ := mem_filter.mp qa
    exact lonely_port_low_if_other_at_most_two hc two even degree cd cover (.inl ⟨rfl,rfl⟩)
      xC ax bx only qD aq (fun bq=>none q qD ⟨aq,bq⟩) vD bv av a1 (by omega)
  have blow (b1 : (portColor D b).card=1) (q : V) (qb : q∈portColor D b) :
      ¬5≤G.degree q := by
    obtain ⟨qD,bq⟩ := mem_filter.mp qb
    exact lonely_port_low_if_other_at_most_two hc two even degree cd cover (.inr ⟨rfl,rfl⟩)
      xC bx ax (fun z zs bz az=>only z zs az bz)
      qD bq (fun aq=>none q qD ⟨aq,bq⟩) uD au bu b1 (by omega)
  by_cases a1 : (portColor D a).card=1
  · have b2 : (portColor D b).card=2 := by
      apply Classical.byContradiction
      intro nb
      have b1 : (portColor D b).card=1 := by omega
      exact (degree u v uv).elim (alow a1 _ (mem_filter.mpr ⟨uD,au⟩))
        (blow b1 _ (mem_filter.mpr ⟨vD,bv⟩))
    exact .inl ⟨a1,b2,alow a1⟩
  have a2 : (portColor D a).card=2 := by omega
  have b1 : (portColor D b).card=1 := by omega
  exact .inr ⟨a2,b1,blow b1⟩

theorem ranks_at_three_exclusive_foreign_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (only : ∀ q∈Shore C,G.Adj a q → G.Adj b q → q=x)
    (none : ∀ q∈Shore D,¬(G.Adj a q ∧ G.Adj b q))
    (p : (cutPorts D).card≤3) :
    ((portColor D a).card=1 ∧ (portColor D b).card=2 ∧
      4≤(portColor C a).card ∧ 3≤(portColor C b).card ∧
      (secondShore C b).card≤1 ∧
      ∀ u∈portColor D a, ¬5≤G.degree u) ∨
    ((portColor D a).card=2 ∧ (portColor D b).card=1 ∧
      3≤(portColor C a).card ∧ 4≤(portColor C b).card ∧
      (secondShore C a).card≤1 ∧
      ∀ u∈portColor D b, ¬5≤G.degree u) := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have two' : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have da := count_cut_degree_on_two_shores cd cover two (.inl rfl)
  have db := count_cut_degree_on_two_shores cd cover two (.inr rfl)
  obtain ⟨u,uD,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vD,bv⟩ := shore_hit_b ab conn D
  have bu : ¬G.Adj b u := fun h=>none u uD ⟨au,h⟩
  have av : ¬G.Adj a v := fun h=>none v vD ⟨h,bv⟩
  have uv : u≠v := fun e=>av (e ▸ au)
  have up : u∈portColor D a := mem_filter.mpr ⟨uD,au⟩
  have vp : v∈portColor D b := mem_filter.mpr ⟨vD,bv⟩
  rcases few_exclusive_ports_force_three_and_low hc two even conn degree cd cover
      xC ax bx only none p with ⟨one,dbl,low⟩|⟨dbl,one,low⟩
  · have uh := low _ up
    have ah := (degree u a (fun e=>(shore_off D).1 (e ▸ uD))).resolve_left uh
    have bh := (degree u b (fun e=>(shore_off D).2 (e ▸ uD))).resolve_left uh
    have vh := (degree u v uv).resolve_left uh
    have charge := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vD bv vh
    rw [if_neg av] at charge
    change 5≤(portColor D b).card+(secondShore D b).card at charge
    have cap := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ two' even
    exact .inl ⟨one,dbl,by omega,by omega,by omega,low⟩
  have vh := low _ vp
  have ah := (degree v a (fun e=>(shore_off D).1 (e ▸ vD))).resolve_left vh
  have bh := (degree v b (fun e=>(shore_off D).2 (e ▸ vD))).resolve_left vh
  have uh := (degree v u uv.symm).resolve_left vh
  have charge := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc uD au uh
  rw [if_neg bu] at charge
  change 5≤(portColor D a).card+(secondShore D a).card at charge
  have cap := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  exact .inr ⟨dbl,one,by omega,by omega,by omega,low⟩


private theorem foreign_exclusive_subset_at_port (hc : G.Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c u : V} (_cut : c=a ∨ c=b) (uD : u∈Shore D) (cu : G.Adj c u) :
    portColor C c⊆DistanceTwo G u := by
  intro z zp
  obtain ⟨zC,cz⟩ := mem_filter.mp zp
  have nu : u≠z := fun e=>disjoint_left.mp (shore_disjoint cd) zC (e ▸ uD)
  have no : ¬G.Adj u z := by
    intro e
    rcases shore_closed D u uD z e with rfl|rfl|zD
    · exact (shore_off C).1 zC
    · exact (shore_off C).2 zC
    exact disjoint_left.mp (shore_disjoint cd) zC zD
  exact d2 hc nu no cu.symm cz

private theorem complete_b_port_at_tight_shell (hc : G.Connected)
    {D : Cmp (G:=G) (a:=a) (b:=b)} {c d v : V}
    (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (vD : v∈Shore D) (dv : G.Adj d v) (cv : ¬G.Adj c v) (vh : 5≤G.degree v)
    (dbl : (portColor D d).card=2) (tri : (secondShore D d).card=3) :
    ∀ e∈secondShore D d,G.Adj v e := by
  classical
  let P := portColor D d
  let Q := secondShore D d
  have vp : v∈P := mem_filter.mpr ⟨vD,dv⟩
  have doff : d∉Shore D := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact (shore_off D).2
    exact (shore_off D).1
  let N := insert d (P.erase v∪Q)
  have sub : G.neighborFinset v⊆N := by
    intro z zn
    have e := (mem_neighborFinset G v z).mp zn
    have bd : z=c ∨ z=d ∨ z∈Shore D := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact shore_closed D v vD z e
      rcases shore_closed D v vD z e with h|h|h
      · exact .inr (.inl h)
      · exact .inl h
      exact .inr (.inr h)
    rcases bd with rfl|rfl|zD
    · exact (cv e.symm).elim
    · exact mem_insert_self _ _
    apply mem_insert_of_mem
    by_cases dz : G.Adj d z
    · exact mem_union_left _ (mem_erase.mpr ⟨e.ne.symm,mem_filter.mpr ⟨zD,dz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zD,d2 hc (fun e=>doff (e.symm ▸ zD)) dz dv e⟩)
  have u := card_insert_le d (P.erase v∪Q)
  change N.card≤_ at u
  have w := card_union_le (P.erase v) Q
  rw [card_erase_of_mem vp] at w
  change P.card=2 at dbl
  change Q.card=3 at tri
  have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; omega)
  intro z zq
  apply (mem_neighborFinset G v z).mp
  rw [eq]
  exact mem_insert_of_mem (mem_union_right _ zq)

private theorem universal_if_no_own_second
    (hc : G.Connected) {D : Cmp (G:=G) (a:=a) (b:=b)} {u : V}
    (uD : u∈Shore D) (zero : (secondShore D u).card=0) :
    ∀ z∈Shore D,z=u ∨ G.Adj u z := by
  classical
  intro z zD
  let W := ↑(↑(Shore D) : Set V)
  have step {v w : W} (p : (G.induce (↑(Shore D) : Set V)).Walk v w) :
      (v.val=u ∨ G.Adj u v.val) → (w.val=u ∨ G.Adj u w.val) := by
    induction p with
    | nil => exact id
    | @cons v w t e p ih =>
      intro hu
      apply ih
      by_cases wz : w.val=u
      · exact .inl wz
      by_cases uw : G.Adj u w.val
      · exact .inr uw
      change G.Adj v.val w.val at e
      rcases hu with rfl|hu
      · exact (uw e).elim
      have mem : w.val∈secondShore D u :=
        mem_inter.mpr ⟨w.property,d2 hc (Ne.symm wz) uw hu e⟩
      have bad := card_pos.mpr ⟨_,mem⟩
      omega
  obtain ⟨p⟩ := (shore_connected D).preconnected (⟨u,uD⟩ : W) ⟨z,zD⟩
  exact step p (.inl rfl)

private theorem no_three_oriented
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {x c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (xC : x∈Shore C) (dx : G.Adj d x)
    (only : ∀ z∈Shore C,G.Adj c z → G.Adj d z → z=x)
    (none : ∀ z∈Shore D,¬(G.Adj c z ∧ G.Adj d z))
    (c4 : 4≤(portColor C c).card)
    (d1 : (secondShore C d).card≤1)
    (one : (portColor D c).card=1) (dbl : (portColor D d).card=2)
    (low : ∀ z∈portColor D c,¬5≤G.degree z) : False := by
  classical
  let P := portColor C c
  let B := portColor D d
  let E := secondShore D d
  let U := portColor D c
  let O := Shore D
  have cOff : c∉Shore C ∧ c∉O := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact ⟨(shore_off C).1,(shore_off D).1⟩
    exact ⟨(shore_off C).2,(shore_off D).2⟩
  have dOff : d∉Shore C ∧ d∉O := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have swap : (d=a ∧ c=b) ∨ (d=b ∧ c=a) :=
    perm.elim (fun e=>.inr ⟨e.2,e.1⟩) (fun e=>.inl ⟨e.2,e.1⟩)
  have dist : G.dist d c=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rwa [SimpleGraph.dist_comm]
    exact two
  have small : (secondShore C d).card=1 := by
    apply Classical.byContradiction
    intro h
    have zero : (secondShore C d).card=0 := by omega
    have all := all_adj_of_no_second hc dOff.1 ⟨x,xC,dx⟩ zero
    have sub : P⊆{x} := by
      intro q qq
      obtain ⟨qC,cq⟩ := mem_filter.mp qq
      exact mem_singleton.mpr (only q qC cq (all _ qC))
    have l := card_le_card sub
    rw [card_singleton] at l
    change 4≤P.card at c4
    omega
  obtain ⟨u,ueq⟩ := card_eq_one.mp one
  have up : u∈U := by change u∈portColor D c; simp [ueq]
  obtain ⟨uD,cu⟩ := mem_filter.mp up
  have ulo := low _ up
  have ndu : ¬G.Adj d u := fun e=>none _ uD ⟨cu,e⟩
  have onlyC (z : V) (zl : z∈O) (cz : G.Adj c z) : z=u := by
    have g : z∈portColor D c := mem_filter.mpr ⟨zl,cz⟩
    simpa [ueq] using g
  have BB : 1<B.card := by change 1<(portColor D d).card; omega
  obtain ⟨v,vp,w,wp,vw⟩ := one_lt_card.mp BB
  obtain ⟨vD,dv⟩ := mem_filter.mp vp
  obtain ⟨wD,dw⟩ := mem_filter.mp wp
  have uv : u≠v := fun e=>ndu (e.symm ▸ dv)
  have uw : u≠w := fun e=>ndu (e.symm ▸ dw)
  have noh (z : V) (ne : u≠z) : 5≤G.degree z := (degree u z ne).resolve_left ulo
  have ncv : ¬G.Adj c v := fun e=>none _ vD ⟨e,dv⟩
  have ncw : ¬G.Adj c w := fun e=>none _ wD ⟨e,dw⟩
  have e3 : E.card=3 := by
    have t := charge_at_high_port swap hc vD dv (noh v uv)
    rw [if_neg ncv] at t
    change 5≤B.card+E.card at t
    have g := two_shore_budget cd cOff dist even
    change _+E.card≤4 at g
    change B.card=2 at dbl
    omega
  have fromV := complete_b_port_at_tight_shell hc perm vD dv ncv (noh v uv) dbl e3
  have fromW := complete_b_port_at_tight_shell hc perm wD dw ncw (noh w uw) dbl e3
  have PB : P⊆DistanceTwo G u := foreign_exclusive_subset_at_port hc cd
    (perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)) uD cu
  let Q := secondShore D u
  have qp : Disjoint Q P := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have union : Q∪P⊆DistanceTwo G u := union_subset inter_subset_right PB
  have qCap := card_le_card union
  rw [card_union_of_disjoint qp] at qCap
  have budget := distanceTwo_le_of_even 5 u (even u)
  change 4≤P.card at c4
  have q1 : Q.card≤1 := by omega
  have noB (t : V) (tp : t∈B) : ¬G.Adj u t := by
    intro ut
    obtain ⟨tD,dt⟩ := mem_filter.mp tp
    have du2 := d2 hc (show u≠d from fun e=>dOff.2 (e ▸ uD)) (fun e=>ndu e.symm) ut dt.symm
    have dnp : d∉Q∪P := by
      intro h
      exact (mem_union.mp h).elim (fun h=>dOff.2 (mem_inter.mp h).1)
        (fun h=>dOff.1 (mem_filter.mp h).1)
    have uAll : insert d (Q∪P)⊆DistanceTwo G u := by
      intro z h
      exact (mem_insert.mp h).elim (fun e=>e.symm ▸ du2) (fun e=>union e)
    have t1 := card_le_card uAll
    rw [card_insert_of_not_mem dnp,card_union_of_disjoint qp] at t1
    have universal := universal_if_no_own_second hc uD (by change Q.card=0; omega)
    have bne2 : Disjoint B E := by
      apply disjoint_left.mpr
      intro z zb ze
      have h1 := dist_eq_one_iff_adj.mpr (mem_filter.mp zb).2
      have h2 : G.dist d z=2 := by simpa [DistanceTwo] using (mem_inter.mp ze).2
      omega
    have sub : B∪E⊆O := union_subset (filter_subset _ _) inter_subset_left
    have os := card_le_card sub
    rw [card_union_of_disjoint bne2,e3] at os
    have Uc : G.neighborFinset u ⊇ insert c (O.erase u) := by
      intro z h
      rcases mem_insert.mp h with rfl|h
      · exact (mem_neighborFinset G u _).mpr cu.symm
      have ⟨ne,zO⟩ := mem_erase.mp h
      exact (mem_neighborFinset G u z).mpr ((universal z zO).resolve_left ne)
    have p := card_le_card Uc
    rw [card_insert_of_not_mem (fun h=>cOff.2 (mem_erase.mp h).2),
      card_erase_of_mem uD,card_neighborFinset_eq_degree] at p
    change O.card-1+1≤G.degree u at p
    change B.card=2 at dbl
    omega
  have noE (t : V) (tE : t∈E) : ¬G.Adj u t := by
    intro hit
    have vD2 := d2 hc uv (noB v vp) hit (fromV t tE).symm
    have wD2 := d2 hc uw (noB w wp) hit (fromW t tE).symm
    have mV : v∈Q := mem_inter.mpr ⟨vD,vD2⟩
    have mW : w∈Q := mem_inter.mpr ⟨wD,wD2⟩
    exact vw (card_le_one.mp q1 v mV w mW)
  have nbr : ∃ t∈O,G.Adj u t := by
    let Z := ↑(↑O : Set V)
    obtain ⟨p⟩ := (shore_connected D).preconnected (⟨u,uD⟩ : Z) ⟨v,vD⟩
    cases p with
    | nil => exact (uv rfl).elim
    | @cons _ t _ e q => exact ⟨t.val,t.property,e⟩
  obtain ⟨t,tO,ut⟩ := nbr
  have tc : ¬G.Adj c t := fun e=>ut.ne.symm (onlyC t tO e)
  have td : ¬G.Adj d t := fun e=>noB t (mem_filter.mpr ⟨tO,e⟩) ut
  let N := inside G O u
  have tN : t∈N := mem_filter.mpr ⟨tO,ut⟩
  have N3 : N.card≤3 := by
    have off : c∉N := fun e=>cOff.2 (mem_filter.mp e).1
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
    have bd : z=c ∨ z=d ∨ z∈O := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact shore_closed D t tO z tz
      rcases shore_closed D t tO z tz with h|h|h
      · exact .inr (.inl h)
      · exact .inl h
      exact .inr (.inr h)
    rcases bd with rfl|rfl|zD
    · exact (tc tz.symm).elim
    · exact (td tz.symm).elim
    by_cases ze : z=u
    · exact mem_insert.mpr (.inl ze)
    apply mem_insert_of_mem
    by_cases uz : G.Adj u z
    · exact mem_union_left _ (mem_erase.mpr ⟨tz.ne.symm,mem_filter.mpr ⟨zD,uz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zD,d2 hc (Ne.symm ze) uz ut tz⟩)
  have count := card_le_card sub
  rw [card_neighborFinset_eq_degree] at count
  have h := card_insert_le u (N.erase t∪Q)
  have j := card_union_le (N.erase t) Q
  rw [card_erase_of_mem tN] at j
  have t5 := noh t ut.ne
  have pos := card_pos.mpr ⟨t,tN⟩
  omega

theorem more_than_three_foreign_exclusive_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (only : ∀ q∈Shore C,G.Adj a q → G.Adj b q → q=x)
    (none : ∀ q∈Shore D,¬(G.Adj a q ∧ G.Adj b q)) :
    4≤(cutPorts D).card := by
  apply Classical.byContradiction
  intro bad
  have p : (cutPorts D).card≤3 := by omega
  rcases ranks_at_three_exclusive_foreign_ports hc two even conn degree cd cover
      xC ax bx only none p with ⟨one,dbl,c4,_,cap,low⟩|⟨dbl,one,_,c4,cap,low⟩
  · exact no_three_oriented hc two even degree cd (.inl ⟨rfl,rfl⟩)
      xC bx only none c4 cap one dbl low
  exact no_three_oriented hc two even degree cd (.inr ⟨rfl,rfl⟩)
    xC ax (fun z zs bz az=>only z zs az bz) (fun z zs h=>none z zs ⟨h.2,h.1⟩)
    c4 cap one dbl low

#print axioms few_exclusive_ports_force_three_and_low
#print axioms ranks_at_three_exclusive_foreign_ports
#print axioms more_than_three_foreign_exclusive_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
