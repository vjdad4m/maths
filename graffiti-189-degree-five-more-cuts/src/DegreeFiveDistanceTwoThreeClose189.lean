import DegreeFiveActualCut189
import DegreeFiveDistanceTwoComponents189
import DegreeFiveDistanceTwoSingletonClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_nonempty shore_disjoint shore_closed
  shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private abbrev CC := (CutGraph (G:=G) a b).ConnectedComponent

private noncomputable def secondShore (C : CC (G:=G) (a:=a) (b:=b)) (c : V) : Finset V :=
  Shore C ∩ DistanceTwo G c

private theorem anywhere_high_of_two
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {A : Finset V} (two : 2≤A.card) :
    ∃ x∈A,5≤G.degree x := by
  obtain ⟨x,xm,y,ym,xy⟩ := one_lt_card.mp (show 1<A.card by omega)
  rcases degree x y xy with h|h
  · exact ⟨x,xm,h⟩
  exact ⟨y,ym,h⟩

private theorem four_in_nonsingleton {C : CC (G:=G) (a:=a) (b:=b)}
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (many : 2≤(Shore C).card) : 4≤(Shore C).card := by
  classical
  obtain ⟨x,xm,hx⟩ := anywhere_high_of_two degree many
  have sub : G.neighborFinset x⊆insert a (insert b ((Shore C).erase x)) := by
    intro z zm
    have e := (mem_neighborFinset G x z).mp zm
    rcases shore_closed C x xm z e with rfl|rfl|zs
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,zs⟩))
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have l := card_insert_le a (insert b ((Shore C).erase x))
  have r := card_insert_le b ((Shore C).erase x)
  rw [card_erase_of_mem xm] at r
  omega

private theorem second_positive_of_small_ports
    {C : CC (G:=G) (a:=a) (b:=b)} {c : V}
    (off : c∉Shore C) (hit : ∃ x∈Shore C,G.Adj c x)
    (hc : G.Connected) (big : 4≤(Shore C).card)
    (ports : (cutPorts C).card≤3)
    (valid : c=a ∨ c=b) :
    1≤(secondShore C c).card := by
  classical
  obtain ⟨x,xm,cx⟩ := hit
  apply Classical.byContradiction
  intro small
  have universal (y : V) (ym : y∈Shore C) : G.Adj c y := by
    let W := ↑(↑(Shore C) : Set V)
    obtain ⟨p⟩ := (shore_connected C).preconnected (⟨x,xm⟩ : W) ⟨y,ym⟩
    have prop {u v : W} (q : (G.induce (↑(Shore C) : Set V)).Walk u v) :
        G.Adj c u.val → G.Adj c v.val := by
      induction q with
      | nil => exact id
      | @cons u w v uw q ih =>
        intro cu
        apply ih
        apply Classical.byContradiction
        intro no
        have w2 : w.val∈secondShore C c := mem_inter.mpr ⟨w.property,
          d2 hc (fun e=>off (e.symm ▸ w.property)) no cu uw⟩
        have pos := card_pos.mpr ⟨_,w2⟩
        omega
    exact prop p cx
  have sub : Shore C⊆cutPorts C := by
    intro z zm
    refine mem_filter.mpr ⟨zm,?_⟩
    rcases valid with rfl|rfl
    · exact .inl (universal z zm)
    exact .inr (universal z zm)
  have m := card_le_card sub
  omega

private theorem charge_at_high_port
    {C : CC (G:=G) (a:=a) (b:=b)} {c d u : V}
    (cd : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (hc : G.Connected)
    (uC : u∈Shore C) (cu : G.Adj c u) (high : 5≤G.degree u) :
    (if G.Adj d u then 4 else 5) ≤
      ((Shore C).filter (G.Adj c)).card + (secondShore C c).card := by
  classical
  let P := (Shore C).filter (G.Adj c)
  let Q := secondShore C c
  have up : u∈P := mem_filter.mpr ⟨uC,cu⟩
  have cp : c∉Shore C := by rcases cd with ⟨rfl,_⟩|⟨rfl,_⟩; exact (shore_off C).1; exact (shore_off C).2
  have incl : G.neighborFinset u ⊆ insert c (insert d (P.erase u∪Q)) := by
    intro v vn
    have uv := (mem_neighborFinset G u v).mp vn
    have q : v=c ∨ v=d ∨ v∈Shore C := by
      rcases cd with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact shore_closed C u uC v uv
      rcases shore_closed C u uC v uv with h|h|h
      · exact .inr (.inl h)
      · exact .inl h
      exact .inr (.inr h)
    rcases q with rfl|rfl|vC
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases cv : G.Adj c v
    · exact mem_union_left _ (mem_erase.mpr ⟨uv.ne.symm,mem_filter.mpr ⟨vC,cv⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨vC,d2 hc (fun e=>cp (e.symm ▸ vC)) cv cu uv⟩)
  have pos := card_pos.mpr ⟨_,up⟩
  have p := card_union_le (P.erase u) Q
  rw [card_erase_of_mem up] at p
  change _ ≤ P.card+Q.card
  split_ifs with h
  · have cap := card_le_card incl
    rw [card_neighborFinset_eq_degree] at cap
    have q := card_insert_le c (insert d (P.erase u∪Q))
    have r := card_insert_le d (P.erase u∪Q)
    omega
  have incl' : G.neighborFinset u ⊆ insert c (P.erase u∪Q) := by
    intro v vn
    have uv := (mem_neighborFinset G u v).mp vn
    rcases mem_insert.mp (incl vn) with rfl|vt
    · exact mem_insert_self _ _
    rcases mem_insert.mp vt with rfl|vv
    · exact (h uv.symm).elim
    exact mem_insert_of_mem vv
  have cap := (card_le_card incl').trans (card_insert_le c _)
  rw [card_neighborFinset_eq_degree] at cap
  omega

private theorem capacity_three_shores {C D E : CC (G:=G) (a:=a) (b:=b)}
    (cd : C≠D) (ce : C≠E) (de : D≠E)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) :
    (secondShore C c).card+(secondShore D c).card+(secondShore E c).card≤4 := by
  classical
  let I := secondShore C c
  let J := secondShore D c
  let K := secondShore E c
  have ij : Disjoint I J := (shore_disjoint cd).mono inter_subset_left inter_subset_left
  have ik : Disjoint I K := (shore_disjoint ce).mono inter_subset_left inter_subset_left
  have jk : Disjoint J K := (shore_disjoint de).mono inter_subset_left inter_subset_left
  have off (F : CC (G:=G) (a:=a) (b:=b)) : d∉secondShore F c := by
    intro h
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact (shore_off F).2 (mem_inter.mp h).1
    exact (shore_off F).1 (mem_inter.mp h).1
  have d2 : d∈DistanceTwo G c := by
    have e : G.dist c d=2 := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact two
      rwa [SimpleGraph.dist_comm]
    simp [DistanceTwo,e]
  have dn : d∉I∪J∪K := by
    simp only [mem_union]
    exact fun h=>h.elim (fun h=>h.elim (off C) (off D)) (off E)
  have sub : insert d (I∪J∪K)⊆DistanceTwo G c := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact d2
    rcases mem_union.mp zm with h|h
    · exact (mem_union.mp h).elim (fun p=>(mem_inter.mp p).2) (fun p=>(mem_inter.mp p).2)
    exact (mem_inter.mp h).2
  have k := card_le_card sub
  have ijk : Disjoint (I∪J) K := disjoint_union_left.mpr ⟨ik,jk⟩
  rw [card_insert_of_not_mem dn,card_union_of_disjoint ijk,card_union_of_disjoint ij] at k
  have cap := distanceTwo_le_of_even 5 c (even c)
  change I.card+J.card+K.card≤4
  omega

private theorem cost_of_two_port_common {C : CC (G:=G) (a:=a) (b:=b)}
    (hc : G.Connected) (ab : a≠b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (big : 4≤(Shore C).card) (twoP : (cutPorts C).card=2)
    (common : ∃ u∈Shore C,G.Adj a u ∧ G.Adj b u) :
    4≤(secondShore C a).card+(secondShore C b).card := by
  classical
  let P := cutPorts C
  have positiveA := second_positive_of_small_ports (shore_off C).1
    (shore_hit_a ab conn C) hc big (by omega) (.inl rfl)
  have positiveB := second_positive_of_small_ports (shore_off C).2
    (shore_hit_b ab conn C) hc big (by omega) (.inr rfl)
  by_cases high : ∃ u∈Shore C,G.Adj a u ∧ G.Adj b u ∧ 5≤G.degree u
  · obtain ⟨u,uC,au,bu,u5⟩ := high
    let I := secondShore C a ∩ secondShore C b
    have up : u∈P := mem_filter.mpr ⟨uC,.inl au⟩
    have sub : G.neighborFinset u⊆insert a (insert b (P.erase u∪I)) := by
      intro z zn
      have uz := (mem_neighborFinset G u z).mp zn
      rcases shore_closed C u uC z uz with rfl|rfl|zC
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)
      apply mem_insert_of_mem
      apply mem_insert_of_mem
      by_cases p : G.Adj a z ∨ G.Adj b z
      · exact mem_union_left _ (mem_erase.mpr ⟨uz.ne.symm,mem_filter.mpr ⟨zC,p⟩⟩)
      have neA : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zC)
      have neB : b≠z := fun e=>(shore_off C).2 (e.symm ▸ zC)
      have da := d2 hc neA (fun e=>p (.inl e)) au uz
      have db := d2 hc neB (fun e=>p (.inr e)) bu uz
      exact mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨zC,da⟩,mem_inter.mpr ⟨zC,db⟩⟩)
    have cap := card_le_card sub
    rw [card_neighborFinset_eq_degree] at cap
    have m := card_insert_le a (insert b (P.erase u∪I))
    have n := card_insert_le b (P.erase u∪I)
    have k := card_union_le (P.erase u) I
    rw [card_erase_of_mem up] at k
    change P.card=2 at twoP
    have la : I.card≤(secondShore C a).card := card_le_card inter_subset_left
    have lb : I.card≤(secondShore C b).card := card_le_card inter_subset_right
    omega
  obtain ⟨v,vp,v5⟩ := anywhere_high_of_two degree (show 2≤P.card by exact twoP.ge)
  obtain ⟨vC,hit⟩ := mem_filter.mp vp
  have cnt (c : V) (where' : c=a ∨ c=b) : ((Shore C).filter (G.Adj c)).card≤2 := by
    have sub : (Shore C).filter (G.Adj c)⊆P := by
      intro x hx
      obtain ⟨xC,cx⟩ := mem_filter.mp hx
      rcases where' with rfl|rfl
      · exact mem_filter.mpr ⟨xC,.inl cx⟩
      exact mem_filter.mpr ⟨xC,.inr cx⟩
    exact (card_le_card sub).trans twoP.le
  rcases hit with av|bv
  · have nb : ¬G.Adj b v := fun h=>high ⟨v,vC,av,h,v5⟩
    have paid := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc vC av v5
    rw [if_neg nb] at paid
    have h := cnt a (.inl rfl)
    omega
  have na : ¬G.Adj a v := fun h=>high ⟨v,vC,h,bv,v5⟩
  have paid := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vC bv v5
  rw [if_neg na] at paid
  have h := cnt b (.inr rfl)
  omega

private theorem two_port_must_common {C D E : CC (G:=G) (a:=a) (b:=b)}
    (cd : C≠D) (ce : C≠E) (de : D≠E)
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (twoP : (cutPorts C).card=2)
    (dBig : 4≤(Shore D).card) (dSmall : (cutPorts D).card≤3) :
    ∃ u∈Shore C,G.Adj a u ∧ G.Adj b u := by
  classical
  have ab : a≠b := by intro h; rw [h,SimpleGraph.dist_self] at two; omega
  apply Classical.byContradiction
  intro no
  obtain ⟨u,uC,au⟩ := shore_hit_a ab conn C
  obtain ⟨v,vC,bv⟩ := shore_hit_b ab conn C
  have na : ¬G.Adj a v := fun h=>no ⟨v,vC,h,bv⟩
  have nb : ¬G.Adj b u := fun h=>no ⟨u,uC,au,h⟩
  have uv : u≠v := fun e=>na (e ▸ au)
  have only : cutPorts C={u,v} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact mem_filter.mpr ⟨uC,.inl au⟩
      exact mem_filter.mpr ⟨vC,.inr bv⟩
    simp [twoP,uv]
  have capA : ((Shore C).filter (G.Adj a)).card≤1 := by
    have sub : (Shore C).filter (G.Adj a) ⊆ {u} := by
      intro z hz
      obtain ⟨zC,az⟩ := mem_filter.mp hz
      have zp : z∈cutPorts C := mem_filter.mpr ⟨zC,.inl az⟩
      rw [only] at zp
      simp only [mem_insert,mem_singleton] at zp
      rcases zp with rfl|rfl
      · simp
      exact (na az).elim
    have h := card_le_card sub
    simpa using h
  have capB : ((Shore C).filter (G.Adj b)).card≤1 := by
    have sub : (Shore C).filter (G.Adj b) ⊆ {v} := by
      intro z hz
      obtain ⟨zC,bz⟩ := mem_filter.mp hz
      have zp : z∈cutPorts C := mem_filter.mpr ⟨zC,.inr bz⟩
      rw [only] at zp
      simp only [mem_insert,mem_singleton] at zp
      rcases zp with rfl|rfl
      · exact (nb bz).elim
      simp
    have h := card_le_card sub
    simpa using h
  rcases degree u v uv with uh|vh
  · have m := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc uC au uh
    rw [if_neg nb] at m
    have cap := capacity_three_shores cd ce de two even (.inl ⟨rfl,rfl⟩)
    have pos := second_positive_of_small_ports (shore_off D).1
      (shore_hit_a ab conn D) hc dBig dSmall (.inl rfl)
    omega
  have m := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vC bv vh
  rw [if_neg na] at m
  have cap := capacity_three_shores cd ce de two even (.inr ⟨rfl,rfl⟩)
  have pos := second_positive_of_small_ports (shore_off D).2
    (shore_hit_b ab conn D) hc dBig dSmall (.inr rfl)
  omega

/-- Under degree-five #189, three shores at a distance-two cut force a
singleton. Any three nonsingleton shores would exhaust both cut shells. -/
theorem singleton_of_three_at_five_distance_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (three : 3≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ C : (CutGraph (G:=G) a b).ConnectedComponent,(Shore C).card=1 := by
  classical
  apply Classical.byContradiction
  intro none
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have ab : a≠b := by intro h; rw [h,SimpleGraph.dist_self] at two; omega
  have large (F : J.ConnectedComponent) : 1<(Shore F).card := by
    have h := card_pos.mpr (shore_nonempty F)
    have n : (Shore F).card≠1 := fun h=>none ⟨F,h⟩
    omega
  have big (F : J.ConnectedComponent) : 4≤(Shore F).card :=
    four_in_nonsingleton degree (large F)
  have ports (F : J.ConnectedComponent) : 2≤(cutPorts F).card :=
    two_ports_of_nonsingleton ab conn F (large F)
  have paircap {F D E : J.ConnectedComponent} {x : V} (xF : x∈Shore F)
      (ax : G.Adj a x) (bx : G.Adj b x) (fd : F≠D) (fe : F≠E) (de : D≠E) :
      (cutPorts D).card+(cutPorts E).card≤5 := by
    have cap := foreign_ports_le_five_at_common hc even xF ax bx
      (T:=({D,E} : Finset J.ConnectedComponent)) (by simp [fd,fe])
    rw [sum_insert (by simp [de]),sum_singleton] at cap
    exact cap
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C : J.ConnectedComponent := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : 1<T.card := by
    change 3≤Nat.card J.ConnectedComponent at three
    rw [Nat.card_eq_fintype_card] at three
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ]
    omega
  obtain ⟨D,dt,E,et,de⟩ := one_lt_card.mp tc
  have dc := (mem_erase.mp dt).1
  have ec := (mem_erase.mp et).1
  have finish {L N : J.ConnectedComponent} (lc : L≠C) (nc : N≠C) (ln : L≠N)
      (l2 : (cutPorts L).card=2) (nSmall : (cutPorts N).card≤3) : False := by
    obtain ⟨y,yL,ay,by'⟩ := two_port_must_common ln lc nc hc two even conn degree l2 (big N) nSmall
    have k := paircap yL ay by' lc ln nc.symm
    have cs : (cutPorts C).card≤3 := by have := ports N; omega
    have costL := cost_of_two_port_common hc ab conn degree (big L) l2 ⟨y,yL,ay,by'⟩
    have capA := capacity_three_shores lc ln nc.symm two even (.inl ⟨rfl,rfl⟩)
    have capB := capacity_three_shores lc ln nc.symm two even (.inr ⟨rfl,rfl⟩)
    by_cases hn : (cutPorts N).card=2
    · have com := two_port_must_common nc ln.symm lc.symm hc two even conn degree hn (big C) cs
      have costN := cost_of_two_port_common hc ab conn degree (big N) hn com
      have pos := second_positive_of_small_ports (shore_off C).1
        (shore_hit_a ab conn C) hc (big C) cs (.inl rfl)
      omega
    have c2 : (cutPorts C).card=2 := by have := ports N; have := ports C; omega
    have costC := cost_of_two_port_common hc ab conn degree (big C) c2 ⟨x,xC,ax,xb.symm⟩
    have pos := second_positive_of_small_ports (shore_off N).1
      (shore_hit_a ab conn N) hc (big N) nSmall (.inl rfl)
    omega
  have both := paircap xC ax xb.symm dc.symm ec.symm de
  have l := ports D
  have r := ports E
  by_cases hd : (cutPorts D).card=2
  · exact finish dc ec de hd (by omega)
  exact finish ec dc de.symm (by omega) (by omega)

/-- All degree-five cases with at least three shores at a distance-two cut. -/
theorem traceable_of_three_shores_at_five_distance_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (three : 3≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ x y : V,∃ q : G.Walk x y,q.IsPath ∧ ∀ z,z∈q.support :=
  traceable_of_three_shores_one_singleton hc two even conn degree three
    (singleton_of_three_at_five_distance_two hc two even conn degree three)

#print axioms singleton_of_three_at_five_distance_two
#print axioms traceable_of_three_shores_at_five_distance_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
