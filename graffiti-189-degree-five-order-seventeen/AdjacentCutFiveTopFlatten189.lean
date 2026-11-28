import AdjacentCutFiveAllCommonFour189
import AdjacentCutFiveComponents189
import AdjacentCutFiveProfilePorts189
import AdjacentCutFiveTopProfiles189
import AdjacentCutFiveTwoDoubleCover189
import AdjacentCutFiveTwoOrderTwenty189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore shore_closed shore_connected shore_off shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private positive_cap Vis vis_card_ge_two degree_le_shore from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private mem_positive from AdjacentCutFiveBound189
open private key classSet prof sa sb pa paysA paysB cnt compat selected_card key_facts
  profile_size terminal_charges foreign_charges from AdjacentCutFiveTopProfiles189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem cut_profile_budget (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card≤6) {C D : Cmp G a b} (cd : C≠D) :
    (prof C).cutOK (prof D) := by
  classical
  have one (f : Fin 6→Prop) [DecidablePred f] (v : V)
      (off : v∉Shore C ∧ v∉Shore D)
      (hit : ∀ w,f (key G a b w) → Even (G.dist v w)) :
      (∑ i : Fin 6, if f i then (classSet C i).card else 0)+
        (∑ i : Fin 6, if f i then (classSet D i).card else 0)≤5 := by
    let X := (Shore C).filter (fun w=>f (key G a b w))
    let Y := (Shore D).filter (fun w=>f (key G a b w))
    have h : X∪Y⊆PositiveEven G v := by
      intro w hw
      rcases mem_union.mp hw with wm|wm
      · obtain ⟨wc,wf⟩ := mem_filter.mp wm
        exact mem_positive.mpr ⟨fun e=>off.1 (e ▸ wc),hit w wf⟩
      · obtain ⟨wc,wf⟩ := mem_filter.mp wm
        exact mem_positive.mpr ⟨fun e=>off.2 (e ▸ wc),hit w wf⟩
    have dis : Disjoint X Y := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
    have c := (card_le_card h).trans (positive_cap v even)
    rw [card_union_of_disjoint dis] at c
    change ((Shore C).filter (fun w=>f (key G a b w))).card+
      ((Shore D).filter (fun w=>f (key G a b w))).card≤5 at c
    rwa [selected_card C f, selected_card D f] at c
  have h := one paysA a ⟨(shore_off C).1,(shore_off D).1⟩
    (fun _ => (terminal_charges hc ab).1.mp)
  have k := one paysB b ⟨(shore_off C).2,(shore_off D).2⟩
    (fun _ => (terminal_charges hc ab).2.mp)
  refine ⟨?_,?_⟩
  · simpa [Fin.sum_univ_succ,Fin.sum_univ_zero,paysA,prof,add_assoc] using h
  · simpa [Fin.sum_univ_succ,Fin.sum_univ_zero,paysB,prof,add_assoc] using k

private theorem cross_profile_budget (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card≤6) {C D : Cmp G a b} (cd : C≠D) :
    (prof C).crossOK (prof D) := by
  classical
  have r (i : Fin 6) (hit : (classSet C i).Nonempty) :
      (∑ j : Fin 6, if compat i j then (classSet D j).card else 0)+cnt i≤5 := by
    obtain ⟨x,hx⟩ := hit
    obtain ⟨xc,kx⟩ := mem_filter.mp hx
    let P := (Shore D).filter (fun z=>compat i (key G a b z))
    let K := ({a,b} : Finset V).filter (fun z=>Even (G.dist x z))
    have sub : P∪K ⊆ PositiveEven G x := by
      intro z hz
      rcases mem_union.mp hz with zp|zk
      · obtain ⟨zd,cp⟩ := mem_filter.mp zp
        have zx : z≠x := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e ▸ zd)
        exact mem_positive.mpr ⟨zx,(foreign_charges hc ab cd xc zd).mp (by rwa [kx])⟩
      · obtain ⟨mem,ev⟩ := mem_filter.mp zk
        obtain az|bz : z=a ∨ z=b := by simpa using mem
        · exact mem_positive.mpr ⟨fun e=>(shore_off C).1 ((e.symm.trans az) ▸ xc),ev⟩
        · exact mem_positive.mpr ⟨fun e=>(shore_off C).2 ((e.symm.trans bz) ▸ xc),ev⟩
    have dis : Disjoint P K := by
      apply disjoint_left.mpr
      intro z zp zk
      have zD := (mem_filter.mp zp).1
      obtain az|bz : z=a ∨ z=b := by simpa using (mem_filter.mp zk).1
      · exact (shore_off D).1 (az ▸ zD)
      · exact (shore_off D).2 (bz ▸ zD)
    have CK := terminal_charges hc ab (w:=x)
    rw [kx] at CK
    have kCard : K.card=cnt i := by
      have qa : Even (G.dist x a) ↔ paysA i := by rw [dist_comm]; exact CK.1.symm
      have qb : Even (G.dist x b) ↔ paysB i := by rw [dist_comm]; exact CK.2.symm
      by_cases ha : paysA i <;> by_cases hb : paysB i
      · have aa := qa.mpr ha
        have bb := qb.mpr hb
        simp [K,cnt,Finset.filter_insert,Finset.filter_singleton,aa,bb,ha,hb,ab.ne]
      · have aa := qa.mpr ha
        have bb : ¬Even (G.dist x b) := fun e=>hb (qb.mp e)
        simp [K,cnt,Finset.filter_insert,Finset.filter_singleton,aa,bb,ha,hb]
      · have aa : ¬Even (G.dist x a) := fun e=>ha (qa.mp e)
        have bb := qb.mpr hb
        simp [K,cnt,Finset.filter_insert,Finset.filter_singleton,aa,bb,ha,hb]
      · have aa : ¬Even (G.dist x a) := fun e=>ha (qa.mp e)
        have bb : ¬Even (G.dist x b) := fun e=>hb (qb.mp e)
        simp [K,cnt,Finset.filter_insert,Finset.filter_singleton,aa,bb,ha,hb]
    have c := (card_le_card sub).trans (positive_cap x even)
    rw [card_union_of_disjoint dis,kCard] at c
    change ((Shore D).filter (fun z=>compat i (key G a b z))).card+cnt i≤5 at c
    rwa [selected_card] at c
  unfold AdjProfile.crossOK
  refine ⟨fun h=>?_,fun h=>?_,fun h=>?_,fun h=>?_,fun h=>?_,fun h=>?_⟩
  all_goals
    first
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 0 (card_pos.mp h)
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 1 (card_pos.mp h)
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 2 (card_pos.mp h)
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 3 (card_pos.mp h)
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 4 (card_pos.mp h)
    | simpa [prof,Fin.sum_univ_succ,Fin.sum_univ_zero,compat,pa,sa,sb,cnt,paysA,paysB,add_assoc] using r 5 (card_pos.mp h)

end Graffiti189LongestPath.CrossSaturation.FiveAdjacent

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore shore_closed shore_connected shore_off shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Vis vis_card_ge_two degree_le_shore degree_le_shore_add_one from AdjacentCutFiveComponents189
open private d2 from AdjacentCutFiveBound189
open private key classSet prof sa sb pa key_facts profile_size selected_card from AdjacentCutFiveTopProfiles189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem key_a_port (hc : G.Connected) (ab : G.Adj a b)
    {v : V} (vb : v≠b) (ea : G.Adj a v) :
    key G a b v=3 ∨ key G a b v=5 := by
  classical
  have ha := dist_eq_one_iff_adj.mpr ea
  by_cases eb : G.Adj b v
  · have hb := dist_eq_one_iff_adj.mpr eb
    exact .inr (by simp [key,ha,hb,Nat.even_iff])
  · have hb := (mem_filter.mp (d2 hc vb.symm eb ab.symm ea)).2
    exact .inl (by simp [key,ha,hb,Nat.even_iff])

private theorem key_b_port (hc : G.Connected) (ab : G.Adj a b)
    {v : V} (va : v≠a) (eb : G.Adj b v) :
    key G a b v=4 ∨ key G a b v=5 := by
  classical
  have hb := dist_eq_one_iff_adj.mpr eb
  by_cases ea : G.Adj a v
  · have ha := dist_eq_one_iff_adj.mpr ea
    exact .inr (by simp [key,ha,hb,Nat.even_iff])
  · have ha := (mem_filter.mp (d2 hc va.symm ea ab eb)).2
    exact .inl (by simp [key,ha,hb,Nat.even_iff])

private theorem small_noncommon_card_le_one
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp G a b} (four : (Shore C).card=4) :
    ((Shore C).filter (fun v=>¬(G.Adj a v ∧ G.Adj b v))).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u um v vm
  by_contra ne
  have low {w : V} (wm : w∈((Shore C).filter (fun v=>¬(G.Adj a v ∧ G.Adj b v)))) :
      G.degree w≤4 := by
    obtain ⟨wc,nc⟩ := mem_filter.mp wm
    have t : ¬G.Adj a w ∨ ¬G.Adj b w := by
      by_cases au : G.Adj a w
      · exact .inr (fun bu=>nc ⟨au,bu⟩)
      · exact .inl au
    simpa [four] using degree_le_shore C wc t
  have each := degree u v ne
  rcases each with d|d
  · have one := low um; omega
  · have one := low vm; omega

private theorem local_profile_conditions (hc : G.Connected) (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp G a b} (four : 4≤(Shore C).card) :
    (prof C).localOK := by
  classical
  have p4 : 4≤(prof C).size := by rwa [profile_size]
  refine ⟨p4,?_,?_,?_,?_,?_,?_⟩
  · let f : Fin 6→Prop := fun i=>i=3 ∨ i=4 ∨ i=5
    have sub : Vis C⊆(Shore C).filter (fun v=>f (key G a b v)) := by
      intro v vv
      obtain ⟨vc,pv⟩ := mem_filter.mp vv
      have va : v≠a := fun e=>(shore_off C).1 (e ▸ vc)
      have vb : v≠b := fun e=>(shore_off C).2 (e ▸ vc)
      refine mem_filter.mpr ⟨vc,?_⟩
      rcases pv with av|bv
      · exact (key_a_port hc ab vb av).imp id Or.inr
      · exact .inr (key_b_port hc ab va bv)
    have h := (vis_card_ge_two ab.ne conn C (by omega)).trans (card_le_card sub)
    rw [selected_card C f] at h
    simpa [f,Fin.sum_univ_succ,Fin.sum_univ_zero,prof,add_assoc] using h
  · obtain ⟨v,vc,av⟩ := shore_hit_a ab.ne conn C
    have vb : v≠b := fun e=>(shore_off C).2 (e ▸ vc)
    rcases key_a_port hc ab vb av with k|k
    · have q := card_pos.mpr (show (classSet C 3).Nonempty from ⟨v,mem_filter.mpr ⟨vc,k⟩⟩)
      change 1≤(classSet C 3).card+(classSet C 5).card
      omega
    · have q := card_pos.mpr (show (classSet C 5).Nonempty from ⟨v,mem_filter.mpr ⟨vc,k⟩⟩)
      change 1≤(classSet C 3).card+(classSet C 5).card
      omega
  · obtain ⟨v,vc,bv⟩ := shore_hit_b ab.ne conn C
    have va : v≠a := fun e=>(shore_off C).1 (e ▸ vc)
    rcases key_b_port hc ab va bv with k|k
    · have q := card_pos.mpr (show (classSet C 4).Nonempty from ⟨v,mem_filter.mpr ⟨vc,k⟩⟩)
      change 1≤(classSet C 4).card+(classSet C 5).card
      omega
    · have q := card_pos.mpr (show (classSet C 5).Nonempty from ⟨v,mem_filter.mpr ⟨vc,k⟩⟩)
      change 1≤(classSet C 4).card+(classSet C 5).card
      omega
  · intro h
    obtain ⟨v,m⟩ := (card_pos.mp h : (classSet C 0).Nonempty)
    obtain ⟨vc,kv⟩ := mem_filter.mp m
    obtain ⟨da,db,dd⟩ := key_facts hc ab v
    rw [kv] at da db
    have near : G.dist a v<G.dist b v := by
      change G.dist a v=depth G a b v+0 at da
      change G.dist b v=depth G a b v+1 at db
      omega
    obtain ⟨w,wc,aw,nb⟩ := exclusive_left_port_of_strictly_nearer hc vc near
    have wb : w≠b := fun e=>(shore_off C).2 (e ▸ wc)
    have k := (key_a_port hc ab wb aw).resolve_right (fun e=>by
      have h := (key_facts hc ab w).2.1
      rw [e] at h
      change G.dist b w=depth G a b w+0 at h
      have ha := (key_facts hc ab w).1
      rw [e] at ha
      change G.dist a w=depth G a b w+0 at ha
      exact nb (dist_eq_one_iff_adj.mp (h.trans (ha.symm.trans (dist_eq_one_iff_adj.mpr aw)))))
    exact card_pos.mpr (show (classSet C 3).Nonempty from ⟨w,mem_filter.mpr ⟨wc,k⟩⟩)
  · intro h
    obtain ⟨v,m⟩ := (card_pos.mp h : (classSet C 1).Nonempty)
    obtain ⟨vc,kv⟩ := mem_filter.mp m
    obtain ⟨da,db,dd⟩ := key_facts hc ab v
    rw [kv] at da db
    have near : G.dist b v<G.dist a v := by
      change G.dist a v=depth G a b v+1 at da
      change G.dist b v=depth G a b v+0 at db
      omega
    obtain ⟨w,wc,bw,na⟩ := exclusive_right_port_of_strictly_nearer hc vc near
    have wa : w≠a := fun e=>(shore_off C).1 (e ▸ wc)
    have k := (key_b_port hc ab wa bw).resolve_right (fun e=>by
      have h := (key_facts hc ab w).1
      rw [e] at h
      change G.dist a w=depth G a b w+0 at h
      have ha := (key_facts hc ab w).2.1
      rw [e] at ha
      change G.dist b w=depth G a b w+0 at ha
      exact na (dist_eq_one_iff_adj.mp (h.trans (ha.symm.trans (dist_eq_one_iff_adj.mpr bw)))))
    exact card_pos.mpr (show (classSet C 4).Nonempty from ⟨w,mem_filter.mpr ⟨wc,k⟩⟩)
  · intro hs
    rw [profile_size] at hs
    have n1 := small_noncommon_card_le_one degree hs
    let N := (Shore C).filter (fun v=>¬(G.Adj a v ∧ G.Adj b v))
    change N.card≤1 at n1
    have sub : Shore C⊆N∪classSet C 5 := by
      intro v vc
      by_cases c : G.Adj a v ∧ G.Adj b v
      · have k : key G a b v=5 := by
          simp [key,dist_eq_one_iff_adj.mpr c.1,dist_eq_one_iff_adj.mpr c.2]
        exact mem_union_right _ (mem_filter.mpr ⟨vc,k⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨vc,c⟩)
    have h := (card_le_card sub).trans (card_union_le N (classSet C 5))
    change 3≤(classSet C 5).card
    omega

end Graffiti189LongestPath.CrossSaturation.FiveAdjacent

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_connected shore_off shore_disjoint shore_nonempty shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private degree_le_shore_add_one from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private d2 from AdjacentCutFiveBound189
open private key classSet prof sa sb pa key_facts profile_size from AdjacentCutFiveTopProfiles189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem all_common_of_four_equal_odd (hc : G.Connected) (ab : G.Adj a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp G a b} (four : (Shore C).card=4) (c4 : (classSet C 5).card=4) :
    ∀ z∈Shore C,G.Adj a z ∧ G.Adj b z := by
  classical
  have eq : classSet C 5=Shore C := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have nc := small_noncommon_card_le_one degree four
  intro z zc
  by_contra no
  have out : ((Shore C).erase z).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem zc,four]
    decide
  obtain ⟨w,wm⟩ := out
  obtain ⟨wz,wc⟩ := mem_erase.mp wm
  let U : Set V := ↑(Shore C)
  let H := G.induce U
  have near : ∃ u∈Shore C,G.Adj z u := by
    obtain ⟨p⟩ := (shore_connected C).preconnected ⟨z,zc⟩ ⟨w,wc⟩
    have ne : (⟨z,zc⟩ : U) ≠ ⟨w,wc⟩ := fun e=>wz (congrArg Subtype.val e).symm
    cases p with
    | nil => exact (ne rfl).elim
    | @cons _ x _ e q => exact ⟨x.val,x.property,e⟩
  obtain ⟨u,uc,zu⟩ := near
  have Cx : G.Adj a u ∧ G.Adj b u := by
    by_contra nuc
    exact zu.ne (Finset.card_le_one.mp nc z (mem_filter.mpr ⟨zc,no⟩)
      u (mem_filter.mpr ⟨uc,nuc⟩))
  have kz := (mem_filter.mp (show z∈classSet C 5 by rwa [eq])).2
  obtain ⟨da,db,o⟩ := key_facts hc ab z
  rw [kz] at da db o
  change G.dist a z=depth G a b z+0 at da
  change G.dist b z=depth G a b z+0 at db
  change (depth G a b z)%2=1 at o
  have az : ¬G.Adj a z := by
    intro e
    exact no ⟨e,dist_eq_one_iff_adj.mp (db.trans (da.symm.trans (dist_eq_one_iff_adj.mpr e)))⟩
  have za : z≠a := fun e=>(shore_off C).1 (e ▸ zc)
  have second := (mem_filter.mp (d2 hc za.symm az Cx.1 zu.symm)).2
  omega

private theorem order_counts_of_two_shores (ab : a≠b)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) :
    (Shore C).card+(Shore D).card+2=Fintype.card V := by
  classical
  have eq : (univ.erase a |>.erase b : Finset V)=Shore C∪Shore D := by
    ext z
    constructor
    · intro h
      exact mem_union.mpr (cover (mem_erase.mp (mem_erase.mp h).2).1 (mem_erase.mp h).1)
    · intro h
      have p : z≠a ∧ z≠b := by
        rcases mem_union.mp h with zc|zd
        · exact ⟨fun e=>(shore_off C).1 (e ▸ zc),fun e=>(shore_off C).2 (e ▸ zc)⟩
        · exact ⟨fun e=>(shore_off D).1 (e ▸ zd),fun e=>(shore_off D).2 (e ▸ zd)⟩
      exact mem_erase.mpr ⟨p.2,mem_erase.mpr ⟨p.1,mem_univ _⟩⟩
  have z := congrArg Finset.card eq
  rw [card_erase_of_mem (by simp [ab.symm]),card_erase_of_mem (mem_univ _),
    card_univ,card_union_of_disjoint (shore_disjoint cd)] at z
  have ge2 : 2≤Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨a,b,ab⟩⟩
  omega

theorem order_le_seventeen_of_actual_adjacent_two_nonsingleton_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2)
    (nonsingleton : ∀ C : Cmp G a b,2≤(Shore C).card) :
    Fintype.card V≤17 := by
  classical
  by_contra large
  have lo : 18≤Fintype.card V := Nat.lt_of_not_ge large
  have hi := order_le_nineteen_of_actual_adjacent_two_shores hc ab even conn two
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have size4 (E : Cmp G a b) : 4≤(Shore E).card := by
    by_contra tooSmall
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (nonsingleton E)
    have du := degree_le_shore_add_one E ue
    have dv := degree_le_shore_add_one E ve
    rcases degree u v uv with h|h <;> omega
  have orient {K L : Cmp G a b} (kl : K≠L)
      (cov : ∀ {z : V},z≠a→z≠b→z∈Shore K ∨ z∈Shore L)
      (small : (Shore K).card≤(Shore L).card) : False := by
    have ck := order_counts_of_two_shores ab.ne kl cov
    have key := AdjProfile.compact_top_pair (prof K) (prof L)
      (by simpa only [profile_size] using small)
      (by simp only [profile_size]; omega)
      (by simp only [profile_size]; omega)
      (local_profile_conditions hc ab conn degree (size4 K))
      (local_profile_conditions hc ab conn degree (size4 L))
      (cut_profile_budget hc ab even kl)
      (cross_profile_budget hc ab even kl)
      (cross_profile_budget hc ab even kl.symm)
    have k4 : (Shore K).card=4 := by simpa only [profile_size] using key.1
    have ko4 : (classSet K 5).card=4 := key.2
    have bnd := order_le_sixteen_of_adjacent_four_common_shore hc ab even kl cov k4
      (all_common_of_four_equal_odd hc ab degree k4 ko4)
    omega
  by_cases ht : (Shore C).card≤(Shore D).card
  · exact orient cd cover ht
  · exact orient cd.symm (fun za zb=>(cover za zb).symm) (by omega)

#print axioms order_le_seventeen_of_actual_adjacent_two_nonsingleton_shores

private theorem order_le_sixteen_of_adjacent_singleton_shore
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) :
    Fintype.card V≤16 := by
  classical
  by_contra tooLarge
  have huge : 17≤Fintype.card V := Nat.lt_of_not_ge tooLarge
  have order := order_counts_of_two_shores ab.ne cd cover
  obtain ⟨x,eq⟩ := card_eq_one.mp one
  obtain ⟨u,uc,au⟩ := shore_hit_a ab.ne conn C
  obtain ⟨v,vc,bv⟩ := shore_hit_b ab.ne conn C
  have ueq : u=x := by simpa [eq] using uc
  have veq : v=x := by simpa [eq] using vc
  have ax : G.Adj a x := ueq ▸ au
  have bx : G.Adj b x := veq ▸ bv
  have k : key G a b x=5 := by
    simp [key,dist_eq_one_iff_adj.mpr ax,dist_eq_one_iff_adj.mpr bx]
  have source : prof C=⟨0,0,0,0,0,1⟩ := by simp [prof,classSet,eq,k,Finset.filter_singleton]
  have lc := local_profile_conditions hc ab conn degree (show 4≤(Shore D).card by omega)
  have cc := cut_profile_budget hc ab even cd
  have cr := cross_profile_budget hc ab even cd
  have size := profile_size D
  rw [source] at cc cr
  simp only [AdjProfile.localOK] at lc
  simp only [AdjProfile.cutOK] at cc
  simp only [AdjProfile.crossOK] at cr
  unfold AdjProfile.size at size
  have w := cr.2.2.2.2.2 (by decide)
  omega

theorem order_le_seventeen_of_actual_adjacent_two_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2) :
    Fintype.card V≤17 := by
  classical
  by_cases h : ∀ C : Cmp G a b,2≤(Shore C).card
  · exact order_le_seventeen_of_actual_adjacent_two_nonsingleton_shores hc ab even conn degree two h
  push_neg at h
  obtain ⟨C,hc'⟩ := h
  have one : (Shore C).card=1 := by have c := card_pos.mpr (shore_nonempty C); omega
  obtain ⟨K,L,kl,cover⟩ := actual_two_shores two
  have k : C=K ∨ C=L := by
    obtain ⟨z,zc⟩ := shore_nonempty C
    have za : z≠a := fun e=>(shore_off C).1 (e ▸ zc)
    have zb : z≠b := fun e=>(shore_off C).2 (e ▸ zc)
    rcases cover za zb with zk|zl
    · exact .inl (Classical.byContradiction (fun h=>disjoint_left.mp (shore_disjoint h) zc zk))
    · exact .inr (Classical.byContradiction (fun h=>disjoint_left.mp (shore_disjoint h) zc zl))
  rcases k with rfl|rfl
  · exact (order_le_sixteen_of_adjacent_singleton_shore hc ab even conn degree kl cover one).trans (by decide)
  · exact (order_le_sixteen_of_adjacent_singleton_shore hc ab even conn degree kl.symm
      (fun za zb=>(cover za zb).symm) one).trans (by decide)

#print axioms order_le_seventeen_of_actual_adjacent_two_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
