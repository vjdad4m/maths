import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveBalanceBridgeCore189
import DegreeFiveMixedFourForeign189
import DegreeFiveBalancedCommonRoot189
import DegreeFiveBalancedSmallRoute189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_hit_b from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem opposite_port_has_four_inside
    {D : Cmp (G:=G) (a:=a) (b:=b)} {y : V}
    (yd : y∈Shore D) (ay : ¬ G.Adj a y) (hi : 5≤G.degree y) :
    4≤(inside G (Shore D) y).card := by
  classical
  let Y := inside G (Shore D) y
  have sub : G.neighborFinset y⊆insert b Y := by
    intro z zm
    have yz := (mem_neighborFinset G y z).mp zm
    rcases shore_closed D y yd z yz with rfl|rfl|zd
    · exact (ay yz.symm).elim
    · exact mem_insert_self _ _
    exact mem_insert_of_mem (mem_filter.mpr ⟨zd,yz⟩)
  have k := (card_le_card sub).trans (card_insert_le b Y)
  rw [card_neighborFinset_eq_degree] at k
  change 4≤Y.card
  omega

private theorem balanced_bridge_core_impossible
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {D : Cmp (G:=G) (a:=a) (b:=b)} {u : V} (ud : u∈Shore D) (au : G.Adj a u)
    (noCommon : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (noMixed : ∀ r∈Shore D,∀ s∈Shore D,G.Adj a r → G.Adj b s → ¬G.Adj r s)
    (twoA : (portColor D a).card=2) (hitB : ∃ y∈Shore D,G.Adj b y)
    (P : BalancedBridgeCore D u) : False := by
  classical
  let t := P.t
  let q := P.q
  let N := inside G (Shore D) u
  let H := insert u N
  let M := N.filter (fun z=>z≠t ∧ ¬G.Adj a z)
  have td : t∈Shore D := P.tD
  have qd : q∈Shore D := P.qD
  have ut : G.Adj u t := P.ut
  have tq : G.Adj t q := P.tq
  have ta : ¬G.Adj a t := P.ta
  have tb : ¬G.Adj b t := P.tb
  have qa : ¬G.Adj a q := P.qa
  have qb : ¬G.Adj b q := P.qb
  have tN : t∈N := mem_filter.mpr ⟨td,ut⟩
  have tH : t∈H := mem_insert_of_mem tN
  have uH : u∈H := mem_insert_self _ _
  have uOff : u∉N := fun h=>G.loopless u (mem_filter.mp h).2
  have N5 : N.card=5 := P.nFive
  have H6 : H.card=6 := by rw [show H=insert u N from rfl, card_insert_of_not_mem uOff,N5]
  have Hsub : H⊆Shore D := by
    intro z zh
    exact (mem_insert.mp zh).elim (fun e=>e.symm ▸ ud) (fun h=>(mem_filter.mp h).1)
  have q2u : G.dist u q=2 := by
    have h : q∈secondShore D u := by rw [P.qSet]; exact mem_singleton.mpr rfl
    simpa [DistanceTwo] using (mem_inter.mp h).2
  have qu : q≠u := by
    intro e
    rw [e,SimpleGraph.dist_self] at q2u
    omega
  have qN : q∉N := by
    intro e
    have one := dist_eq_one_iff_adj.mpr (mem_filter.mp e).2
    omega
  have qH : q∉H := by
    intro e
    exact (mem_insert.mp e).elim qu qN
  have threeM : 3≤M.card := by
    let A := portColor D a
    have up : u∈A := mem_filter.mpr ⟨ud,au⟩
    have sub : N⊆insert t (A.erase u∪M) := by
      intro z zn
      by_cases zt : z=t
      · exact mem_insert.mpr (.inl zt)
      apply mem_insert_of_mem
      obtain ⟨zd,uz⟩ := mem_filter.mp zn
      by_cases az : G.Adj a z
      · exact mem_union_left _ (mem_erase.mpr ⟨uz.ne.symm,mem_filter.mpr ⟨zd,az⟩⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨zn,zt,az⟩)
    have k := (card_le_card sub).trans (card_insert_le t _)
    have l := card_union_le (A.erase u) M
    rw [card_erase_of_mem up] at l
    change A.card=2 at twoA
    omega
  have universal (r : V) (rm : r∈M) (rh : 5≤G.degree r) (z : V) (zh : z∈H)
      (zr : z≠r) : G.Adj r z := by
    obtain ⟨rn,rt,ra⟩ := mem_filter.mp rm
    exact P.universal r rn rt ra rh z zh zr
  have Hnei {z : V} (zh : z∈H) (zt : z≠t) (tz : G.Adj t z) :
      z∈DistanceTwo G q :=
    d2 hc (fun e=>qH (e.symm ▸ zh)) (P.qOnly z zh zt) tq.symm tz
  obtain ⟨y,yd,by'⟩ := hitB
  have qy := P.qOther y yd by'
  have qnb : q≠b := by
    intro e
    exact (shore_off D).2 (Eq.mp (congrArg (fun z : V => z∈Shore D) e) qd)
  have qnoB : ¬G.Adj q b := fun e=>qb e.symm
  have b2 : b∈DistanceTwo G q := d2 hc qnb qnoB qy by'.symm
  let J := (H.erase t).filter (G.Adj t)
  have subJ : insert b J⊆DistanceTwo G q := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zn
    · exact b2
    obtain ⟨ze,tz⟩ := mem_filter.mp zn
    exact Hnei (mem_erase.mp ze).2 (mem_erase.mp ze).1 tz
  have bJ : b∉J := fun e=>(shore_off D).2 (Hsub (mem_erase.mp (mem_filter.mp e).1).2)
  have kJ := card_le_card subJ
  rw [card_insert_of_not_mem bJ] at kJ
  have qcap := distanceTwo_le_of_even 5 q (even q)
  have miss : ∃ z∈H.erase t,¬G.Adj t z := by
    apply Classical.byContradiction
    intro empty
    have sub : H.erase t⊆J := by
      intro z ze
      exact mem_filter.mpr ⟨ze,Classical.byContradiction (fun no=>empty ⟨z,ze,no⟩)⟩
    have k := card_le_card sub
    rw [card_erase_of_mem tH,H6] at k
    omega
  obtain ⟨m,me,tm⟩ := miss
  obtain ⟨mt,mH⟩ := mem_erase.mp me
  obtain ⟨r,rm,r5⟩ := anywhere_high_of_two degree (show 2≤M.card by omega)
  have rt := (mem_filter.mp rm).2.1
  have tr := (universal r rm r5 t tH rt.symm).symm
  have mr : m≠r := fun e=>tm (e.symm ▸ tr)
  have m2 : m∈DistanceTwo G t := d2 hc mt.symm tm tr (universal r rm r5 m mH mr)
  have tna : t≠a := by
    intro e
    exact (shore_off D).1 (Eq.mp (congrArg (fun z : V => z∈Shore D) e) td)
  have tnoA : ¬G.Adj t a := fun e=>ta e.symm
  have a2 : a∈DistanceTwo G t := d2 hc tna tnoA ut.symm au.symm
  let Z := (G.neighborFinset q).erase t
  have Zprop {z : V} (zz : z∈Z) : z∈Shore D ∧ z∉H ∧ G.Adj q z := by
    obtain ⟨zt,qn⟩ := mem_erase.mp zz
    have qz := (mem_neighborFinset G q z).mp qn
    have zD : z∈Shore D := by
      rcases shore_closed D q qd z qz with rfl|rfl|zD
      · exact (qa qz.symm).elim
      · exact (qb qz.symm).elim
      exact zD
    exact ⟨zD,fun h=>P.qOnly z h zt qz,qz⟩
  have subZ : Z⊆DistanceTwo G t := by
    intro z zz
    obtain ⟨zd,zh,qz⟩ := Zprop zz
    have tu : t≠z := fun e=>zh (e ▸ tH)
    have notz : ¬G.Adj t z := by
      intro tz
      have uz : ¬G.Adj u z := fun e=>zh (mem_insert_of_mem (mem_filter.mpr ⟨zd,e⟩))
      have nu : u≠z := fun e=>zh (e ▸ uH)
      have z2 := d2 hc nu uz ut tz
      have inQ : z∈secondShore D u := mem_inter.mpr ⟨zd,z2⟩
      have zq : z=q := by simpa [P.qSet] using inQ
      exact qz.ne zq.symm
    exact d2 hc tu notz tq qz
  have mz : m∉Z := fun e=>(Zprop e).2.1 mH
  have az : a∉insert m Z := by
    intro h
    rcases mem_insert.mp h with eq|h
    · exact (shore_off D).1 (eq.symm ▸ Hsub mH)
    exact (shore_off D).1 (Zprop h).1
  have capT : insert a (insert m Z)⊆DistanceTwo G t := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact a2
    exact (mem_insert.mp zm).elim (fun e=>e.symm ▸ m2) (fun h=>subZ h)
  have tc := card_le_card capT
  rw [card_insert_of_not_mem az,card_insert_of_not_mem mz] at tc
  have tcap := distanceTwo_le_of_even 5 t (even t)
  have zcard : Z.card=G.degree q-1 := by
    change ((G.neighborFinset q).erase t).card=_
    rw [card_erase_of_mem ((mem_neighborFinset G q t).mpr tq.symm),card_neighborFinset_eq_degree]
  have loq : ¬5≤G.degree q := by omega
  have hM (z : V) (zm : z∈M) : 5≤G.degree z :=
    (degree q z (fun e=>qH (e.symm ▸ mem_insert_of_mem (mem_filter.mp zm).1))).resolve_left loq
  have Qfull : insert b (insert u M)⊆DistanceTwo G q := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact b2
    rcases mem_insert.mp zm with rfl|zm
    · exact Hnei uH ut.ne ut.symm
    have ⟨zn,zt,_⟩ := mem_filter.mp zm
    exact Hnei (mem_insert_of_mem zn) zt (universal z zm (hM z zm) t tH zt.symm).symm
  have um : u∉M := fun h=>uOff (mem_filter.mp h).1
  have bm : b∉insert u M := by
    intro h
    rcases mem_insert.mp h with eq|h
    · exact (shore_off D).2 (eq.symm ▸ ud)
    exact (shore_off D).2 (mem_filter.mp (mem_filter.mp h).1).1
  have satur : insert b (insert u M)=DistanceTwo G q := by
    apply eq_of_subset_of_card_le Qfull
    rw [card_insert_of_not_mem bm,card_insert_of_not_mem um]
    omega
  have nyH (z : V) (zh : z∈H) : ¬G.Adj y z := by
    intro yz
    have uy : ¬G.Adj u y := noMixed u ud y yd au by'
    rcases mem_insert.mp zh with rfl|zn
    · exact uy yz.symm
    have une : u≠y := fun e=>noCommon u ud ⟨au,e.symm ▸ by'⟩
    have y2 := d2 hc une uy (mem_filter.mp zn).2 yz.symm
    have yy : y∈secondShore D u := mem_inter.mpr ⟨yd,y2⟩
    have h : y=q := by simpa [P.qSet] using yy
    exact qb (h ▸ by')
  let Y := inside G (Shore D) y
  have qY : q∈Y := mem_filter.mpr ⟨qd,qy.symm⟩
  have yhi := (degree q y (fun e=>qb (e.symm ▸ by'))).resolve_left loq
  have y4 : 4≤Y.card := opposite_port_has_four_inside yd (fun e=>noCommon y yd ⟨e,by'⟩) yhi
  have near : Y.erase q⊆G.neighborFinset q := by
    intro z zz
    obtain ⟨zq,zy⟩ := mem_erase.mp zz
    obtain ⟨zd,yz⟩ := mem_filter.mp zy
    apply (mem_neighborFinset G q z).mpr
    apply Classical.byContradiction
    intro qz
    have zd2 := d2 hc zq.symm qz qy yz
    rw [←satur] at zd2
    rcases mem_insert.mp zd2 with eq|zr
    · exact (shore_off D).2 (eq ▸ zd)
    have zh : z∈H := (mem_insert.mp zr).elim (fun e=>e.symm ▸ uH)
      (fun h=>mem_insert_of_mem (mem_filter.mp h).1)
    exact nyH z zh yz
  have yOff : y∉Y.erase q := fun e=>G.loopless y (mem_filter.mp (mem_erase.mp e).2).2
  have tOff : t∉Y.erase q := fun e=>nyH t tH (mem_filter.mp (mem_erase.mp e).2).2
  have ty : t≠y := fun e=>tb (e.symm ▸ by')
  have subq : insert t (insert y (Y.erase q))⊆G.neighborFinset q := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact (mem_neighborFinset G q _).mpr tq.symm
    rcases mem_insert.mp zm with rfl|zm
    · exact (mem_neighborFinset G q _).mpr qy
    exact near zm
  have qc := card_le_card subq
  rw [card_insert_of_not_mem (fun e=>(mem_insert.mp e).elim ty tOff),
    card_insert_of_not_mem yOff,card_erase_of_mem qY,card_neighborFinset_eq_degree] at qc
  omega

theorem exclusive_shore_le_seven_of_balanced_four_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (noCommon : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (fourA : (portColor C a).card=4) (fourB : (portColor C b).card=4)
    (twoA : (portColor D a).card=2) (twoB : 2≤(portColor D b).card) :
    (Shore D).card≤7 := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have hitB := shore_hit_b ab conn D
  by_cases mixed : ∃ u∈Shore D,∃ v∈Shore D,G.Adj a u ∧ G.Adj b v ∧ G.Adj u v
  · obtain ⟨u,ud,v,vd,au,bv,uv⟩ := mixed
    exact exclusive_shore_le_seven_of_mixed_with_four_foreign hc two even cd
      (.inl ⟨rfl,rfl⟩) ud au (fun e=>noCommon u ud ⟨au,e⟩) vd bv uv (by omega) fourA
  have noMixed (u : V) (ud : u∈Shore D) (v : V) (vd : v∈Shore D) (au : G.Adj a u)
      (bv : G.Adj b v) : ¬G.Adj u v := fun e=>mixed ⟨u,ud,v,vd,au,bv,e⟩
  obtain ⟨u,up,u5⟩ := anywhere_high_of_two degree (show 2≤(portColor D a).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  obtain ⟨P⟩ := bridge_core_of_balanced_four_four hc two even degree cd noCommon noMixed
    fourA fourB twoA twoB ud au u5
  exact (balanced_bridge_core_impossible hc even degree ud au noCommon noMixed twoA hitB P).elim

theorem traceable_of_balanced_four_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (noCommon : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (fourA : (portColor C a).card=4) (fourB : (portColor C b).card=4)
    (twoA : (portColor D a).card=2) (twoB : 2≤(portColor D b).card) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support :=
  traceable_of_balanced_exclusive_shore_at_most_seven hc two even conn degree cd cover
    shared noCommon (by omega) twoB
    (exclusive_shore_le_seven_of_balanced_four_four hc two even conn degree cd
      noCommon fourA fourB twoA twoB)

#print axioms exclusive_shore_le_seven_of_balanced_four_four
#print axioms traceable_of_balanced_four_four
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
