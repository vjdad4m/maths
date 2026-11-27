import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveFourGateway189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private two_walk_middle from DistanceTwoCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Geometry supplied by the high member of the two-contact color. -/
structure BalancedBridgeCore
    (D : Cmp (G:=G) (a:=a) (b:=b)) (u : V) where
  t : V
  q : V
  tD : t∈Shore D
  qD : q∈Shore D
  ut : G.Adj u t
  tq : G.Adj t q
  ta : ¬G.Adj a t
  tb : ¬G.Adj b t
  qa : ¬G.Adj a q
  qb : ¬G.Adj b q
  nFive : (inside G (Shore D) u).card=5
  qSet : secondShore D u={q}
  qOnly : ∀ z∈insert u (inside G (Shore D) u), z≠t → ¬ G.Adj q z
  qOther : ∀ z∈Shore D,G.Adj b z → G.Adj q z
  universal :
    ∀ z∈inside G (Shore D) u,z≠t → ¬G.Adj a z → 5≤G.degree z →
      ∀ w∈insert u (inside G (Shore D) u),w≠z → G.Adj z w

private theorem inside_bound_exclusive
    {D : Cmp (G:=G) (a:=a) (b:=b)} {u : V} (uD : u∈Shore D) (no : ¬G.Adj b u)
    (high : 5≤G.degree u) : 4≤(inside G (Shore D) u).card := by
  classical
  let N := inside G (Shore D) u
  have s : G.neighborFinset u⊆insert a N := by
    intro z zn
    have h := (mem_neighborFinset G u z).mp zn
    rcases shore_closed D u uD z h with rfl|rfl|zD
    · exact mem_insert_self _ _
    · exact (no h.symm).elim
    exact mem_insert_of_mem (mem_filter.mpr ⟨zD,h⟩)
  have k := (card_le_card s).trans (card_insert_le a N)
  rw [card_neighborFinset_eq_degree] at k
  change 4≤N.card
  omega

theorem bridge_core_of_balanced_four_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (noCommon : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (noMixed : ∀ r∈Shore D,∀ s∈Shore D,G.Adj a r → G.Adj b s → ¬G.Adj r s)
    (fourA : (portColor C a).card=4) (fourB : (portColor C b).card=4)
    (twoA : (portColor D a).card=2) (twoB : 2≤(portColor D b).card)
    {u : V} (uD : u∈Shore D) (au : G.Adj a u) (u5 : 5≤G.degree u) :
    Nonempty (BalancedBridgeCore D u) := by
  classical
  let N := inside G (Shore D) u
  let H := insert u N
  let A := portColor D a
  let B := portColor D b
  have bu : ¬G.Adj b u := fun h=>noCommon u uD ⟨au,h⟩
  change 2≤B.card at twoB
  obtain ⟨v,vB,w,wB,vw⟩ := one_lt_card.mp (show 1<B.card by omega)
  obtain ⟨vD,bv⟩ := mem_filter.mp vB
  obtain ⟨wD,bw⟩ := mem_filter.mp wB
  have uGate :
      ∃ q∈Shore D,secondShore D u={q} ∧
        (∀ z∈Shore D,z≠u → ¬G.Adj u z → z≠q → G.Adj q z) :=
    exclusive_four_local_gateway hc two even cd (.inl ⟨rfl,rfl⟩) au uD bu
      (fun z zd bz=>noMixed u uD z zd au bz) ⟨v,vD,bv⟩ fourA
  obtain ⟨q,qD,qSet,far⟩ := uGate
  have qdist := (mem_inter.mp (show q∈secondShore D u by simp [qSet])).2
  have uqNo : ¬G.Adj u q := by
    intro h
    have two : G.dist u q=2 := by simpa [DistanceTwo] using qdist
    have one := dist_eq_one_iff_adj.mpr h
    omega
  have qa : ¬G.Adj a q := by
    intro aq
    have vq : v≠q := fun e=>noCommon q qD ⟨aq,e ▸ bv⟩
    have vu : v≠u := fun e=>bu (e ▸ bv)
    exact noMixed q qD v vD aq bv (far v vD vu (noMixed u uD v vD au bv) vq)
  have farB (y : V) (yD : y∈Shore D) (by' : G.Adj b y) (yq : y≠q) :
      G.Adj q y := far y yD (fun e=>bu (e ▸ by')) (noMixed u uD y yD au by') yq
  have sel : ∃ y∈Shore D,G.Adj b y ∧ y≠q := by
    by_cases eq : v=q
    · exact ⟨w,wD,bw,fun h=>vw (eq.trans h.symm)⟩
    exact ⟨v,vD,bv,eq⟩
  obtain ⟨y,yD,by',yq⟩ := sel
  have qy := farB y yD by' yq
  have gB (y : V) (yD : y∈Shore D) (by' : G.Adj b y) :
      ∃ s∈Shore D,secondShore D y={s} := by
    have ya : ¬G.Adj a y := fun h=>noCommon y yD ⟨h,by'⟩
    obtain ⟨s,sD,se,_⟩ := exclusive_four_local_gateway hc two even cd
      (.inr ⟨rfl,rfl⟩) by' yD ya (fun z zD az zy=>noMixed z zD y yD az by' zy.symm)
      ⟨u,uD,au⟩ fourB
    exact ⟨s,sD,se⟩
  obtain ⟨s,sD,sEq⟩ := gB y yD by'
  have d2q : G.dist u q=2 := by simpa [DistanceTwo] using qdist
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist u q
  obtain ⟨t,ut,tq⟩ := two_walk_middle p (pl.trans d2q)
  have tD : t∈Shore D := by
    rcases shore_closed D u uD t ut with rfl|rfl|tD
    · exact (qa tq).elim
    · exact (bu ut.symm).elim
    exact tD
  have tN : t∈N := mem_filter.mpr ⟨tD,ut⟩
  have onlyBridge (r : V) (rn : r∈N) (rq : G.Adj r q) : r=t := by
    have mem (z : V) (zn : z∈N) (zq : G.Adj z q) : z∈secondShore D y := by
      obtain ⟨zD,uz⟩ := mem_filter.mp zn
      have ny : ¬G.Adj u y := noMixed u uD y yD au by'
      have ne : y≠z := fun e=>ny (e.symm ▸ uz)
      have no : ¬G.Adj y z := by
        intro h
        have uy : u≠y := fun e=>bu (e.symm ▸ by')
        have h' := d2 hc uy ny uz h.symm
        have m : y∈secondShore D u := mem_inter.mpr ⟨yD,h'⟩
        exact yq (by simpa [qSet] using m)
      exact mem_inter.mpr ⟨zD,d2 hc ne no qy.symm zq.symm⟩
    have rs : r=s := by simpa [sEq] using mem r rn rq
    have ts : t=s := by simpa [sEq] using mem t tN tq
    exact rs.trans ts.symm
  have tb : ¬G.Adj b t := fun h=>noMixed u uD t tD au h ut
  have ta : ¬G.Adj a t := by
    intro ati
    by_cases qb : G.Adj b q
    · exact noMixed t tD q qD ati qb tq
    obtain ⟨k,kD,kSet,_⟩ := exclusive_four_local_gateway hc two even cd
      (.inl ⟨rfl,rfl⟩) ati tD tb (fun z zd bz=>noMixed t tD z zd ati bz) ⟨v,vD,bv⟩ fourA
    have vK (z : V) (zD : z∈Shore D) (bz : G.Adj b z) : z∈secondShore D t := by
      have zq : z≠q := fun e=>qb (e ▸ bz)
      have qz := farB z zD bz zq
      exact mem_inter.mpr ⟨zD,d2 hc (fun e=>tb (e.symm ▸ bz))
        (noMixed t tD z zD ati bz) tq qz⟩
    have v1 : v=k := by simpa [kSet] using vK v vD bv
    have w1 : w=k := by simpa [kSet] using vK w wD bw
    exact vw (v1.trans w1.symm)
  have qOnly (r : V) (rH : r∈H) (rt : r≠t) : ¬G.Adj q r := by
    intro qr
    rcases mem_insert.mp rH with rfl|rn
    · exact uqNo qr.symm
    exact rt (onlyBridge r rn qr.symm)
  have cutBound := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have capN : N.card≤5 := by
    have up : u∈A := mem_filter.mpr ⟨uD,au⟩
    have sub : N⊆A.erase u∪secondShore D a := by
      intro z zn
      obtain ⟨zD,uz⟩ := mem_filter.mp zn
      by_cases az : G.Adj a z
      · exact mem_union_left _ (mem_erase.mpr ⟨uz.ne.symm,mem_filter.mpr ⟨zD,az⟩⟩)
      exact mem_union_right _ (mem_inter.mpr ⟨zD,d2 hc
        (fun e=>(shore_off D).1 (e.symm ▸ zD)) az au uz⟩)
    have m := (card_le_card sub).trans (card_union_le _ _)
    rw [card_erase_of_mem up] at m
    change A.card=2 at twoA
    omega
  have minN : 4≤N.card := inside_bound_exclusive uD bu u5
  have uOff : u∉N := fun h=>G.loopless u (mem_filter.mp h).2
  have hCard : H.card=N.card+1 := card_insert_of_not_mem uOff
  have contained (r : V) (rn : r∈N) (rt : r≠t) (ra : ¬G.Adj a r) :
      G.neighborFinset r⊆H.erase r := by
    intro z zm
    obtain ⟨rD,ur⟩ := mem_filter.mp rn
    have rz := (mem_neighborFinset G r z).mp zm
    have rb : ¬G.Adj b r := fun e=>noMixed u uD r rD au e ur
    rcases shore_closed D r rD z rz with rfl|rfl|zD
    · exact (ra rz.symm).elim
    · exact (rb rz.symm).elim
    refine mem_erase.mpr ⟨rz.ne.symm,?_⟩
    apply Classical.byContradiction
    intro no
    have neq : u≠z := fun e=>no (mem_insert.mpr (.inl e.symm))
    have noadj : ¬G.Adj u z := fun e=>no (mem_insert_of_mem (mem_filter.mpr ⟨zD,e⟩))
    have z2 : z∈secondShore D u := mem_inter.mpr ⟨zD,d2 hc neq noadj ur rz⟩
    have eq : z=q := by simpa [qSet] using z2
    exact rt (onlyBridge r rn (eq ▸ rz))
  let M := N.filter (fun r=>r≠t ∧ ¬G.Adj a r)
  have mCard : 2≤M.card := by
    have up : u∈A := mem_filter.mpr ⟨uD,au⟩
    have sub : N⊆insert t ((A.erase u)∪M) := by
      intro z zn
      by_cases zt : z=t
      · exact mem_insert.mpr (.inl zt)
      apply mem_insert_of_mem
      obtain ⟨zD,uz⟩ := mem_filter.mp zn
      by_cases az : G.Adj a z
      · exact mem_union_left _ (mem_erase.mpr ⟨uz.ne.symm,mem_filter.mpr ⟨zD,az⟩⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨zn,zt,az⟩)
    have k := (card_le_card sub).trans (card_insert_le t _)
    have l := card_union_le (A.erase u) M
    rw [card_erase_of_mem up] at l
    change A.card=2 at twoA
    omega
  obtain ⟨r,rM,r5⟩ := anywhere_high_of_two degree mCard
  obtain ⟨rN,rt,ra⟩ := mem_filter.mp rM
  have rH : r∈H := mem_insert_of_mem rN
  have rCost := card_le_card (contained r rN rt ra)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem rH] at rCost
  have nFive : N.card=5 := by omega
  have universal (z : V) (zN : z∈N) (zt : z≠t) (za : ¬G.Adj a z)
      (z5 : 5≤G.degree z) (w : V) (wH : w∈H) (wz : w≠z) : G.Adj z w := by
    have zH : z∈H := mem_insert_of_mem zN
    have hu : (H.erase z).card=5 := by rw [card_erase_of_mem zH,hCard,nFive]
    have eq := eq_of_subset_of_card_le (contained z zN zt za) (by
      rw [hu,card_neighborFinset_eq_degree]
      exact z5)
    exact (mem_neighborFinset G z w).mp (eq.symm ▸ mem_erase.mpr ⟨wz,wH⟩)
  have qb : ¬G.Adj b q := by
    intro qb
    obtain ⟨k,kD,kEq⟩ := gB q qD qb
    have qr : ¬G.Adj q r := qOnly r rH rt
    have qu : ¬G.Adj q u := fun e=>uqNo e.symm
    have tr : G.Adj t r := (universal r rN rt ra r5 t (mem_insert_of_mem tN) rt.symm).symm
    have qru : r∈secondShore D q := mem_inter.mpr ⟨(mem_filter.mp rN).1,
      d2 hc (fun e=>uqNo (e.symm ▸ (mem_filter.mp rN).2)) qr tq.symm tr⟩
    have qne : q≠u := by
      intro e
      rw [e,SimpleGraph.dist_self] at d2q
      omega
    have quu : u∈secondShore D q := mem_inter.mpr ⟨uD,d2 hc qne qu tq.symm ut.symm⟩
    have r1 : r=k := by simpa [kEq] using qru
    have u1 : u=k := by simpa [kEq] using quu
    exact uOff (r1.trans u1.symm ▸ rN)
  exact ⟨⟨t,q,tD,qD,ut,tq,ta,tb,qa,qb,nFive,qSet,qOnly,
    fun z zd bz=>farB z zd bz (fun e=>qb (e ▸ bz)),universal⟩⟩

#print axioms bridge_core_of_balanced_four_four
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
