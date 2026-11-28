import DegreeFiveSevenSmallInner189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem far_dark_b_port_candidates (far : 3≤G.dist a b)
    {q : V} (qb : q∈S.L.filter (G.Adj b)) (dark : q∉visibleBPorts S.L a b G) :
    G.neighborFinset q⊆insert b (((S.L.filter (G.Adj b)).erase q)∪farNonports S.L a b G) := by
  have fd : 3≤G.dist b a := by rwa [dist_comm]
  have n := bounds_of_local_color_port S.flip fd (show q∈S.flip.localA from qb)
    (fun p pp h=>dark (mem_filter.mpr
      ⟨(mem_filter.mp qb).1,(mem_filter.mp qb).2,p,(mem_filter.mp pp).1,(mem_filter.mp pp).2,h.symm⟩))
  have e : farNonports S.flip.L b a G=farNonports S.L a b G := by
    ext x
    simp [farNonports,and_comm,and_left_comm,and_assoc,Split.flip]
  change G.neighborFinset q⊆insert b (((S.L.filter (G.Adj b)).erase q)∪farNonports S.flip.L b a G) at n
  rwa [e] at n

theorem bridge_two_locals_full (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (foreign : S.foreignA.card=3)
    (showI : farNonports S.L a b G⊆secondA G S.L a)
    {p q : V} (pa : p∈S.localA) (qb : q∈S.L.filter (G.Adj b))
    (b2 : b∈DistanceTwo G p) (q2 : q∈DistanceTwo G p) :
    (∀ u∈S.localA,p≠u → G.Adj p u) ∧ (∀ u∈farNonports S.L a b G,G.Adj p u) := by
  have ne : b≠q := fun e=>S.leftOff.2 (e.symm ▸ (mem_filter.mp qb).1)
  apply two_charges_force_full_on_a_and_nonports S hc far even foreign showI pa
    (W:={b,q}) (by simp [ne])
  · exact insert_subset_iff.mpr ⟨mem_insert_self _ _,singleton_subset_iff.mpr (mem_insert_of_mem qb)⟩
  exact insert_subset_iff.mpr ⟨b2,singleton_subset_iff.mpr q2⟩

theorem no_four_b_with_bridge_two_inner (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (b4 : (S.L.filter (G.Adj b)).card=4)
    (i2 : (farNonports S.L a b G).card=2)
    (w1 : (visibleBPorts S.L a b G).card=1) (foreign : S.foreignA.card=3)
    (showI : farNonports S.L a b G⊆secondA G S.L a) (bridge : portBridge S) : False := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let W := visibleBPorts S.L a b G
  let T := B\W
  let H := T.filter (fun t=>5≤G.degree t)
  change A.card=4 at a4
  change B.card=4 at b4
  change I.card=2 at i2
  change W.card=1 at w1
  have wb : W⊆B := fun _ e=>mem_filter.mpr ⟨(mem_filter.mp e).1,(mem_filter.mp e).2.1⟩
  have ht : H⊆T := filter_subset _ _
  have tb : T⊆B := sdiff_subset
  have bL : B⊆S.L := filter_subset _ _
  have iL : I⊆S.L := filter_subset _ _
  have sep : Disjoint A B := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  obtain ⟨p,pl,v,vl,ap,pv,bv⟩ := bridge
  have pa : p∈A := mem_filter.mpr ⟨pl,ap⟩
  have vv : v∈W := mem_filter.mpr ⟨vl,bv,p,pl,ap,pv⟩
  have vb := wb vv
  have wEq : W={v} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr vv)
    (by rw [card_singleton,w1])).symm
  have t3 : T.card=3 := by
    change (B\W).card=3
    rw [card_sdiff wb,b4,w1]
  have hi := count_high_subset_of_one_low degree T
  change T.card≤H.card+1 at hi
  have h2 : 2≤H.card := by omega
  have ne : p≠b := fun e=>S.leftOff.2 (e ▸ pl)
  have b2 := d2 hc ne (fun e=>not_common far ap e.symm) pv bv.symm
  have darkNo (q : V) (qt : q∈T) (p : V) (pa : p∈A) : ¬G.Adj p q := by
    obtain ⟨qb,qw⟩ := mem_sdiff.mp qt
    obtain ⟨qL,bq⟩ := mem_filter.mp qb
    obtain ⟨pL,ap⟩ := mem_filter.mp pa
    exact fun pq=>qw (mem_filter.mpr ⟨qL,bq,p,pL,ap,pq⟩)
  have bBound (q : V) (qt : q∈T) : G.neighborFinset q⊆insert b ((B.erase q)∪I) :=
    far_dark_b_port_candidates S far (mem_sdiff.mp qt).1 (mem_sdiff.mp qt).2
  have cap (q : V) (qa : q∈A) {X : Finset V}
      (loc : X⊆insert b S.L) (chg : X⊆DistanceTwo G q) : X.card≤2 :=
    local_distance_two_at_foreign_three S hc even foreign (mem_filter.mp qa).1
      (mem_filter.mp qa).2 loc chg
  have bOff : b∉H := fun m=>S.leftOff.2 (bL (tb (ht m)))
  have noSecond (q : V) (qt : q∈T) (q2 : q∈DistanceTwo G p) : False := by
    have full := (bridge_two_locals_full S hc far even foreign showI pa (tb qt) b2 q2).2
    have hNear : H⊆DistanceTwo G p := by
      intro r rh
      obtain ⟨rt,hr⟩ := mem_filter.mp rh
      have bound := far_port_nonport_degree_lower (tb rt) (bBound r rt)
      obtain ⟨x,xx⟩ := card_pos.mp (show 0<(I.filter (G.Adj r)).card by omega)
      obtain ⟨xi,rx⟩ := mem_filter.mp xx
      exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) (tb rt))
        (darkNo r rt p pa) (full x xi) rx.symm
    have d := cap p pa (insert_subset_iff.mpr ⟨mem_insert_self _ _,fun r rh=>
      mem_insert_of_mem (bL (tb (ht rh)))⟩) (insert_subset_iff.mpr ⟨b2,hNear⟩)
    rw [card_insert_of_not_mem bOff] at d
    omega
  have vNo (q : V) (qt : q∈T) : ¬G.Adj q v := by
    intro qv
    exact noSecond q qt (d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) (tb qt))
      (darkNo q qt p pa) pv qv.symm)
  have hFull (q : V) (qh : q∈H) : ∀ x∈I,G.Adj q x := by
    obtain ⟨qt,h⟩ := mem_filter.mp qh
    have neq : v≠q := fun e=>(mem_sdiff.mp qt).2 (e ▸ vv)
    have bound := far_port_nonport_degree_lower_of_missing_peer (tb qt) vb neq (vNo q qt) (bBound q qt)
    have eq : I.filter (G.Adj q)=I := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact fun x xi=>(mem_filter.mp (eq.symm ▸ xi)).2
  obtain ⟨q,qh⟩ := card_pos.mp (show 0<H.card by omega)
  have pI (x : V) (xi : x∈I) : ¬G.Adj p x := fun px=>noSecond q (ht qh)
    (d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) (tb (ht qh)))
      (darkNo q (ht qh) p pa) px (hFull q qh x xi).symm)
  by_cases p5 : 5≤G.degree p
  · have sub : G.neighborFinset p⊆insert a (insert v (A.erase p)) := by
      intro u un
      have pu := (mem_neighborFinset G p u).mp un
      rcases left_boundary S p pl u pu with e|e|ul
      · exact mem_insert.mpr (.inl e)
      · exact (not_common far ap (e ▸ pu.symm)).elim
      by_cases au : G.Adj a u
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨pu.ne.symm,mem_filter.mpr ⟨ul,au⟩⟩))
      by_cases bu : G.Adj b u
      · have uw : u∈W := mem_filter.mpr ⟨ul,bu,p,pl,ap,pu⟩
        exact mem_insert_of_mem (mem_insert.mpr (.inl (by simpa [wEq] using uw)))
      exact (pI u (mem_filter.mpr ⟨ul,au,bu⟩) pu).elim
    have n : (insert a (insert v (A.erase p))).card≤5 := by
      have m := card_insert_le a (insert v (A.erase p))
      have n := card_insert_le v (A.erase p)
      rw [card_erase_of_mem pa,a4] at n
      omega
    have eq : G.neighborFinset p=insert a (insert v (A.erase p)) :=
      eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; omega)
    have full (r : V) (ra : r∈A) (pr : p≠r) : G.Adj p r := by
      apply (mem_neighborFinset G p r).mp
      exact eq.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨pr.symm,ra⟩))
    have allI : I⊆DistanceTwo G p := by
      intro x xi
      obtain ⟨r,ra,rx⟩ := nonport_a_neighbor S hc far (iL xi) (mem_inter.mp (showI xi)).2
      have pr : p≠r := fun e=>pI x xi (e.symm ▸ rx)
      exact d2 hc (fun e=>(mem_filter.mp xi).2.1 (e ▸ ap)) (pI x xi) (full r ra pr) rx
    have bOut : b∉I := fun h=>S.leftOff.2 (iL h)
    have d := cap p pa (insert_subset_iff.mpr ⟨mem_insert_self _ _,fun r ri=>mem_insert_of_mem (iL ri)⟩)
      (insert_subset_iff.mpr ⟨b2,allI⟩)
    rw [card_insert_of_not_mem bOut,i2] at d
    omega
  have exactH : H=T := eq_of_subset_of_card_le ht (by
    have sub : T⊆H := by
      intro w wt
      have wp : w≠p := fun e=>disjoint_left.mp sep (e.symm ▸ pa) (tb wt)
      exact mem_filter.mpr ⟨wt,(degree w p wp).resolve_right p5⟩
    exact card_le_card sub)
  obtain ⟨i,ii⟩ := card_pos.mp (show 0<I.card by omega)
  obtain ⟨r,ra,ri⟩ := nonport_a_neighbor S hc far (iL ii) (mem_inter.mp (showI ii)).2
  have all : H⊆DistanceTwo G r := by
    intro w wh
    have wt := ht wh
    exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ ra) (tb wt))
      (darkNo w wt r ra) ri (hFull w wh i ii).symm
  have d := cap r ra (fun w wh=>mem_insert_of_mem (bL (tb (ht wh)))) all
  rw [exactH,t3] at d
  omega

#print axioms bridge_two_locals_full
#print axioms no_four_b_with_bridge_two_inner
end Graffiti189LongestPath.CrossSaturation.Split.Five
