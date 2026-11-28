import SixJointNearDegrees189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem active_nonempty (hc : G.Connected)
    {x d : V} (Q : RadiusFiveNearEquality G x) (d4 : d∈Shell G x 4) :
    ∃ a∈Q.T,Q.Active d a := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x d
  have len := hp.trans (mem_shell.mp d4)
  let b := p.getVert 2
  let c := p.getVert 3
  have b2 : b∈Shell G x 2 := mem_shell.mpr (distance_on_geodesic hc p hp 2 (by omega))
  have c3 : c∈Shell G x 3 := mem_shell.mpr (distance_on_geodesic hc p hp 3 (by omega))
  have bc : G.Adj b c := p.adj_getVert_succ (i:=2) (by omega)
  have cd : G.Adj c d := by
    have h := p.adj_getVert_succ (i:=3) (by omega)
    have e : p.getVert 4=d := by rw [←len,getVert_length]
    simpa only [e] using h
  obtain ⟨a,aT,ar⟩ := Q.rep_cover b b2
  exact ⟨a,aT,c,c3,ar.symm ▸ bc,cd⟩

theorem selector_ne_rep (_hc : G.Connected) {x a : V}
    (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T) : a≠Q.rep a := by
  exact (Q.adj a aT).ne

theorem low_contradiction_of_single_active
    (hc : G.Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x d a b c : V} (dx : G.degree x≤6) (Q : RadiusFiveNearEquality G x)
    (d4 : d∈Shell G x 4) (labels : Q.T={a,b,c})
    (aT : a∈Q.T) (bT : b∈Q.T) (cT : c∈Q.T) (ab : a≠b)
    (live : Q.Active d a) (deadB : ¬Q.Active d b) (deadC : ¬Q.Active d c)
    (fullB : (JointFarGroup G x b).card=4) (fullC : (JointFarGroup G x c).card=4) :
    False := by
  have ⟨nab,nrb⟩ := Q.no_edges_between_active_and_full_inactive hc aT bT d4 live deadB fullB
  have ⟨nac,nrc⟩ := Q.no_edges_between_active_and_full_inactive hc aT cT d4 live deadC fullC
  have allowed (z : V) (zt : z∈Q.T) : z=a ∨ z=b ∨ z=c := by
    simpa [labels] using zt
  have aLow := Q.selected_degree_le_five_plus_allowed hc dx aT ∅ (by
    intro z zt az
    rcases allowed z zt with rfl|rfl|rfl
    · exact False.elim (az.ne rfl)
    · exact False.elim (nab az)
    · exact False.elim (nac az))
  have bLow := Q.rep_degree_le_one_plus_group_plus_allowed hc aT ∅
    (Q.rep_no_extra_of_nonadj_to_full hc aT bT ab fullB (fun e=>nab e.symm)) (by
      intro z zt az
      rcases allowed z zt with rfl|rfl|rfl
      · exact False.elim (az.ne rfl)
      · exact False.elim (nrb az)
      · exact False.elim (nrc az))
  have bound := (card_le_card (show Shell G x 3∩JointFarGroup G x a⊆JointFarGroup G x a from
    inter_subset_right)).trans (Q.far_card a aT)
  rw [card_empty] at aLow bLow
  rcases high a (Q.rep a) (Q.selector_ne_rep hc aT) with h|h <;> omega

theorem low_contradiction_of_single_inactive
    (hc : G.Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x d a b c : V} (dx : G.degree x≤6) (Q : RadiusFiveNearEquality G x)
    (d4 : d∈Shell G x 4) (labels : Q.T={a,b,c})
    (aT : a∈Q.T) (bT : b∈Q.T) (cT : c∈Q.T) (ac : a≠c)
    (liveA : Q.Active d a) (liveB : Q.Active d b) (deadC : ¬Q.Active d c)
    (fullA : (JointFarGroup G x a).card=4) (fullC : (JointFarGroup G x c).card=4) :
    False := by
  have ⟨nac,nrc⟩ := Q.no_edges_between_active_and_full_inactive hc aT cT d4 liveA deadC fullC
  have ⟨nbc,nsc⟩ := Q.no_edges_between_active_and_full_inactive hc bT cT d4 liveB deadC fullC
  have allowed (z : V) (zt : z∈Q.T) : z=a ∨ z=b ∨ z=c := by
    simpa [labels] using zt
  have aLow := Q.selected_degree_le_five_plus_allowed hc dx cT ∅ (by
    intro z zt az
    rcases allowed z zt with rfl|rfl|rfl
    · exact False.elim (nac az.symm)
    · exact False.elim (nbc az.symm)
    · exact False.elim (az.ne rfl))
  have bLow := Q.rep_degree_le_one_plus_group_plus_allowed hc cT ∅
    (Q.rep_no_extra_of_nonadj_to_full hc cT aT ac.symm fullA nac) (by
      intro z zt az
      rcases allowed z zt with rfl|rfl|rfl
      · exact False.elim (nrc az.symm)
      · exact False.elim (nsc az.symm)
      · exact False.elim (az.ne rfl))
  have bound := (card_le_card (show Shell G x 3∩JointFarGroup G x c⊆JointFarGroup G x c from
    inter_subset_right)).trans (Q.far_card c cT)
  rw [card_empty] at aLow bLow
  rcases high c (Q.rep c) (Q.selector_ne_rep hc cT) with h|h <;> omega

theorem no_fifth_support_when_full
    (hc : G.Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x d e : V} (dx : G.degree x≤6) (Q : RadiusFiveNearEquality G x)
    (d4 : d∈Shell G x 4) (e5 : e∈Shell G x 5) (de : G.Adj d e)
    (lo : 11≤(Shell G x 3∪Shell G x 5).card)
    (full : ∀ a∈Q.T,(JointFarGroup G x a).card=4) : False := by
  classical
  obtain ⟨a,aT,aLive⟩ := Q.active_nonempty hc d4
  have two : (Q.T.erase a).card=2 := by rw [card_erase_of_mem aT,Q.t3]
  obtain ⟨b,bm⟩ := card_pos.mp (show 0<(Q.T.erase a).card by omega)
  obtain ⟨ba,bT⟩ := mem_erase.mp bm
  obtain ⟨c,cT,ca,cb,labels⟩ := label_three_of_mem Q.t3 aT bT ba.symm
  have all : ¬(Q.Active d b ∧ Q.Active d c) := by
    intro h
    exact near_cover_not_common_to_three Q.T (JointFarGroup G x)
      (Shell G x 3∪Shell G x 5) Q.t3 Q.far_cover lo Q.far_card (mem_union_right _ e5)
      aT bT cT ba.symm ca.symm cb.symm (Q.fifth_mem_of_active hc aT de e5 aLive)
      (Q.fifth_mem_of_active hc bT de e5 h.1) (Q.fifth_mem_of_active hc cT de e5 h.2)
  by_cases hb : Q.Active d b
  · exact Q.low_contradiction_of_single_inactive hc high dx d4 labels aT bT cT ca.symm
      aLive hb (fun hc=>all ⟨hb,hc⟩) (full a aT) (full c cT)
  by_cases hh : Q.Active d c
  · have el : Q.T={a,c,b} := by rw [labels]; ext v; simp only [mem_insert,mem_singleton]; tauto
    exact Q.low_contradiction_of_single_inactive hc high dx d4 el aT cT bT ba.symm
      aLive hh hb (full a aT) (full b bT)
  exact Q.low_contradiction_of_single_active hc high dx d4 labels aT bT cT ba.symm
    aLive hb hh (full b bT) (full c cT)

theorem fourth_dist_to_deficient_if_fifth_support
    (hc : G.Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x d e k : V} (dx : G.degree x≤6) (Q : RadiusFiveNearEquality G x)
    (d4 : d∈Shell G x 4) (e5 : e∈Shell G x 5) (de : G.Adj d e)
    (lo : 11≤(Shell G x 3∪Shell G x 5).card)
    (kT : k∈Q.T) (small : (JointFarGroup G x k).card<4) : G.dist k d=4 := by
  classical
  obtain ⟨_ks,full,sep⟩ := near_cover_deficient_members Q.T (JointFarGroup G x)
    (Shell G x 3∪Shell G x 5) Q.t3 Q.far_cover lo Q.far_card kT small
  obtain ⟨a,aT,aLive⟩ := Q.active_nonempty hc d4
  have eA := Q.fifth_mem_of_active hc aT de e5 aLive
  have only {b : V} (bT : b∈Q.T) (ba : b≠a) : ¬Q.Active d b := by
    intro h
    exact disjoint_left.mp (sep a aT b bT ba.symm) eA (Q.fifth_mem_of_active hc bT de e5 h)
  have ak : a≠k := by
    intro e
    subst a
    have two : (Q.T.erase k).card=2 := by rw [card_erase_of_mem kT,Q.t3]
    obtain ⟨b,bm⟩ := card_pos.mp (show 0<(Q.T.erase k).card by omega)
    obtain ⟨bk,bT⟩ := mem_erase.mp bm
    obtain ⟨c,cT,ck,cb,labels⟩ := label_three_of_mem Q.t3 kT bT bk.symm
    exact Q.low_contradiction_of_single_active hc high dx d4 labels kT bT cT bk.symm
      aLive (only bT bk) (only cT ck) (full b bT bk) (full c cT ck)
  obtain ⟨b,bT,ba,bk,labels⟩ := label_three_of_mem Q.t3 aT kT ak
  have fullB := full b bT bk
  have ⟨ab,arb⟩ := Q.no_edges_between_active_and_full_inactive hc aT bT d4 aLive (only bT ba) fullB
  have allowed (z : V) (zt : z∈Q.T) : z=a ∨ z=k ∨ z=b := by simpa [labels] using zt
  have repLow := Q.rep_degree_le_one_plus_group_plus_allowed hc aT {Q.rep k}
    (Q.rep_no_extra_of_nonadj_to_full hc aT bT ba.symm fullB (fun e=>ab e.symm)) (by
      intro z zt adj
      rcases allowed z zt with rfl|rfl|rfl
      · exact False.elim (adj.ne rfl)
      · exact mem_singleton.mpr rfl
      · exact False.elim (arb adj))
  have cap3 := Q.third_group_le_three_of_fifth aT e5 eA
  rw [card_singleton] at repLow
  have aHigh := (high a (Q.rep a) (Q.selector_ne_rep hc aT)).resolve_right (by omega)
  have adjAK : G.Adj a k := by
    by_contra no
    have aLow := Q.selected_degree_le_five_plus_allowed hc dx aT ∅ (by
      intro z zt adj
      rcases allowed z zt with rfl|rfl|rfl
      · exact False.elim (adj.ne rfl)
      · exact False.elim (no adj)
      · exact False.elim (ab adj))
    rw [card_empty] at aLow
    omega
  have r := Q.dist_le_three_of_active hc aT aLive
  have h := hc.dist_triangle (u:=k) (v:=a) (w:=d)
  have one := dist_eq_one_iff_adj.mpr adjAK.symm
  have dd := mem_shell.mp d4
  have k1 := mem_shell.mp (Q.near kT)
  have lower := hc.dist_triangle (u:=x) (v:=k) (w:=d)
  have nd : G.dist k d≠3 := fun e=>only kT ak.symm (Q.active_of_dist_three hc kT d4 e)
  omega

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.no_fifth_support_when_full
#print axioms RadiusFiveNearEquality.fourth_dist_to_deficient_if_fifth_support
end Graffiti189LongestPath
