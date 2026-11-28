import SixThree20FourteenPairMiss189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.Rigidity.reverse_longest from Rigidity189
open private Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem pair_contradiction_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14)
    (pos : 0<p.length) (sz : (Omit p).card=5) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2) : False := by
  classical
  let U := PortSet p (Omit p)
  by_cases bad : ∃ v∈CandHigh p,1≤(Misses G U v).card
  · obtain ⟨v,vm,bad⟩ := bad
    obtain ⟨ve,dv⟩ := mem_filter.mp vm
    obtain ⟨u,q,hq,same,ql,ue⟩ := cand_rotated_path hp ve
    have du : 6≤G.degree u := ue.elim (fun e=>e.symm ▸ da) (fun e=>e.symm ▸ db)
    have hqr := Graffiti189LongestPath.Rigidity.reverse_longest hq
    have oldnew : ∀ v,v∈p.support ↔ v∈q.reverse.support := by
      intro v
      simpa using same v
    have Oeq := same_support_omit oldnew
    have Ueq : U=PortSet q.reverse (Omit q.reverse) := by
      change PortSet p (Omit p)=PortSet q.reverse (Omit q.reverse)
      rw [←Oeq]
      exact same_support_port_set hp hqr oldnew (fun v vm=>mem_Omit.mp vm)
    rw [Ueq] at bad
    exact pair_contradiction_if_right_misses_fourteen hc conn cap degree hqr (by simpa [ql] using len)
      (by simpa [ql] using pos) (Oeq ▸ sz) du dv (pair_profile_same_support hp hqr oldnew pair) bad
  have Hn : (HighOmit p).Nonempty := card_pos.mp (by
    have h := high_filter_card degree (Omit p)
    change (Omit p).card≤(HighOmit p).card+1 at h
    omega)
  obtain ⟨x,xm⟩ := Hn
  have pairx := pair x xm
  have xo := (highOmit_data xm).1
  have c : (PinVertices p x).card=2 := (Graffiti189LongestPath.OneSlack.card_pinVertices hp).trans pairx
  have adj := omitted_adj_of_high_pairs hp sz degree pair
  have three := port_set_ge_three_of_omitted_adj conn hp ⟨x,mem_Omit.mpr xo⟩ adj
  have hit := pair_port_candidate_hit_cap hc cap hp adj three xo pairx
  have sub : CandHigh p ⊆ (CandHigh p).filter (fun v=>SeesPort p x v) := by
    intro v vm
    refine mem_filter.mpr ⟨vm,sees_some_from_pin_miss_count (pin_vertices_sub_ports (mem_Omit.mpr xo)) ?_⟩
    rw [c]
    exact lt_of_not_ge (fun m => bad ⟨v,vm,show 1 ≤ (Misses G U v).card from le_trans (by decide : 1 ≤ 2) m⟩)
  have n := (card_le_card sub).trans hit
  have lower := cand_high_ge_six hp pos da db degree
  omega

theorem no_nonspanning_length_fourteen_at_twenty (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=14) {x : V} (hx : x∉p.support) : False := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have ql : q.length=14 := by
    have e := hp.2 u v q hq.1
    have f := hq.2 a b p hp.1
    omega
  have sz : (Omit q).card=5 := by have h:=omit_add_length hq; omega
  by_cases triple : ∃ y∈HighOmit q,3≤(Pins q y).card
  · obtain ⟨y,ym,yp⟩ := triple
    exact triple_high_contradiction_fourteen hc conn cap degree hq (by omega) sz du dv ym yp
  apply pair_contradiction_fourteen hc conn cap degree hq (by omega) (by omega) sz du dv
  intro y ym
  have d := degree_covered_by_pins_and_omitted hq (highOmit_data ym).1
  have dy := (highOmit_data ym).2
  have h : ¬3≤(Pins q y).card := fun bad=>triple ⟨y,ym,bad⟩
  omega

#print axioms no_nonspanning_length_fourteen_at_twenty
end Graffiti189LongestPath.SixThreeTwenty
