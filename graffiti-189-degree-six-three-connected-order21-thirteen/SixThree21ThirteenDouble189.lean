import SixThree21ShortGeometry189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeTwenty (HighOmit Sites highOmit_data SeesHighPorts
  two_end_miss_budget candidate_charge_contradiction three_active_of_three_omitted CandL CandR CandHigh
  cand_left_card cand_rotated_path cand_no_omitted_edge orig_cand)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length high_filter_card LM RM)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort SeesEveryPort pin_card_same_support
  left_candidate_sees_port right_candidate_sees_port degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest Graffiti189LongestPath.Rigidity.dist_two from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem one_end_sees_high_ports_at_thirteen_seven (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (len : p.length≤13) (sz : (Omit p).card≤7)
    (da : 6≤G.degree a) (db : 6≤G.degree b) (non : (Sites p (HighOmit p)).Nonempty) :
    SeesHighPorts p a ∨ SeesHighPorts p b := by
  classical
  let I := Sites p (HighOmit p)
  have bounds := two_end_miss_budget hp I non
    (fun i im=>by
      obtain ⟨ir,x,xm,adj⟩ := mem_filter.mp im
      exact ⟨x,(highOmit_data xm).1,mem_filter.mpr ⟨ir,adj⟩⟩)
    (high_sites_separated_seven hc conn cap hp sz)
  have miss (u : V) (no : ¬SeesHighPorts p u) :
      1≤(I.filter (fun i=>¬G.Adj u (p.getVert i))).card := by
    apply card_pos.mpr
    by_contra none
    apply no
    intro x xm w wm xw
    by_contra uw
    obtain ⟨i,ip,e⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp (highOmit_data xm).1 wm xw
    have im : i∈I := mem_filter.mpr ⟨(mem_filter.mp ip).1,x,xm,(Graffiti189LongestPath.pin_data ip).2⟩
    exact none ⟨i,mem_filter.mpr ⟨im,by simpa only [e] using uw⟩⟩
  by_contra no
  have l := miss a (fun h=>no (.inl h))
  have r := miss b (fun h=>no (.inr h))
  omega

theorem double_anchor_forces_low_on_path_thirteen (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (da : 6≤G.degree a) (db : 6≤G.degree b)
    {x : V} (xo : x∉p.support) (xp : 2≤(Pins p x).card) :
    ∃ w∈p.support,¬6≤G.degree w := by
  classical
  by_contra no
  have high (v : V) (vm : v∈p.support) : 6≤G.degree v :=
    Classical.byContradiction (fun bad=>no ⟨v,vm,bad⟩)
  let E := CandL p∪CandR p
  have charged : E⊆DistanceTwo G x := by
    intro v ve
    obtain ⟨u,q,hq,same,_,_⟩ := cand_rotated_path hp ve
    have von := (same v).mpr q.start_mem_support
    have pair : SeesPort p x v := by
      rcases mem_union.mp ve with lm|rm
      · obtain ⟨j,jm,rfl⟩ := mem_image.mp lm
        exact left_candidate_sees_port hp len db xo xp jm (high _ von)
      obtain ⟨j,jm,rfl⟩ := mem_image.mp rm
      exact right_candidate_sees_port hp len da xo xp jm (high _ von)
    obtain ⟨w,wm,xw,vw⟩ := pair
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc (fun e=>xo (e.symm ▸ von))
        (cand_no_omitted_edge hp ve xo) xw vw.symm)
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have ipos := (Graffiti189LongestPath.pin_data ip).1
  have o := orig_cand hp (by omega)
  have e : insert b (CandL p)⊆E := by
    intro v vm
    exact (mem_insert.mp vm).elim (fun eq=>mem_union_right _ (eq.symm ▸ o.2.2.1)) (mem_union_left _)
  have n := (card_le_card e).trans ((card_le_card charged).trans (distanceTwo_le_of_even 6 x (cap x)))
  rw [card_insert_of_not_mem o.2.2.2,cand_left_card hp] at n
  omega

theorem no_double_at_length_thirteen_left (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (da : 6≤G.degree a) (db : 6≤G.degree b)
    (allLeft : SeesHighPorts p a) (allHigh : ∀ y,y∉p.support → 6≤G.degree y)
    {x : V} (xo : x∉p.support) (xp : 2≤(Pins p x).card)
    (A : Finset V) (Ac : 3≤A.card)
    (active : ∀ y∈A,y∉p.support ∧ (Pins p y).Nonempty) : False := by
  classical
  have xm : x∈HighOmit p := mem_filter.mpr ⟨mem_Omit.mpr xo,allHigh x xo⟩
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  apply candidate_charge_contradiction hc cap degree hp da db xo ip (A:=A) (Acard:=Ac)
  · intro j jm dj
    obtain ⟨w,wm,xw,jw⟩ := left_candidate_sees_port hp len db xo xp jm dj
    exact ⟨w,wm,xw,allLeft x xm w wm xw,jw⟩
  · intro j jm dj
    exact right_candidate_sees_port hp len da xo xp jm dj
  · intro y ym
    obtain ⟨yo,j,jp⟩ := active y ym
    have yh : y∈HighOmit p := mem_filter.mpr ⟨mem_Omit.mpr yo,allHigh y yo⟩
    have e := (Graffiti189LongestPath.pin_data jp).2
    exact ⟨yo,p.getVert j,p.getVert_mem_support j,e,allLeft y yh _ (p.getVert_mem_support j) e⟩

theorem no_double_pins_at_length_thirteen_twenty_one (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=13) {x : V} (xo : x∉p.support) : (Pins p x).card≤1 := by
  classical
  by_contra! many
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp xo
  have ql : q.length=13 := by
    have e := hp.2 u v q hq.1
    have f := hq.2 a b p hp.1
    omega
  have sz : (Omit q).card=7 := by have h:=omit_add_length hq; omega
  have xq : x∉q.support := fun h=>xo ((same x).mpr h)
  have xp : 2≤(Pins q x).card := (pin_card_same_support hp hq same xo) ▸ (by omega : 2≤(Pins p x).card)
  obtain ⟨w,won,wl⟩ := double_anchor_forces_low_on_path_thirteen hc cap hq (by omega) du dv xq xp
  have allHigh (y : V) (yo : y∉q.support) : 6≤G.degree y :=
    (degree y w (fun h=>yo (h.symm ▸ won))).resolve_right wl
  have xm : x∈HighOmit q := mem_filter.mpr ⟨mem_Omit.mpr xq,allHigh x xq⟩
  obtain ⟨i,ip⟩ : (Pins q x).Nonempty := card_pos.mp (by omega)
  have non : (Sites q (HighOmit q)).Nonempty := ⟨i,mem_filter.mpr
    ⟨(mem_filter.mp ip).1,x,xm,(Graffiti189LongestPath.pin_data ip).2⟩⟩
  obtain ⟨A,Ac,act⟩ := three_active_of_three_omitted conn hq (by omega)
  rcases one_end_sees_high_ports_at_thirteen_seven hc conn cap hq (by omega) (by omega) du dv non with l|r
  · exact no_double_at_length_thirteen_left hc cap degree hq (by omega) du dv l allHigh xq xp A Ac act
  have hqr := Graffiti189LongestPath.Rigidity.reverse_longest hq
  have eq : ∀ y,y∈q.support ↔ y∈q.reverse.support := fun y=>by simp
  have xr : x∉q.reverse.support := fun h=>xq ((eq x).mpr h)
  have pc : 2≤(Pins q.reverse x).card := (pin_card_same_support hq hqr eq xq) ▸ xp
  have view : SeesHighPorts q.reverse v := by
    intro y ym w' wm yw
    have m := (Graffiti189LongestPath.SixThreeTwenty.highOmit_reverse q) ▸ ym
    exact r y m w' ((eq w').mpr wm) yw
  apply no_double_at_length_thirteen_left hc cap degree hqr (by simp [ql]) dv du view
    (fun y yo=>allHigh y (fun h=>yo ((eq y).mp h))) xr pc A Ac
  intro y ym
  obtain ⟨yo,yp⟩ := act y ym
  exact ⟨fun h=>yo ((eq y).mpr h),card_pos.mp ((pin_card_same_support hq hqr eq yo) ▸ card_pos.mpr yp)⟩

#print axioms no_double_pins_at_length_thirteen_twenty_one
end Graffiti189LongestPath.SixThreeTwentyOne
