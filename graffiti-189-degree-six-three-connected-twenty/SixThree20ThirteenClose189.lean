import SixThree20SingleCharge189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit high_filter_card omit_add_length)
open Graffiti189LongestPath.SixThreeNineteen (degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem all_single_high_contradiction_thirteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (sz : (Omit p).card=6) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (all : ∀ y∈HighOmit p,(Pins p y).card=1) : False := by
  classical
  have high : (HighOmit p).Nonempty := by
    apply card_pos.mp
    have h := high_filter_card degree (Omit p)
    change (Omit p).card≤(HighOmit p).card+1 at h
    omega
  have univ (x : V) (xm : x∈HighOmit p) :
      ∀ y,y∉p.support → x≠y → G.Adj x y := by
    apply high_omitted_universal_when_exact_degree_room hp xm
    rw [all x xm,sz]
  obtain ⟨x,xm⟩ := high
  let I := Sites p (HighOmit p)
  have three : 3≤I.card := high_sites_at_least_three_of_universal_and_no_low_ports conn hp xm (univ x xm)
    (fun y yo dy=>low_omitted_no_pins_at_six hp sz degree all yo dy)
  have inhab : I.Nonempty := card_pos.mp (by omega)
  obtain ⟨i,ip⟩ := inhab
  have h : (I.erase i).Nonempty := card_pos.mp (by rw [card_erase_of_mem ip]; omega)
  obtain ⟨j,jp⟩ := h
  have h : ((I.erase i).erase j).Nonempty := card_pos.mp (by
    rw [card_erase_of_mem jp,card_erase_of_mem ip]
    omega)
  obtain ⟨k,kp⟩ := h
  have ji := (mem_erase.mp jp).1
  have ki := (mem_erase.mp (mem_erase.mp kp).2).1
  have kj := (mem_erase.mp kp).1
  have jp' := (mem_erase.mp jp).2
  have kp' := (mem_erase.mp (mem_erase.mp kp).2).2
  obtain ⟨ir,u,um,ui⟩ := mem_filter.mp ip
  obtain ⟨jr,v,vm,vj⟩ := mem_filter.mp jp'
  obtain ⟨kr,w,wm,wk⟩ := mem_filter.mp kp'
  have iu : i∈Pins p u := mem_filter.mpr ⟨ir,ui⟩
  have jv : j∈Pins p v := mem_filter.mpr ⟨jr,vj⟩
  have kw : k∈Pins p w := mem_filter.mpr ⟨kr,wk⟩
  have ci := single_port_candidate_hit_cap hc cap hp um (all u um) (univ u um) iu jp' kp' ji.symm ki.symm kj.symm
  have cj := single_port_candidate_hit_cap hc cap hp vm (all v vm) (univ v vm) jv ip kp' ji kj.symm ki.symm
  have ck := single_port_candidate_hit_cap hc cap hp wm (all w wm) (univ w wm) kw ip jp' ki kj ji.symm
  have pos : 0<p.length := by have n:=mem_range.mp ir; omega
  have eh := cand_high_ge_six hp pos da db degree
  have pair {s t : ℕ} (sm : s∈I) (tm : t∈I) (ne : s≠t) :
      ∀ z∈CandHigh p,G.Adj z (p.getVert s) ∨ G.Adj z (p.getVert t) := by
    intro z zh
    obtain ⟨sl,y,ym,ys⟩ := mem_filter.mp sm
    obtain ⟨tl,y',ym',yt⟩ := mem_filter.mp tm
    have ne' : p.getVert s≠p.getVert t := fun e=>ne
      (hp.1.getVert_injOn (mem_range.mp sl).le (mem_range.mp tl).le e)
    exact high_candidate_cannot_miss_two_at_thirteen hp len da db zh (highOmit_data ym).1 (highOmit_data ym').1
      (p.getVert_mem_support s) (p.getVert_mem_support t) ys yt ne'
  have endAll := one_end_sees_high_ports_at_thirteen hc conn cap hp len (by omega) da db ⟨i,ip⟩
  rcases endAll with l|r
  · have am : a∈CandHigh p := mem_filter.mpr ⟨mem_union_left _ (orig_cand hp pos).1,da⟩
    exact three_candidate_miss_contradiction G _ eh a am _ _ _ ci cj ck
      (l u um _ (p.getVert_mem_support i) ui) (l v vm _ (p.getVert_mem_support j) vj)
      (l w wm _ (p.getVert_mem_support k) wk)
      (pair ip jp' ji.symm) (pair ip kp' ki.symm) (pair jp' kp' kj.symm)
  have bm : b∈CandHigh p := mem_filter.mpr ⟨mem_union_right _ (orig_cand hp pos).2.2.1,db⟩
  exact three_candidate_miss_contradiction G _ eh b bm _ _ _ ci cj ck
    (r u um _ (p.getVert_mem_support i) ui) (r v vm _ (p.getVert_mem_support j) vj)
    (r w wm _ (p.getVert_mem_support k) wk)
    (pair ip jp' ji.symm) (pair ip kp' ki.symm) (pair jp' kp' kj.symm)

theorem no_nonspanning_length_thirteen_at_twenty (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=13) {x : V} (hx : x∉p.support) : False := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have ql : q.length=13 := by
    have e := hp.2 u v q hq.1
    have f := hq.2 a b p hp.1
    omega
  have sz : (Omit q).card=6 := by have h:=omit_add_length hq; omega
  by_cases double : ∃ y∈HighOmit q,2≤(Pins q y).card
  · obtain ⟨y,ym,yp⟩ := double
    exact double_high_contradiction_thirteen hc conn cap degree hq (by omega) sz du dv ym yp
  apply all_single_high_contradiction_thirteen hc conn cap degree hq (by omega) sz du dv
  intro y ym
  have d := degree_covered_by_pins_and_omitted hq (highOmit_data ym).1
  have dy := (highOmit_data ym).2
  have h : ¬2≤(Pins q y).card := fun bad=>double ⟨y,ym,bad⟩
  omega

#print axioms no_nonspanning_length_thirteen_at_twenty
end Graffiti189LongestPath.SixThreeTwenty
