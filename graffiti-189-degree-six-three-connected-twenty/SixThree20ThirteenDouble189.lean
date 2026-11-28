import SixThree20ShortGeometry189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length high_filter_card LM RM)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort SeesEveryPort pin_card_same_support
  left_candidate_sees_port right_candidate_sees_port degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def SeesHighPorts {a b : V} (p : G.Walk a b) (u : V) :=
    ∀ x∈HighOmit p,SeesEveryPort p x u

theorem highOmit_reverse {a b : V} (p : G.Walk a b) :
    HighOmit p.reverse=HighOmit p := by ext x; simp [HighOmit,Omit]

theorem one_end_sees_high_ports_at_thirteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (len : p.length≤13) (sz : (Omit p).card≤6)
    (da : 6≤G.degree a) (db : 6≤G.degree b) (non : (Sites p (HighOmit p)).Nonempty) :
    SeesHighPorts p a ∨ SeesHighPorts p b := by
  classical
  let I := Sites p (HighOmit p)
  have bounds := two_end_miss_budget hp I non
    (fun i im=>by
      obtain ⟨ir,x,xm,adj⟩ := mem_filter.mp im
      exact ⟨x,(highOmit_data xm).1,mem_filter.mpr ⟨ir,adj⟩⟩)
    (high_sites_separated hc conn cap hp sz)
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

theorem double_high_contradiction_at_left_thirteen (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (sz : (Omit p).card=6) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (allLeft : SeesHighPorts p a) {x : V} (xm : x∈HighOmit p) (xp : 2≤(Pins p x).card) :
    False := by
  classical
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have xo := (highOmit_data xm).1
  have highCard : 3≤(HighOmit p).card := by
    have h := high_filter_card degree (Omit p)
    change (Omit p).card≤(HighOmit p).card+1 at h
    omega
  apply candidate_charge_contradiction hc cap degree hp da db xo ip
    (A:=HighOmit p) (Acard:=highCard)
  · intro j jm dj
    obtain ⟨w,wm,xw,jw⟩ := left_candidate_sees_port hp len db xo xp jm dj
    exact ⟨w,wm,xw,allLeft x xm w wm xw,jw⟩
  · intro j jm dj
    exact right_candidate_sees_port hp len da xo xp jm dj
  · intro y ym
    obtain ⟨yo,dy⟩ := highOmit_data ym
    have pd := degree_covered_by_pins_and_omitted hp yo
    obtain ⟨j,jp⟩ : (Pins p y).Nonempty := card_pos.mp (by omega)
    have e := (Graffiti189LongestPath.pin_data jp).2
    exact ⟨yo,p.getVert j,p.getVert_mem_support j,e,allLeft y ym _ (p.getVert_mem_support j) e⟩

theorem double_high_contradiction_thirteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (sz : (Omit p).card=6) (da : 6≤G.degree a) (db : 6≤G.degree b)
    {x : V} (xm : x∈HighOmit p) (xp : 2≤(Pins p x).card) :
    False := by
  classical
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have non : (Sites p (HighOmit p)).Nonempty := ⟨i,mem_filter.mpr
    ⟨(mem_filter.mp ip).1,x,xm,(Graffiti189LongestPath.pin_data ip).2⟩⟩
  rcases one_end_sees_high_ports_at_thirteen hc conn cap hp len (by omega) da db non with l|r
  · exact double_high_contradiction_at_left_thirteen hc cap degree hp len sz da db l xm xp
  have hq := Graffiti189LongestPath.Rigidity.reverse_longest hp
  have same : ∀ v,v∈p.support ↔ v∈p.reverse.support := fun v=>by simp
  have xo := (highOmit_data xm).1
  have heq := highOmit_reverse p
  apply double_high_contradiction_at_left_thirteen hc cap degree hq (by simpa using len)
    (by simpa [Omit] using sz) db da ?_ (heq.symm ▸ xm)
    ((pin_card_same_support hp hq same xo) ▸ xp)
  intro y ym w wm yw
  exact r y (heq ▸ ym) w ((same w).mpr wm) yw

#print axioms double_high_contradiction_thirteen
end Graffiti189LongestPath.SixThreeTwenty