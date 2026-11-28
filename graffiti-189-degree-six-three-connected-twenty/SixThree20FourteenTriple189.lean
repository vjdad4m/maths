import SixThree20PortMiss189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit LM RM high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest from Rigidity189
open private Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_misses_sum_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤14) (sz : (Omit p).card≤6) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (non : (PortSet p (HighOmit p)).Nonempty) :
    (Misses G (PortSet p (HighOmit p)) a).card+(Misses G (PortSet p (HighOmit p)) b).card≤2 := by
  have h := miss_budget_vertices hp (HighOmit p) (fun x xm=>(highOmit_data xm).1) non
    (high_sites_separated hc conn cap hp sz)
  omega

theorem high_left_candidate_misses_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤14) (sz : (Omit p).card≤6) (db : 6≤G.degree b)
    (non : (PortSet p (HighOmit p)).Nonempty)
    {j : ℕ} (jm : j∈LM p) (dj : 6≤G.degree (p.getVert j)) :
    (Misses G (PortSet p (HighOmit p)) (p.getVert j)).card+
      (Misses G (PortSet p (HighOmit p)) b).card≤2 := by
  obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start hp j (mem_range.mp (mem_filter.mp jm).1) (mem_filter.mp jm).2
  have high := same_support_high_omit same
  have eq : PortSet p (HighOmit p)=PortSet q (HighOmit q) := by
    rw [←high]
    exact same_support_port_set hp hq same (fun x xm=>(highOmit_data xm).1)
  have size : (Omit q).card≤6 := (same_support_omit same) ▸ sz
  rw [eq]
  exact high_misses_sum_fourteen hc conn cap hq (ql ▸ len) size dj db (eq ▸ non)

theorem high_candidate_misses_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤14) (sz : (Omit p).card≤6) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (non : (PortSet p (HighOmit p)).Nonempty) {v : V} (vm : v∈CandHigh p) :
    (Misses G (PortSet p (HighOmit p)) v).card≤2 := by
  obtain ⟨inE,dv⟩ := mem_filter.mp vm
  obtain ⟨u,q,hq,same,ql,ue⟩ := cand_rotated_path hp inE
  have du : 6≤G.degree u := ue.elim (fun e=>e.symm ▸ da) (fun e=>e.symm ▸ db)
  have high := same_support_high_omit same
  have eq : PortSet p (HighOmit p)=PortSet q (HighOmit q) := by
    rw [←high]
    exact same_support_port_set hp hq same (fun x xm=>(highOmit_data xm).1)
  have size : (Omit q).card≤6 := (same_support_omit same) ▸ sz
  have budget := high_misses_sum_fourteen hc conn cap hq (ql ▸ len) size dv du (eq ▸ non)
  rw [←eq] at budget
  omega

theorem shared_pin_of_miss_sum {a b : V} {p : G.Walk a b} {U : Finset V} {x s t : V}
    (sub : PinVertices p x⊆U)
    (budget : (Misses G U s).card+(Misses G U t).card<(PinVertices p x).card) :
    ∃ w∈p.support,G.Adj x w ∧ G.Adj s w ∧ G.Adj t w := by
  classical
  by_contra no
  have charge : PinVertices p x⊆Misses G U s∪Misses G U t := by
    intro w wm
    obtain ⟨i,ip,ie⟩ := mem_image.mp wm
    have wp : w∈p.support := ie ▸ p.getVert_mem_support i
    have xw : G.Adj x w := ie ▸ (Graffiti189LongestPath.pin_data ip).2
    by_cases sw : G.Adj s w
    · exact mem_union_right _ (mem_filter.mpr ⟨sub wm,fun e=>no ⟨w,wp,xw,sw,e⟩⟩)
    exact mem_union_left _ (mem_filter.mpr ⟨sub wm,sw⟩)
  exact (Nat.not_le_of_lt budget) ((card_le_card charge).trans (card_union_le _ _))

theorem triple_high_at_left_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14)
    (sz : (Omit p).card=5) (da : 6≤G.degree a) (db : 6≤G.degree b)
    {x : V} (xm : x∈HighOmit p) (xp : 3≤(Pins p x).card)
    (orient : (Misses G (PortSet p (HighOmit p)) a).card=0 ∨
      ((Misses G (PortSet p (HighOmit p)) a).card≤1 ∧
       1≤(Misses G (PortSet p (HighOmit p)) b).card)) : False := by
  classical
  let U := PortSet p (HighOmit p)
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have non : U.Nonempty := ⟨p.getVert i,pin_vertices_sub_ports xm (mem_image.mpr ⟨i,ip,rfl⟩)⟩
  have xo := (highOmit_data xm).1
  have xc : 3≤(PinVertices p x).card := by rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp]; exact xp
  have hcA : 3≤(HighOmit p).card := by
    have d := high_filter_card degree (Omit p)
    change (Omit p).card≤(HighOmit p).card+1 at d
    omega
  apply candidate_charge_contradiction hc cap degree hp da db xo ip
    (A:=HighOmit p) (Acard:=hcA)
  · intro j jm dj
    have c := high_left_candidate_misses_fourteen hc conn cap hp len (by omega) db non jm dj
    apply shared_pin_of_miss_sum (pin_vertices_sub_ports xm)
    change (Misses G (PortSet p (HighOmit p)) a).card+(Misses G (PortSet p (HighOmit p)) (p.getVert j)).card<(PinVertices p x).card
    rcases orient with h|⟨ha,hb⟩ <;> omega
  · intro j jm dj
    have h : p.getVert (j+1)∈CandHigh p := mem_filter.mpr
      ⟨mem_union_right _ (mem_image.mpr ⟨j,jm,rfl⟩),dj⟩
    have c := high_candidate_misses_fourteen hc conn cap hp len (by omega) da db non h
    exact sees_some_from_pin_miss_count (pin_vertices_sub_ports xm) (by omega)
  · intro y ym
    obtain ⟨yo,dy⟩ := highOmit_data ym
    refine ⟨yo,sees_some_from_pin_miss_count (pin_vertices_sub_ports ym) ?_⟩
    have d := degree_covered_by_pins_and_omitted hp yo
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp]
    rcases orient with zero|⟨one,_⟩ <;> omega

theorem triple_high_contradiction_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14)
    (sz : (Omit p).card=5) (da : 6≤G.degree a) (db : 6≤G.degree b)
    {x : V} (xm : x∈HighOmit p) (xp : 3≤(Pins p x).card) : False := by
  classical
  by_cases left : (Misses G (PortSet p (HighOmit p)) a).card=0
  · exact triple_high_at_left_fourteen hc conn cap degree hp len sz da db xm xp (.inl left)
  by_cases right : (Misses G (PortSet p (HighOmit p)) b).card=0
  · have hq := Graffiti189LongestPath.Rigidity.reverse_longest hp
    have same : ∀ v,v∈p.support ↔ v∈p.reverse.support := fun v=>by simp
    have high := same_support_high_omit same
    have eq : PortSet p (HighOmit p)=PortSet p.reverse (HighOmit p.reverse) := by
      rw [←high]
      exact same_support_port_set hp hq same (fun x xm=>(highOmit_data xm).1)
    have pc := Graffiti189LongestPath.SixThreeNineteen.pin_card_same_support hp hq same (highOmit_data xm).1
    exact triple_high_at_left_fourteen hc conn cap degree hq
      (by simpa using len) ((same_support_omit same) ▸ sz) db da (high ▸ xm) (pc ▸ xp) (.inl (eq ▸ right))
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have non : (PortSet p (HighOmit p)).Nonempty :=
    ⟨p.getVert i,pin_vertices_sub_ports xm (mem_image.mpr ⟨i,ip,rfl⟩)⟩
  have costs := high_misses_sum_fourteen hc conn cap hp len (by omega) da db non
  exact triple_high_at_left_fourteen hc conn cap degree hp len sz da db xm xp
    (.inr ⟨by omega,by omega⟩)

#print axioms triple_high_contradiction_fourteen
end Graffiti189LongestPath.SixThreeTwenty
