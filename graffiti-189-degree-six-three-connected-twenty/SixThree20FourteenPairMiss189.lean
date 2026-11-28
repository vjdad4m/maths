import SixThree20FourteenPairGeometry189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit LM RM high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort pin_card_same_support)
open private Graffiti189LongestPath.Rigidity.reverse_longest from Rigidity189
open private Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem pair_total_miss_budget (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14)
    (sz : (Omit p).card=5) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2)
    (non : (PortSet p (Omit p)).Nonempty) :
    (Misses G (PortSet p (Omit p)) a).card+(Misses G (PortSet p (Omit p)) b).card≤2 := by
  have h := miss_budget_vertices hp (Omit p) (fun v vm=>mem_Omit.mp vm) non
    (all_sites_separated_of_omitted_adj hp (omitted_adj_of_high_pairs hp sz degree pair))
  omega

theorem pair_profile_same_support {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hp : IsLongest p) (hq : IsLongest q) (same : ∀ v,v∈p.support ↔ v∈q.support)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2) :
    ∀ x∈HighOmit q,(Pins q x).card=2 := by
  intro x xm
  have old := (same_support_high_omit same).symm ▸ xm
  exact (pin_card_same_support hp hq same (highOmit_data old).1).symm.trans (pair x old)

theorem pair_left_candidates_hit_of_fixed_right_miss
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14)
    (sz : (Omit p).card=5) (db : 6≤G.degree b)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2)
    (non : (PortSet p (Omit p)).Nonempty)
    (bm : 1≤(Misses G (PortSet p (Omit p)) b).card)
    {v : V} (vl : v∈CandL p) (dv : 6≤G.degree v) {x : V} (xm : x∈HighOmit p) :
    SeesPort p x v := by
  obtain ⟨j,jm,rfl⟩ := mem_image.mp vl
  obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start hp j (mem_range.mp (mem_filter.mp jm).1) (mem_filter.mp jm).2
  have Oeq := same_support_omit same
  have Ueq : PortSet p (Omit p)=PortSet q (Omit q) := by
    rw [←Oeq]
    exact same_support_port_set hp hq same (fun v vm=>mem_Omit.mp vm)
  have bound := pair_total_miss_budget degree hq (ql ▸ len) (Oeq ▸ sz) dv db
    (pair_profile_same_support hp hq same pair) (Ueq ▸ non)
  rw [←Ueq] at bound
  have mx : (PinVertices p x).card=2 := (Graffiti189LongestPath.OneSlack.card_pinVertices hp).trans (pair x xm)
  exact sees_some_from_pin_miss_count (pin_vertices_sub_ports (mem_Omit.mpr (highOmit_data xm).1)) (by omega)

theorem pair_contradiction_if_right_misses_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤14) (pos : 0<p.length)
    (sz : (Omit p).card=5) (da : 6≤G.degree a) (db : 6≤G.degree b)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2)
    (bm : 1≤(Misses G (PortSet p (Omit p)) b).card) : False := by
  classical
  have adj := omitted_adj_of_high_pairs hp sz degree pair
  have on : (Omit p).Nonempty := card_pos.mp (by omega)
  have three := port_set_ge_three_of_omitted_adj conn hp on adj
  have non : (PortSet p (Omit p)).Nonempty := card_pos.mp (by omega)
  let HL := (CandL p).filter (fun v=>6≤G.degree v)
  have lower : 5≤HL.card := by
    have cn := cand_left_card hp
    have n := high_filter_card degree (CandL p)
    change (CandL p).card≤HL.card+1 at n
    omega
  have leftSub (x : V) (xm : x∈HighOmit p) :
      HL⊆(CandHigh p).filter (fun v=>SeesPort p x v) := by
    intro v vm
    obtain ⟨vl,dv⟩ := mem_filter.mp vm
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_union_left _ vl,dv⟩,
      pair_left_candidates_hit_of_fixed_right_miss degree hp len sz db pair non bm vl dv xm⟩
  have capHit (x : V) (xm : x∈HighOmit p) :
      ((CandHigh p).filter (fun v=>SeesPort p x v)).card≤5 :=
    pair_port_candidate_hit_cap hc cap hp adj three (highOmit_data xm).1 (pair x xm)
  by_cases pathHigh : ∀ v∈p.support,6≤G.degree v
  · have eq : HL=CandL p := by
      apply Subset.antisymm (filter_subset _ _)
      intro v vm
      obtain ⟨j,jm,e⟩ := mem_image.mp vm
      exact mem_filter.mpr ⟨vm,pathHigh v (e ▸ p.getVert_mem_support j)⟩
    have Hn : (HighOmit p).Nonempty := card_pos.mp (by
      have ht := high_filter_card degree (Omit p)
      change (Omit p).card≤(HighOmit p).card+1 at ht
      omega)
    obtain ⟨x,xm⟩ := Hn
    have bound := (card_le_card (leftSub x xm)).trans (capHit x xm)
    rw [eq,cand_left_card hp] at bound
    omega
  have low : ∃ w∈p.support,¬6≤G.degree w := by
    by_contra no
    exact pathHigh (fun w wm => Classical.byContradiction (fun h => no ⟨w,wm,h⟩))
  obtain ⟨w,wm,dw⟩ := low
  have bSeen : ∃ z∈PortSet p (Omit p),G.Adj b z := by
    by_contra no
    have sub : PortSet p (Omit p)⊆Misses G (PortSet p (Omit p)) b :=
      fun z zm=>mem_filter.mpr ⟨zm,fun e=>no ⟨z,zm,e⟩⟩
    have bound := pair_total_miss_budget degree hp len sz da db pair non
    have n := card_le_card sub
    omega
  obtain ⟨z,zm,bz⟩ := bSeen
  obtain ⟨zp,x,xO,xz⟩ := (mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mp zm
  have xo := mem_Omit.mp xO
  have xw : x≠w := fun e=>xo (e.symm ▸ wm)
  have xm : x∈HighOmit p := mem_filter.mpr ⟨xO,(degree x w xw).resolve_right dw⟩
  have bOutside : b∉HL := fun e=>(orig_cand hp pos).2.2.2 (mem_filter.mp e).1
  have bCap : b∈(CandHigh p).filter (fun v=>SeesPort p x v) :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_union_right _ (orig_cand hp pos).2.2.1,db⟩,z,zp,xz,bz⟩
  have sub : insert b HL⊆(CandHigh p).filter (fun v=>SeesPort p x v) := by
    intro v vm
    exact (mem_insert.mp vm).elim (fun e=>e.symm ▸ bCap) (fun h=>leftSub x xm h)
  have d := (card_le_card sub).trans (capHit x xm)
  rw [card_insert_of_not_mem bOutside] at d
  omega

#print axioms pair_contradiction_if_right_misses_fourteen
end Graffiti189LongestPath.SixThreeTwenty
