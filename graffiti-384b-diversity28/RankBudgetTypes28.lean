import EarCredit28
namespace Graffiti384b.Types28
open Finset SimpleGraph Thin28 EarMix LowSample JointRank
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def exposed := (high G).filter (fun v => ∃e∈twos G,G.Adj v e)

/-- A hypothetical failure can pay at most 1,946,772 for the realizable
ear omissions and for all distinct high neighbors of degree-two vertices. -/
theorem budget (t : (types G).card=28) (hs : (high G).card=26)
    (bad : bound G<gamma G) {E : Finset V} (low : E⊆twos G) (ind : ∀x∈E,∀y∈E,¬G.Adj x y) :
    (∑ e∈E,(26-(contacts G e).card).choose (10-(contacts G e).card))+
      (exposed G).card*170170≤1946772 := by
  classical
  let H := high G
  let r := rank H (trianglesAt G)
  let fee (v : V) := if v∈exposed G then 170170 else 0
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  have per (v : V) (vm : v∈H) :
      hit G H Hᶜ 10 v+fee v≤row (r v)+gain G H Hᶜ 10 v := by
    have ri := mem_image_of_mem (rank H (trianglesAt G)) vm
    rw [rank_range _ _ inj,show H.card=26 from hs,mem_range] at ri
    have rhs := rank_lower H (trianglesAt G) inj 2 rich vm
    have both := high_cost G (H:=H) hs vm (mem_filter.mp vm).2 (r v) ri (by simpa [r,Nat.add_comm] using rhs)
    by_cases ex : v∈exposed G
    · obtain ⟨e,et,ve⟩ := (mem_filter.mp ex).2
      have credit := both.2 ⟨e,(mem_sdiff.mp et).2,ve,(LowSample.two_degree G et).le⟩
      simp only [fee,if_pos ex]
      omega
    · simpa [fee,ex] using both.1
  have pay := sum_le_sum per
  rw [sum_add_distrib,sum_add_distrib] at pay
  have order := sum_by_rank H (trianglesAt G) inj row
  rw [show H.card=26 from hs,rows.2] at order
  change (∑w∈H,row (r w))=_ at order
  have part : (∑v∈H,fee v)=(exposed G).card*170170 := by
    change (∑v∈H,if v∈exposed G then 170170 else 0)=_
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (show exposed G⊆H from filter_subset ..)]
    simp
  have fail : Fintype.card V-14<gamma G := by simpa only [bound,t] using bad
  have need := ear_mass G hs low ind inj fail
  change 15935205+(∑v∈H,gain G H Hᶜ 10 v)+_≤∑v∈H,hit G H Hᶜ 10 v at need
  omega
end Graffiti384b.Types28
#print axioms Graffiti384b.Types28.budget
