import EdgeMass

namespace Graffiti384b.Donor
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Apply the exact discount incidence count to an averaged budget. An actual
sample either meets the ordinary budget or meets the enlarged budget and has
the specified usable adjacent pair. The donor can even belong to the pool. -/
theorem incidence_at_budget (F X : Finset V) (fx : Disjoint F X) (u v : V) (edge : G.Adj u v)
    (outside : u∉F∪X) {b cap : ℕ} (pos : 0<b)
    (budget : (∑x,loss G F X b x)<(cap+1)*X.card.choose b+(pairTrials G F X b u v).card) :
    ∃k∈X.powersetCard b,
      ((deficient G (F∪k)).card≤cap ∨
       (k∈pairTrials G F X b u v ∧ (deficient G (F∪k)).card≤cap+1)) ∧
      gamma G≤F.card+b+cap := by
  classical
  let Q := pairTrials G F X b u v
  let trials := X.powersetCard b
  obtain ⟨k,kb,hit⟩ : ∃k∈trials,(deficient G (F∪k)).card≤cap ∨
      (k∈Q ∧ (deficient G (F∪k)).card≤cap+1) := by
    by_contra! none
    have each (k : Finset V) (kb : k∈trials) :
        cap+1+(if k∈Q then 1 else 0)≤(deficient G (F∪k)).card := by
      obtain ⟨n,e⟩ := none k kb
      split_ifs with q
      · exact e q
      · omega
    have lower := sum_le_sum each
    have sub : Q⊆trials := filter_subset ..
    rw [sum_add_distrib,sum_const,sum_boole,filter_mem_eq_inter,inter_eq_right.mpr sub] at lower
    change trials.card*(cap+1)+Q.card ≤ _ at lower
    rw [Nat.mul_comm] at lower
    unfold trials at lower
    rw [card_powersetCard,total_loss G F X fx pos] at lower
    exact (not_lt_of_ge lower) budget
  obtain ⟨ks,sz⟩ := mem_powersetCard.mp kb
  have size : (F∪k).card=F.card+b := by rw [card_union_of_disjoint (fx.mono_right ks),sz]
  refine ⟨k,kb,hit,?_⟩
  rcases hit with cheap|⟨q,cheap⟩
  · have ordinary := batch_repair_saves G (F∪k) ∅ (empty_subset _) (by simp)
    change gamma G≤(F∪k).card+(deficient G (F∪k)).card-(∅ : Finset V).card at ordinary
    simp only [card_empty,Nat.sub_zero,size] at ordinary
    omega
  · obtain ⟨_,one,vd⟩ := mem_filter.mp q
    obtain ⟨vs,defv⟩ := (mem_filter.mp vd).2
    have bound := pair_repair_saves G (F∪k) u v edge (fun m => outside (union_subset_union (Subset.rfl : F⊆F) ks m)) vs one defv
    change gamma G≤(F∪k).card+(deficient G (F∪k)).card-1 at bound
    omega

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.incidence_at_budget
