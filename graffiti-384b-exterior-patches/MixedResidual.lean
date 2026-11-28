import ForkPatch
import ChoiceSimultaneous
namespace Graffiti384b.Exterior
open Finset SimpleGraph Four29 LowSample FiveChoice
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A hypothetical failure both defeats every weighted five-point selection
and forces a specific additional edge at every local pair on this backbone. -/
theorem residual (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    (bad : bound G<gamma G) (l : Fin 6 ↪ V)
    (first : G.neighborFinset (l 4)={l 0,l 1}) (second : G.neighborFinset (l 5)={l 2,l 3})
    (bc : G.Adj (l 1) (l 2)) (bd : G.Adj (l 1) (l 3)) :
    (∀F U:Finset V,F⊆pool G (l 4) (l 5) → U⊆pool G (l 4) (l 5) →
      ∀k,F.card+k≤5 → ∀a∈roots G (l 4) (l 5),U.card.choose k≤
      ∑v∈roots G (l 4) (l 5),risk (link G v) (base G (l 4) (l 5)∪F) U k (if v=a then 13 else 2)) ∧
    (∀x∈pool G (l 4) (l 5),∀y∈pool G (l 4) (l 5),x≠y → G.Adj (l 0) x → G.Adj (l 0) y →
      (∃p∈({x,y}:Finset V),∃r∈roots G (l 4) (l 5),G.Adj p r ∧ r≠l 0) ∨
      (∃p∈({x,y}:Finset V),∃r∈triangleContacts G (l 4) (l 5),G.Adj p r ∧ r∉({x,y}:Finset V))) := by
  constructor
  · intro F U fp up k budget a ar
    apply Nat.le_of_not_gt; intro small
    have de : G.degree (l 4)=2 := by rw [←card_neighborFinset_eq_degree,first,card_pair (l.injective.ne (by decide))]
    have df : G.degree (l 5)=2 := by rw [←card_neighborFinset_eq_degree,second,card_pair (l.injective.ne (by decide))]
    exact (not_lt_of_ge (joint_selection G t h q de df (l.injective.ne (by decide)) F U fp up k budget ar small)) bad
  · intro x xp y yp diff ax ay
    by_contra neither
    apply (not_lt_of_ge (fork_patch G t q h l first second bc bd diff xp yp ax ay ?_ ?_)) bad
    · intro p pm r rm pr
      by_contra ne
      exact neither (Or.inl ⟨p,pm,r,rm,pr,ne⟩)
    · intro p pm r rm pr
      by_contra out
      exact neither (Or.inr ⟨p,pm,r,rm,pr,out⟩)
end Graffiti384b.Exterior
#print axioms Graffiti384b.Exterior.residual
