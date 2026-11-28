import EarPairing
import EarDonorPairs
import SeparatorParity
import EarTriangleLoss
namespace Graffiti384b.OddStars.EarKernel
open Finset SimpleGraph PositivePalette EarPacking EarFootprint EarDonors ComponentPort SingleLeaf LeafCharacterization
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Necessary matching and simultaneous-omission tests, with no numerical
restriction on order or number of distinct triangle counts. -/
def Passes : Prop :=
  (∀v,trianglesAt G v≤ EarTriangleLoss.inside G v+2) ∧
  (∀e,trianglesAt G e=1 → ∃L R : Finset V,Disjoint L R ∧ L∪R=insert e (rich G) ∧
    ∃f : L≃R,∀x,(patch G ∅).Adj x.val (f x).val) ∧
  ∀F : Finset V,(∀v∈F,trianglesAt G v=1) → (∀x∈F,∀y∈F,¬(patch G ∅).Adj x y) →
    (2*F.card≤(anchors G F).card+1 ∧
     ∃L R : Finset V,Disjoint L R ∧ L∪R=residual G F ∧
       R.card+2*F.card=L.card+(anchors G F).card+1 ∧
       ∃f : L→R,Function.Injective f ∧ ∀x,(patch G ∅).Adj x.val (f x).val) ∧
    (donors G F).card≤14 ∧ ((anchors G F).card<2*F.card → (donors G F).card≤6)

theorem necessary (bad : bound G<gamma G) (present : 1∈types G) : Passes G :=
  ⟨EarTriangleLoss.loss_at_most_two G bad,fun _ one => EarPairing.actual_perfect G bad one,
   fun _ one ind => ⟨matching_profile G bad present one ind,EarDonorPairs.fourteen_donors G bad present one ind,
     six_donors G bad present one ind⟩⟩

/-- Remaining exact class after an arbitrary-order failure is reduced
to a connected triangle-supported core rooted at the attachment of its only leaf. -/
def RemainingThrough (N : ℕ) : Prop :=
  ∀(W : Type u) [Fintype W] [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj],
    K.Connected → (∀v,0<trianglesAt K v) → (∀{x y},K.Adj x y → ∃z,K.Adj x z ∧ K.Adj y z) →
    (∃e,K.degree e=2 ∧ trianglesAt K e=1) →
    ∀r : W,Fintype.card W+1≤N → Passes (withLeaf K r) → gamma (withLeaf K r)≤bound (withLeaf K r)

theorem catalogue_iff_remaining (N : ℕ) : CatalogueThrough.{u} N ↔ RemainingThrough.{u} N := by
  rw [EarCoreReduction.catalogue_iff_ear_core]
  constructor
  · intro h W _ _ K _ conn pos edges ear r order _
    exact h W K conn pos edges ear r order
  · intro h W _ _ K _ conn pos edges ear r order
    by_contra! bad
    obtain ⟨e,deg,one⟩ := ear
    have mem : 1∈types (withLeaf K r) := mem_image.mpr ⟨.inl e,mem_univ _,((leaf_scores K r).1 e).trans one⟩
    exact (Nat.not_le_of_gt bad) (h W K conn pos edges ⟨e,deg,one⟩ r order (necessary _ bad mem))

end Graffiti384b.OddStars.EarKernel
#print axioms Graffiti384b.OddStars.EarKernel.necessary
#print axioms Graffiti384b.OddStars.EarKernel.catalogue_iff_remaining
