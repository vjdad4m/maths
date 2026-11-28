import FiveFrontData
import FiveSym
import Case0Cover
namespace Graffiti384b.PairMix.Local

/-- Every assignment of the thirty-six high-vertex edges admits the protected cut
when the four anchor scores are at least two and one is at least thirteen. -/
theorem five_large : FiniteClaim :=
  up_to_symmetry (fun a rich => from_tree 0 a rich full0 tested0)
open Finset SimpleGraph LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The same patch is sufficient even if other vertices also lie on anchor triangles.
All triangle lower bounds here refer only to the induced eleven-vertex graph. -/
theorem protected_patch (f : Label ↪ V) (quota : (types G).card≤(nonleaves G).card)
    (ears : ∀z∈twos G,z=f 9 ∨ z=f 10)
    (shape : ∀i j:Label,(9≤ i.val ∨ 9≤j.val) → (preset i j=true ↔ G.Adj (f i) (f j)))
    (pos : ∀r:Root,2≤ inducedScore G f (atRoot r)) (h : Root)
    (large : 13≤ inducedScore G f (atRoot h)) : gamma G≤bound G :=
  labels_induced G five_large f quota ears shape pos h large
end Graffiti384b.PairMix.Local

namespace Graffiti384b.Four29
open Finset SimpleGraph Donor LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Closed five-contact branch in the exact twenty-nine nonleaf profile. -/
theorem five_contacts (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (few : (triangleContacts G e f).card≤5) : gamma G≤bound G :=
  five_from_local G PairMix.Local.five_large t h q de df ne few

/-- A remaining failure has six to fourteen triangle contacts and an anchor on
at least thirteen triangles. The earlier caps on double exposure still apply. -/
theorem five_contact_residual (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) (bad : bound G<gamma G) {e f : V}
    (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f) :
    (∃v∈roots G e f,13≤trianglesAt G v) ∧ 6≤(triangleContacts G e f).card ∧
    (triangleContacts G e f).card≤(exposed G (pool G e f)).card ∧ (exposed G (pool G e f)).card≤14 ∧
    ((exposed G (pool G e f)).card=14 → (twice G (pool G e f)).card≤6) ∧
    ((exposed G (pool G e f)).card=13 → (twice G (pool G e f)).card≤10) := by
  refine ⟨?_,?_,(residual G t h q bad de df ne).2⟩
  · by_contra! low
    exact (not_lt_of_ge (PairMix.low_anchors G t q h de df ne (fun v vm => by have := low v vm; omega))) bad
  · by_contra! small
    exact (not_lt_of_ge (five_contacts G t h q de df ne (by omega))) bad
end Graffiti384b.Four29
#print axioms Graffiti384b.PairMix.Local.five_large
#print axioms Graffiti384b.PairMix.Local.protected_patch
#print axioms Graffiti384b.Four29.five_contacts
#print axioms Graffiti384b.Four29.five_contact_residual
