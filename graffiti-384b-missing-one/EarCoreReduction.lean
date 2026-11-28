import EarComponent
namespace Graffiti384b.OddStars.EarCoreReduction
open Finset SimpleGraph PositivePalette ComponentPort SingleLeaf LeafCharacterization
open private TrianglePrune.triangle_iff from TrianglePrune384b
universe u

/-- The terminal class is one new leaf on an all-positive, triangle-supported,
connected core which contains a degree-two vertex with score one. -/
def EarCoresThrough (N : ℕ) : Prop :=
  ∀(V : Type u) [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj],
    K.Connected → (∀v,0<trianglesAt K v) → (∀{x y},K.Adj x y → ∃z,K.Adj x z ∧ K.Adj y z) →
    (∃e,K.degree e=2 ∧ trianglesAt K e=1) →
    ∀r : V,Fintype.card V+1≤N → gamma (withLeaf K r)≤bound (withLeaf K r)

theorem catalogue_iff_ear_core (N : ℕ) : CatalogueThrough.{u} N ↔ EarCoresThrough.{u} N := by
  rw [catalogue_iff_single_leaf]
  constructor
  · intro all V _ _ K _ conn pos support _ r limit
    exact all _ K conn pos support r limit
  · intro cases V _ _ K _ conn pos support r limit
    let E := withLeaf K r
    by_cases has : 1∈types K
    · obtain ⟨e,_,sc⟩ := mem_image.mp has
      have nb : (patch K ∅).neighborFinset e=K.neighborFinset e := by
        ext y; simp only [mem_neighborFinset]
        exact ⟨fun h => h.1,fun h => ⟨h,Or.inl (support h)⟩⟩
      have degree := congrArg Finset.card nb
      simp only [card_neighborFinset_eq_degree] at degree
      have hi := LeafCritical.skeleton_degree_bound K e
      rw [degree,sc] at hi
      obtain ⟨x,y,xe,ye,xy⟩ := (TrianglePrune.triangle_iff K e).mp (by omega)
      have lo := Prerequisites.deg2 K xy.ne xe ye
      exact cases _ K conn pos support ⟨e,by omega,sc⟩ r limit
    · have sc := leaf_scores K r
      have absent : 1∉types E := by
        intro one; obtain ⟨v,_,e⟩ := mem_image.mp one
        cases v with
        | inl w => exact has (mem_image.mpr ⟨w,mem_univ _,(sc.1 w).symm.trans e⟩)
        | inr w => cases w; have err := sc.2.1.symm.trans e; omega
      obtain ⟨a,b,ra,rb,ab⟩ := (TrianglePrune.triangle_iff K r).mp (pos r)
      have lo := Prerequisites.deg2 K ab.ne ra rb
      have hi := K.degree_lt_card_verts r
      exact MissingOne.exact E (leaf_connected K conn r) (by rw [Fintype.card_sum,Fintype.card_unit]; omega) absent
end Graffiti384b.OddStars.EarCoreReduction
#print axioms Graffiti384b.OddStars.EarCoreReduction.catalogue_iff_ear_core
