import BicycleFigureCanonical133
import BicycleShapeCatalog133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem exclusion550 (H : Hole G 7) (h4 : FourCycleFree G)
    (f : Fin 9 → V) (inj : Function.Injective f) (outside : ∀ i,Outside H.c (f i))
    (single : ∀ i,∃ k,∀ j,G.Adj (f i) (H.c j) ↔ k=j)
    (edge : ∀ i j,G.Adj (f i) (f j) ↔ dumbRelation 5 5 0 i.val j.val=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  choose site attach using single
  exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
    (dumbRelation 5 5 0) edge Dumb550.labeling
    (fun i j e=>Dumb550.canonical_rows.1 i j e) Dumb550.canonical_rows.2
    Dumb550.distanceTwo_checked Dumb550.checked

private theorem exclusion560 (H : Hole G 7) (h4 : FourCycleFree G)
    (f : Fin 10 → V) (inj : Function.Injective f) (outside : ∀ i,Outside H.c (f i))
    (single : ∀ i,∃ k,∀ j,G.Adj (f i) (H.c j) ↔ k=j)
    (edge : ∀ i j,G.Adj (f i) (f j) ↔ dumbRelation 5 6 0 i.val j.val=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  choose site attach using single
  exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
    (dumbRelation 5 6 0) edge Dumb560.labeling
    (fun i j e=>Dumb560.canonical_rows.1 i j e) Dumb560.canonical_rows.2
    Dumb560.distanceTwo_checked Dumb560.checked

theorem no_single_branch_bicycle_of_singleton_seven [DecidableRel G.Adj]
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p) (S : Finset V)
    (outside : ∀ z∈S,Outside H.c z)
    (singleton : ∀ z∈S, ∃ k, ∀ j,G.Adj z (H.c j) ↔ k=j)
    (noTri : ∀ a b c : (S : Set V),
      G.Adj a.val b.val → G.Adj b.val c.val → G.Adj c.val a.val → False)
    (h : (S : Set V)) (d4 : (G.induce (S : Set V)).degree h=4)
    (d2 : ∀ x≠h,(G.induce (S : Set V)).degree x=2) : False := by
  let J := G.induce (S : Set V)
  have four : FourCycleFree J := by
    intro a b c d ne ac bc ad bd
    exact Subtype.ext (h4 a.val b.val c.val d.val (fun q=>ne (Subtype.ext q)) ac bc ad bd)
  have nine : ¬∃ p : Fin 9 → (S : Set V), InducedPath J p := by
    rintro ⟨p,hp⟩
    exact h9 ⟨Subtype.val ∘ p,Subtype.val_injective.comp hp.1,hp.2⟩
  rcases one_degree_four_yields_a_canonical_figure (G := J) h d4 d2 noTri four nine with
    ⟨f,inj,edges⟩|⟨f,inj,edges⟩
  · exact h9 (exclusion550 H h4 (Subtype.val ∘ f) (Subtype.val_injective.comp inj)
      (fun i=>outside _ (f i).property) (fun i=>singleton _ (f i).property) edges)
  · exact h9 (exclusion560 H h4 (Subtype.val ∘ f) (Subtype.val_injective.comp inj)
      (fun i=>outside _ (f i).property) (fun i=>singleton _ (f i).property) edges)

#print axioms no_single_branch_bicycle_of_singleton_seven
end Graffiti133Bicycle
