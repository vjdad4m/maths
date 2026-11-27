import BicycleFigureBounds133
import BicycleShapeCheck133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem figure55_labels : ∀ i j : Fin 9,
    figureRel 4 4 i.val j.val ↔ dumbRelation 5 5 0 i.val j.val=true := by decide
private theorem figure56_labels : ∀ i j : Fin 10,
    figureRel 4 5 i.val j.val ↔ dumbRelation 5 6 0 i.val j.val=true := by decide

theorem one_degree_four_yields_a_canonical_figure [DecidableRel G.Adj] (h : V)
    (d4 : G.degree h=4) (d2 : ∀ x≠h,G.degree x=2)
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9 → V, InducedPath G p) :
    (∃ f : Fin 9 → V, Function.Injective f ∧
      ∀ i j, G.Adj (f i) (f j) ↔ dumbRelation 5 5 0 i.val j.val=true) ∨
    (∃ f : Fin 10 → V, Function.Injective f ∧
      ∀ i j, G.Adj (f i) (f j) ↔ dumbRelation 5 6 0 i.val j.val=true) := by
  obtain ⟨P⟩ := degree_four_single_branch_has_two_paths h d4 d2
  rcases P.small_figure_keys noTri h4 h9 with ⟨en,em⟩|⟨en,em⟩|⟨en,em⟩
  · have M := P.figureModel
    rw [en,em] at M
    exact Or.inl ⟨M.f,M.inj,fun i j => (M.adj i j).trans (figure55_labels i j)⟩
  · have M := P.figureModel
    rw [en,em] at M
    exact Or.inr ⟨M.f,M.inj,fun i j => (M.adj i j).trans (figure56_labels i j)⟩
  · have M := P.swap.figureModel
    change FigureModel G P.two.n P.one.n at M
    rw [en,em] at M
    exact Or.inr ⟨M.f,M.inj,fun i j => (M.adj i j).trans (figure56_labels i j)⟩

#print axioms one_degree_four_yields_a_canonical_figure
end Graffiti133Bicycle
