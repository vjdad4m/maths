import TreeBudget

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Distance along the unique path to a root supplies the rank
conditions used by the catalogue's induced-tree certificate. -/
theorem rooted_tree_rank (tree : G.IsTree) (r : V) :
    ∃ rank : V → ℕ, (∀ x, rank x = 0 ↔ x = r) ∧
      (∀ ⦃x y⦄, G.Adj x y → rank x ≠ rank y) ∧
      ∀ x, x ≠ r → ∃! y, G.Adj x y ∧ rank y < rank x := by
  classical
  choose p path unique using fun x => tree.existsUnique_path x r
  let rank (x : V) := (p x).length
  have next {x y : V} (h : G.Adj x y) (ord : rank y ≤ rank x) :
      p x = (p y).cons h := by
    have off : x ∉ (p y).support := by
      intro on
      have single : h.symm.toWalk.IsPath :=
        by simp [SimpleGraph.Adj.toWalk,Walk.isPath_def,h.ne.symm]
      have pref := (tree.existsUnique_path y x).unique ((path y).takeUntil on) single
      have suff := (unique x) ((p y).dropUntil x on) ((path y).dropUntil on)
      have split := congrArg Walk.length ((p y).take_spec on)
      rw [Walk.length_append,pref,suff] at split
      change (h.symm.toWalk).length + rank x = rank y at split
      change 1 + rank x = rank y at split
      omega
    exact (unique x _ ((Walk.cons_isPath_iff _ _).mpr ⟨path y,off⟩)).symm
  have sm {x y : V} (h : G.Adj x y) (ord : rank y ≤ rank x) : rank x = rank y + 1 :=
    congrArg Walk.length (next h ord)
  have zero (x : V) : rank x = 0 ↔ x = r := by
    constructor
    · intro h
      apply Classical.byContradiction
      intro ne
      have length := (p x).length_tail_add_one (Walk.not_nil_of_ne ne)
      change (p x).length = 0 at h
      omega
    · intro eq
      subst x
      change (p r).length = 0
      rw [show p r = Walk.nil from (unique r _ Walk.IsPath.nil).symm]
      rfl
  refine ⟨rank,zero,?_,?_⟩
  · intro x y adj eq
    have h := sm adj (le_of_eq eq.symm)
    omega
  · intro x xr
    let y := (p x).snd
    have nn := Walk.not_nil_of_ne (p := p x) xr
    have xy : G.Adj x y := Walk.adj_snd nn
    have tail := unique y (p x).tail (path x).tail
    have len := (p x).length_tail_add_one nn
    rw [tail] at len
    change rank y + 1 = rank x at len
    refine ⟨y,⟨xy,by omega⟩,?_⟩
    intro z hz
    have eq := congrArg (fun (w : G.Walk x r) => w.snd) (next hz.1 hz.2.le)
    simpa only [y,Walk.snd_cons] using eq.symm

#print axioms rooted_tree_rank

end Graffiti199Depleted.Catalogue
