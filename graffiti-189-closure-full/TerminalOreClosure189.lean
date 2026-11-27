import TwoTerminalOre189
import OreClosure189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
open private liftCap_support leaf_cap_degree_ge from OreClosure189
open private cap_path_forces_end from TwoTerminalOre189
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

/-- Two-terminal version of the degree-sum closure, with the terminal
vertices unchanged and no assumptions on edges already in the graph. -/
theorem terminal_ore_closure (sub : G≤H)
    (deg : ∀ u v : V,H.Adj u v → ¬G.Adj u v → Fintype.card V+1≤G.degree u+G.degree v)
    {x y : V} (p : H.Walk x y) (pp : p.IsPath) (ps : ∀ v,v∈p.support) :
    ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  let P (v : V) := v=y
  have hm : cap G P≤cap H P := by
    intro i j e
    cases i <;> cases j <;> try exact e
    exact sub e
  have hw : Graffiti189Ore.Rooted (cap H P) (some x) := by
    let q := p.map (liftCap H P)
    have qp : q.IsPath := IsPath.mk'
      (liftCap_support p ▸ pp.support_nodup.map (liftCap_injective H P))
    have off : (none : Option V)∉q.support := by
      change (none : Option V)∉(p.map (liftCap H P)).support
      rw [liftCap_support]
      simp
    let e : (cap H P).Adj (some y) none := rfl
    refine ⟨none,q.concat e,path_concat_new q qp e off,?_⟩
    intro z
    cases z with
    | none => exact (q.concat e).end_mem_support
    | some v =>
      rw [support_concat,List.concat_eq_append]
      exact List.mem_append_left _ (liftCap_support p ▸ List.mem_map.mpr ⟨v,ps v,rfl⟩)
  apply cap_path_forces_end
  apply Graffiti189Ore.rooted_closure hm (some x) _ hw
  intro i j e no
  cases i <;> cases j
  · exact (no e).elim
  · exact (no e).elim
  · exact (no e).elim
  rename_i u v
  have c := deg u v e no
  have zu := leaf_cap_degree_ge (G:=G) y u
  have zv := leaf_cap_degree_ge (G:=G) y v
  change G.degree u≤(cap G P).degree (some u) at zu
  change G.degree v≤(cap G P).degree (some v) at zv
  rw [Fintype.card_option]
  omega

#print axioms terminal_ore_closure
end Graffiti189LongestPath.CrossSaturation
