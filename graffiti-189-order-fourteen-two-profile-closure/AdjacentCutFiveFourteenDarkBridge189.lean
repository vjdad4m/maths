import CliqueLowInsert189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
variable {W : Type*} [Fintype W] [DecidableEq W] {J : SimpleGraph W} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- Complete the high vertices by the terminal-preserving Ore rule and
insert a single exception between two selectable high neighbors. -/
theorem terminal_route_through_one_dark_exception
    (A : Finset W) {l x y u v : W}
    (covers : insert l A=(univ : Finset W)) (out : l∉A)
    (xa : x∈A) (ya : y∈A) (xy : x≠y)
    (ua : u∈A) (va : v∈A) (uv : u≠v)
    (lu : J.Adj l u) (lv : J.Adj l v)
    (notPair : ¬((x=u ∧ y=v) ∨ (x=v ∧ y=u)))
    (ore : ∀ u∈A,∀ v∈A,u≠v → ¬J.Adj u v →
      Fintype.card W+1≤J.degree u+J.degree v) :
    RouteOn J univ x y := by
  classical
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  have e (u v : W) (edge : H.Adj u v) (old : ¬J.Adj u v) :
      Fintype.card W+1≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at edge
    obtain ⟨a,b,n⟩ := edge.resolve_left old
    exact ore u a v b n old
  have p := clique_path_via_low H A (completeWith_of_mem J A) out xa ya xy ua va uv
    (sub lu) (sub lv) notPair
  obtain ⟨p,pp,ps⟩ := (covers ▸ p : RouteOn H univ x y)
  obtain ⟨q,qp,qs⟩ := terminal_ore_closure sub e p pp (fun z=>(ps z).mpr (mem_univ _))
  exact ⟨q,qp,fun z=>by simp [qs z]⟩

/-- Two nonempty disjoint endpoint classes, one of which offers two choices,
let us avoid a prescribed two-element pair of endpoints. -/
theorem choose_opposite_endpoints_away_from_pair
    (P Q : Finset W) (sep : Disjoint P Q) (p : P.Nonempty) (q : Q.Nonempty)
    (room : 2≤P.card ∨ 2≤Q.card) {u v : W} :
    ∃ x∈P,∃ y∈Q,x≠y ∧ ¬((x=u ∧ y=v) ∨ (x=v ∧ y=u)) := by
  classical
  have bad_unique {x y z : W} (xy : x≠y) (xz : x≠z)
      (h1 : (x=u ∧ y=v) ∨ (x=v ∧ y=u))
      (h2 : (x=u ∧ z=v) ∨ (x=v ∧ z=u)) : y=z := by
    rcases h1 with h|h <;> rcases h2 with k|k
    · exact h.2.trans k.2.symm
    · exact (xy (k.1.trans h.2.symm)).elim
    · exact (xz (h.1.trans k.2.symm)).elim
    · exact h.2.trans k.2.symm
  rcases room with p2|q2
  · obtain ⟨x,xm,z,zm,xz⟩ := one_lt_card.mp p2
    obtain ⟨y,ym⟩ := q
    have xy : x≠y := fun h=>disjoint_left.mp sep xm (h.symm ▸ ym)
    have zy : z≠y := fun h=>disjoint_left.mp sep zm (h.symm ▸ ym)
    by_cases hx : (x=u ∧ y=v) ∨ (x=v ∧ y=u)
    · refine ⟨z,zm,y,ym,zy,?_⟩
      intro hz
      exact xz (bad_unique xy.symm zy.symm
        (by rcases hx with h|h; exact .inr h.symm; exact .inl h.symm)
        (by rcases hz with h|h; exact .inr h.symm; exact .inl h.symm))
    exact ⟨x,xm,y,ym,xy,hx⟩
  obtain ⟨x,xm⟩ := p
  obtain ⟨y,ym,z,zm,yz⟩ := one_lt_card.mp q2
  have xy : x≠y := fun h=>disjoint_left.mp sep xm (h.symm ▸ ym)
  have xz : x≠z := fun h=>disjoint_left.mp sep xm (h.symm ▸ zm)
  by_cases hy : (x=u ∧ y=v) ∨ (x=v ∧ y=u)
  · exact ⟨x,xm,z,zm,xz,fun h=>yz (bad_unique xy xz hy h)⟩
  exact ⟨x,xm,y,ym,xy,hy⟩

#print axioms terminal_route_through_one_dark_exception
#print axioms choose_opposite_endpoints_away_from_pair
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
