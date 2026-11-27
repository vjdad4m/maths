import DegreeFiveRouteBasic189
import OreClosure189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Rooted Ore completion at order at most twice the local degree threshold, with a possible one low vertex
entered first via a real edge to the high class. -/
private theorem rooted_small_Ore_at_d
    (d : ℕ) (R : Finset V) (small : R.card ≤ 2*d) {x : V} (xr : x∈R)
    (mode : (∀ v∈R,d ≤ (R.filter (G.Adj v)).card) ∨
      ((∀ v∈R,v≠x → d ≤ (R.filter (G.Adj v)).card) ∧
        ∃ v∈R,G.Adj x v)) :
    ∃ y∈R,RouteOn G R x y := by
  classical
  let U := ↑(↑R : Set V)
  let J := G.induce (↑R : Set V)
  let xx : U := ⟨x,xr⟩
  have count : Fintype.card U ≤ 2*d := (Fintype.card_coe R).trans_le small
  have law (v : U) : (R.filter (G.Adj v.val)).card = J.degree v :=
    inside_card_eq_degree_induce (G:=G) R v
  let ore : RootedClosureAPI.{u} := by
    intro W _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  have cap (A : Finset U) (h : ∀ v∈A,d≤J.degree v) :
      ∀ v∈A,∀ w∈A,Fintype.card U≤J.degree v+J.degree w := by
    intro v vm w wm
    have p := h v vm
    have q := h w wm
    omega
  have pack (h : RootedSpan J xx) : ∃ y∈R,RouteOn G R x y := by
    obtain ⟨y,p,pp,ps⟩ := h
    exact ⟨y.val,y.property,lift_side_path R p pp ps⟩
  rcases mode with hh|⟨hh,v,vr,xv⟩
  · apply pack
    let A : Finset U := univ
    apply close_completed_class ore A xx (cap A (fun v _=> (law v) ▸ hh v.val v.property))
    obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem J A) (mem_univ xx)
    exact ⟨y,p,pp,fun v=>(ps v).mpr (mem_univ _)⟩
  apply pack
  let A : Finset U := univ.erase xx
  have hi (w : U) (wa : w∈A) : d≤J.degree w := by
    have neq : w.val≠x := fun e=>(mem_erase.mp wa).1 (Subtype.ext e)
    exact (law w) ▸ hh w.val w.property neq
  apply close_completed_class ore A xx (cap A hi)
  let vv : U := ⟨v,vr⟩
  have edge : (completeWith J A).Adj xx vv := (completeWith_mono J A) xv
  exact rooted_path_from_root_into_clique (completeWith J A) edge (completeWith_of_mem J A)

theorem rooted_high_residual_Ore_at_d (d : ℕ) (R : Finset V) (small : R.card≤2*d)
    (high : ∀ v∈R,d≤(R.filter (G.Adj v)).card) {x : V} (xr : x∈R) :
    ∃ y∈R,RouteOn G R x y :=
  rooted_small_Ore_at_d d R small xr (.inl high)

theorem residual_route_if_low_not_isolated_at_d (d : ℕ) (R : Finset V) (small : R.card≤2*d)
    (pos : R.Nonempty)
    (degree : ∀ u∈R,∀ v∈R,u≠v →
      d≤(R.filter (G.Adj u)).card ∨ d≤(R.filter (G.Adj v)).card)
    (hit : ∀ u∈R,(R.filter (G.Adj u)).card<d → ∃ v∈R,G.Adj u v) :
    ∃ x∈R,∃ y∈R,RouteOn G R x y := by
  by_cases h : ∀ u∈R,d≤(R.filter (G.Adj u)).card
  · obtain ⟨x,xr⟩ := pos
    obtain ⟨y,yr,p⟩ := rooted_high_residual_Ore_at_d d R small h xr
    exact ⟨x,xr,y,yr,p⟩
  push_neg at h
  obtain ⟨x,xr,l⟩ := h
  have hh (v : V) (vr : v∈R) (vx : v≠x) : d≤(R.filter (G.Adj v)).card :=
    (degree x xr v vr vx.symm).resolve_left (by omega)
  obtain ⟨y,yr,p⟩ := rooted_small_Ore_at_d d R small xr (.inr ⟨hh,hit x xr l⟩)
  exact ⟨x,xr,y,yr,p⟩

#print axioms rooted_high_residual_Ore_at_d
#print axioms residual_route_if_low_not_isolated_at_d
end Graffiti189LongestPath.CrossSaturation
