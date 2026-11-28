import Cut189
import Mathlib.SetTheory.Cardinal.Finite
namespace Issue189
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
abbrev T (s : Finset V) := {v : V // v ∉ s}
abbrev H (s : Finset V) := G.induce {v : V | v ∉ s}
def tag (v : T xyZ) : Fin 3 := if v.val.val < 9 then 0 else if v.val.val < 15 then 1 else 2
def rep : Fin 3 → T xyZ
  | 0 => ⟨6,by decide⟩
  | 1 => ⟨9,by decide⟩
  | 2 => ⟨15,by decide⟩
theorem tag_rep : ∀ i, tag (rep i) = i := by decide
theorem edge_tag : ∀ a b : T xyZ, (H xyZ).Adj a b → tag a = tag b := by decide
theorem center : ∀ a : T xyZ, a = rep (tag a) ∨ (H xyZ).Adj a (rep (tag a)) := by decide
theorem reach_tag {a b : T xyZ} (p : (H xyZ).Walk a b) : tag a = tag b := by
  induction p with
  | nil => rfl
  | cons e _ ih => exact (edge_tag _ _ e).trans ih
theorem reach_rep (a : T xyZ) : (H xyZ).Reachable a (rep (tag a)) := by
  rcases center a with e|e
  · rw [←e]
  · exact e.reachable
/-- The quotient by graph reachability is literally equivalent to `Fin 3`. -/
def componentEquiv : (H xyZ).ConnectedComponent ≃ Fin 3 where
  toFun := Quot.lift tag (fun _ _ ⟨p⟩ => reach_tag p)
  invFun i := (H xyZ).connectedComponentMk (rep i)
  left_inv := by
    intro c; refine Quot.inductionOn c ?_
    intro v; exact SimpleGraph.ConnectedComponent.sound (reach_rep v).symm
  right_inv := tag_rep
theorem three_components : Nat.card (H xyZ).ConnectedComponent = 3 := by
  simpa using Nat.card_congr componentEquiv
theorem canonical_separates : Separates xyZ := by
  refine ⟨liftB {3},?_,?_,?_,?_⟩ <;> decide
/-- Non-reachability after a deletion gives a separation by the reachable side. -/
theorem separates_of_nreach {s : Finset V} (a b : T s)
    (h : ¬ (H s).Reachable a b) : Separates s := by
  classical
  let u := Finset.univ.filter fun v : V => ∃ hv : v ∉ s, (H s).Reachable a ⟨v,hv⟩
  have umem (v : V) : v ∈ u ↔ ∃ hv : v ∉ s, (H s).Reachable a ⟨v,hv⟩ := by simp [u]
  refine ⟨u, ⟨a.val,(umem _).mpr ⟨a.property,.rfl⟩⟩,?_,⟨b.val,?_,b.property⟩,?_⟩
  · exact Finset.disjoint_left.mpr (fun _ hu hs => ((umem _).mp hu).choose hs)
  · intro hb; exact h ((umem _).mp hb).choose_spec
  · intro x hx y hy ys e
    obtain ⟨xs,ax⟩ := (umem _).mp hx
    have ee : (H s).Adj ⟨x,xs⟩ ⟨y,ys⟩ := e
    exact hy ((umem _).mpr ⟨ys,ax.trans ee.reachable⟩)
theorem no_smaller_or_other_minimum (s : Finset V) (sc : s.card ≤ 13)
    (hn : ¬ (H s).Preconnected) : s = xyZ := by
  classical
  by_contra ne
  apply hn
  intro a b
  by_contra nr
  exact ne (unique_small_cut s (separates_of_nreach a b nr) sc)
theorem cut_is_disconnected : ¬ (H xyZ).Preconnected := by
  intro pc
  obtain ⟨p⟩ := pc (rep 0) (rep 1)
  have e := reach_tag p
  simp [tag_rep] at e
#print axioms no_smaller_or_other_minimum
#print axioms three_components
end Issue189
