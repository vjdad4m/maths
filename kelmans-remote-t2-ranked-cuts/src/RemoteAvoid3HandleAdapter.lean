import HandleCuts
import RemoteAvoid3RootTransfer
import RemoteAvoid3MixedBridge

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3HandleAdapter
open SquareCap (FactorOn SmallTrivial)
open RemoteT2CompletionTransfer (marked eraseEdge SmallerIsolatedAvoid3)
open RemoteAvoid3RootTransfer (sPole tPole use_smaller_avoid3)
open RemoteAvoid3MixedBridge (SmallerRootOmit)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private def chosen {G : SimpleGraph V} {x w r s : V}
    (xw : G.Adj x w) (rs : G.Adj r s) (xr : x≠r) (xs : x≠s) (wr : w≠r) (ws : w≠s) :
    HandleExtension.Edges G where
  a b := if b then r else x
  b b := if b then s else w
  edge := fun b => by cases b <;> assumption
  separated := by
    intro a b v h j
    cases a <;> cases b
    · rfl
    · simp only [Bool.false_eq_true,if_false,if_true] at h j
      rcases h with rfl|rfl <;> rcases j with j|j
      · exact (xr j).elim
      · exact (xs j).elim
      · exact (wr j).elim
      · exact (ws j).elim
    · simp only [Bool.false_eq_true,if_false,if_true] at h j
      rcases j with rfl|rfl <;> rcases h with h|h
      · exact (xr h).elim
      · exact (xs h).elim
      · exact (wr h).elim
      · exact (ws h).elim
    · rfl

/-- Isolated-edge-pattern Avoid3 on order-zero cyclic-four graphs
forces nonincident F2 at strictly smaller order-four inputs when the
two extra handle vertices fit the bound. Uses the published handle
geometry, not a new connectivity premise. -/
theorem smaller_root_omit_of_avoid3 (n : ℕ) (avoid : SmallerIsolatedAvoid3.{u} n) :
    SmallerRootOmit.{u} n := by
  classical
  intro W _ _ G _ budget rem cub cut x r s rs xr xs
  have e : ∃ w : W,G.Adj x w ∧ w≠r ∧ w≠s := by
    by_contra! missing
    have sub : G.neighborFinset x ⊆ ({r,s}:Finset W) := by
      intro v vm
      have h := missing v ((mem_neighborFinset _ _ _).mp vm)
      simp only [mem_insert,mem_singleton]
      by_cases vr : v=r
      · exact Or.inl vr
      · exact Or.inr (h vr)
    have cnt := (card_le_card sub).trans card_le_two
    rw [card_neighborFinset_eq_degree,cub] at cnt
    omega
  obtain ⟨w,xw,wr,ws⟩ := e
  let E := chosen xw rs xr xs wr ws
  let H := E.host
  have old : ∀ a b : W,H.Adj (.inl a) (.inl b) ↔
      G.Adj a b ∧ ¬marked x w a b ∧ ¬marked r s a b := by
    intro a b
    change (G.Adj a b ∧ ¬E.Removed a b) ↔ _
    have false_slot : E.PairFor false a b ↔ marked x w a b := Iff.rfl
    have true_slot : E.PairFor true a b ↔ marked r s a b := Iff.rfl
    constructor
    · rintro ⟨edge,notEither⟩
      exact ⟨edge,fun h=>notEither ⟨false,false_slot.mpr h⟩,
        fun h=>notEither ⟨true,true_slot.mpr h⟩⟩
    · rintro ⟨edge,one,two⟩
      refine ⟨edge,?_⟩
      rintro ⟨which,h⟩
      cases which
      · exact one (false_slot.mp h)
      · exact two (true_slot.mp h)
  have sl : ∀ a : W,H.Adj sPole (.inl a) ↔ a=x∨a=w := fun _=>Iff.rfl
  have tl : ∀ a : W,H.Adj tPole (.inl a) ↔ a=r∨a=s := fun _=>Iff.rfl
  have link : H.Adj sPole tPole := Bool.false_ne_true
  have hu : ∀ v,H.degree v=3 := E.cubic cub
  have hc : SmallTrivial H := E.preserves_small_trivial cub cut
  have c : Fintype.card (W⊕Bool)=Fintype.card W+2 := by simp
  have conn := SquareCap.three_connected_of_small_trivial H hu (by omega) hc
  exact use_smaller_avoid3 G H x w r s xw.ne rs.ne old sl tl link wr ws n (by omega)
    (by omega) hu conn hc avoid

#print axioms smaller_root_omit_of_avoid3
end KelmansCactus.AtomicBridge.RemoteAvoid3HandleAdapter
