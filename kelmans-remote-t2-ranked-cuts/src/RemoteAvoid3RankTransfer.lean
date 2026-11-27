import HandleCuts
import RemoteT2CompletionTransfer
import RemoteT2AvoidThree

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3RankTransfer
open SquareCap (SmallTrivial ThreeConnected FactorOn omitEdge)
open RemoteT2Scope (Remote)
open RemoteT2CompletionTransfer (marked eraseEdge SmallerIsolatedAvoid3)
open RemoteT2AvoidThree (selected target use_remote_promise xh yh)
universe u

/-- The exact cyclic-four remote pair-deletion promise, with a
strict original graph-order upper bound. -/
def SmallerRemoteT2 (n : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V<n → Fintype.card V%6=2 → (∀ x,G.degree x=3) →
    ThreeConnected G → SmallTrivial G →
    ∀ x y a b : V, G.Adj x y → G.Adj a b → Remote G x a b →
      FactorOn (omitEdge G a b) ((univ.erase x).erase y)

private def chosen {V : Type u} {G : SimpleGraph V} {a b d e : V}
    (ab : G.Adj a b) (de : G.Adj d e) (ad : a≠d) (ae : a≠e) (bd : b≠d) (be : b≠e) :
    HandleExtension.Edges G where
  a z := if z then d else a
  b z := if z then e else b
  edge z := by cases z <;> assumption
  separated := by
    intro z w x a b
    cases z <;> cases w
    · rfl
    · simp only [Bool.false_eq_true,if_false,if_true] at a b
      rcases a with rfl|rfl <;> rcases b with q|q
      · exact (ad q).elim
      · exact (ae q).elim
      · exact (bd q).elim
      · exact (be q).elim
    · simp only [Bool.false_eq_true,if_false,if_true] at a b
      rcases b with rfl|rfl <;> rcases a with q|q
      · exact (ad q).elim
      · exact (ae q).elim
      · exact (bd q).elim
      · exact (be q).elim
    · rfl

/-- The public disjoint-edge handle raises old order by exactly two;
hence a bounded Remote T2 assumption at n+2 supplies precisely the
strictly smaller isolated-pattern Avoid3 assumption at n. The
third edge may share endpoints with the second, but not the first. -/
theorem smaller_avoid3_of_remote (n : ℕ) (remote : SmallerRemoteT2.{u} (n+2)) :
    SmallerIsolatedAvoid3.{u} n := by
  classical
  intro V _ _ G _ size cub _ small rem a b d e r s ab de rs ad ae bd be ar as br bs last
  let E := chosen ab de ad ae bd be
  let H := E.host
  have old : ∀ x y : V,H.Adj (.inl x) (.inl y) ↔
      G.Adj x y∧¬selected a b x y∧¬selected d e x y := by
    intro x y
    change (G.Adj x y∧¬E.Removed x y) ↔ _
    have ef : E.PairFor false x y ↔ selected a b x y := Iff.rfl
    have et : E.PairFor true x y ↔ selected d e x y := Iff.rfl
    constructor
    · rintro ⟨edge,avoid⟩
      exact ⟨edge,fun h=>avoid ⟨false,ef.mpr h⟩,fun h=>avoid ⟨true,et.mpr h⟩⟩
    · rintro ⟨edge,one,two⟩
      refine ⟨edge,?_⟩
      rintro ⟨slot,h⟩
      cases slot
      · exact one (ef.mp h)
      · exact two (et.mp h)
  have first : ∀ v : V,H.Adj xh (.inl v)↔v=a∨v=b := fun _=>Iff.rfl
  have link : H.Adj xh yh := Bool.false_ne_true
  have ch : ∀ z,H.degree z=3 := E.cubic cub
  have sc : SmallTrivial H := E.preserves_small_trivial cub small
  have cardH : Fintype.card (V⊕Bool)=Fintype.card V+2 := by simp
  have min : 4≤Fintype.card (V⊕Bool) := by
    have two := card_le_univ (s:=({a,b}:Finset V))
    have cnt : 2≤Fintype.card V := by simpa [ab.ne] using two
    omega
  have vc := SquareCap.three_connected_of_small_trivial H ch min sc
  have typed : ∀ x y u v : V⊕Bool,H.Adj x y→H.Adj u v→Remote H x u v→
      FactorOn (omitEdge H u v) ((univ.erase x).erase y) :=
    remote (V⊕Bool) H (by omega) (by omega) ch vc sc
  exact use_remote_promise G H a b d e r s old first link rs
    ⟨ar.symm,br.symm,as.symm,bs.symm⟩ last typed

#print axioms smaller_avoid3_of_remote
end KelmansCactus.AtomicBridge.RemoteAvoid3RankTransfer
