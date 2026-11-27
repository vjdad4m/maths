import RemoteSixSwitch
import RemoteSquareSingleSlot

namespace KelmansCactus.AtomicBridge.RemoteSquareThenSix
open SimpleGraph
open scoped Sym2
open RemoteSquareConvergence RemoteSixSwitch
open RemoteSquareRankFactor (TwoRegular)
open RemoteSquareSingleSlot (old factor_connected_one_slot)
open SquareCap (HasFactor)
variable {V I : Type*}

def Ready (h : Six V) (K X : SimpleGraph V) : Prop :=
  (K.Reachable h.a h.b ∧ K.Reachable h.c h.d ∧ K.Reachable h.e h.f) ∨
  (X.Reachable h.a h.c ∧ ¬X.Reachable h.a h.e ∧
    (X.deleteEdges {s(h.a,h.b)}).Reachable h.a h.b ∧
    (X.deleteEdges {s(h.e,h.f)}).Reachable h.e h.f ∧
    (K.Reachable h.c h.d ∨ K.Reachable h.a h.c ∨ K.Reachable h.b h.d))

theorem ready_preserves {h : Six V} {K X Y : SimpleGraph V}
    (g : Realization h K X Y) (ok : Ready h K X) :
    ∀ x y,X.Reachable x y → Y.Reachable x y := by
  rcases ok with ⟨ab,cd,ef⟩|⟨join,split,wAB,wEF,ports⟩
  · exact all_bypasses_preserve_reach g ab cd ef
  · exact (merge_preserves_reach g join split wAB wEF ports).1

theorem lift_realization {h : Six V} {K B C : SimpleGraph V} (g : Realization h K B C)
    (gates : I→Quad V) (s : I→Bool) :
    Realization h (network K gates s) (network B gates s) (network C gates s) := by
  refine ⟨fun x y=>?_,fun x y=>?_⟩
  · change (B.Adj x y ∨ _) ↔ (K.Adj x y ∨ _) ∨ h.old x y
    rw [g.1]
    tauto
  · change (C.Adj x y ∨ _) ↔ (K.Adj x y ∨ _) ∨ h.new x y
    rw [g.2]
    tauto

/-- Exhaust binary square choices on one side of a designated six-switch.
A safe crossing six-switch after this exhaustion reaches the exact union
connectivity of both sides without going back to search alternative squares. -/
theorem square_then_six [Fintype V] [DecidableEq I]
    (h : Six V) {K B C : SimpleGraph V} (g : Realization h K B C)
    (gates : I→Quad V) (bypass : CanBypass B gates)
    (safe : ∀ s, (∀ x y,(network B gates s).Reachable x y ↔
                            (unionNetwork B gates).Reachable x y) →
      (∃ x y, (unionNetwork C gates).Adj x y ∧ ¬ (network B gates s).Reachable x y) →
        Ready h (network K gates s) (network B gates s))
    (start : I→Bool) :
    ∃ s : I→Bool, ∃ flag : Bool,
      ∀ x y,(network (if flag then C else B) gates s).Reachable x y ↔
        (unionNetwork B gates ⊔ unionNetwork C gates).Reachable x y := by
  classical
  obtain ⟨s,_,done⟩ := square_convergence B gates bypass start
  by_cases yes : ∀ x y,(unionNetwork C gates).Adj x y → (network B gates s).Reachable x y
  · refine ⟨s,false,fun x y=>⟨fun p=>p.mono (le_trans (network_le_union B gates s) le_sup_left),?_⟩⟩
    apply lift_reach
    intro u v e
    rcases e with l|r
    · exact (done _ _).mpr l.reachable
    · exact yes _ _ r
  · push_neg at yes
    have keep := ready_preserves (lift_realization g gates s) (safe s done yes)
    refine ⟨s,true,fun x y=>⟨fun p=>p.mono (le_trans (network_le_union C gates s) le_sup_right),?_⟩⟩
    apply lift_reach
    intro u v e
    rcases e with l|⟨r|⟨i,b,r⟩⟩
    · exact keep _ _ ((done _ _).mpr l.reachable)
    · rcases (g.2 _ _).mp r with edge|added
      · have oldEdge : (unionNetwork B gates).Adj u v := Or.inl (g.base_le_old edge)
        exact keep _ _ ((done _ _).mpr oldEdge.reachable)
      · apply SimpleGraph.Adj.reachable (G:=network C gates s)
        exact Or.inl ((g.2 _ _).mpr (Or.inr added))
    · have oldEdge : (unionNetwork B gates).Adj u v := Or.inr ⟨i,b,r⟩
      exact keep _ _ ((done _ _).mpr oldEdge.reachable)

/-- One extra controlled six-switch is permitted in the actual one-omitted
slot factor criterion. The exact safety input is a residual six-port test. -/
theorem square_then_six_one_slot [Fintype V] [DecidableEq V] [DecidableEq I]
    (h : Six (Option V)) {K B C : SimpleGraph (Option V)} (g : Realization h K B C)
    (gates : I→Quad (Option V)) (bypass : CanBypass B gates)
    (safe : ∀ s, (∀ x y,(network B gates s).Reachable x y ↔
                            (unionNetwork B gates).Reachable x y) →
      (∃ x y, (unionNetwork C gates).Adj x y ∧ ¬(network B gates s).Reachable x y) →
        Ready h (network K gates s) (network B gates s))
    (G : SimpleGraph (Option V)) (a b : V)
    (sub : unionNetwork B gates ⊔ unionNetwork C gates ≤ G)
    (reg : ∀ (j : Bool) s, TwoRegular (old (network (if j then C else B) gates s)))
    (slot : ∀ (j : Bool) s v, (network (if j then C else B) gates s).Adj none (some v) ↔ v=a ∨ v=b)
    (con : (unionNetwork B gates ⊔ unionNetwork C gates).Preconnected)
    (size : 3∣Fintype.card (Option V)) (start : I→Bool) :
    ∃ (s : I→Bool) (j : Bool), HasFactor (network (if j then C else B) gates s) ∧ HasFactor G := by
  obtain ⟨s,j,done⟩ := square_then_six h g gates bypass safe start
  let X := network (if j then C else B) gates s
  have hX : HasFactor X :=
    factor_connected_one_slot _ a b (slot j s) (reg j s) (fun x y=>(done x y).mpr (con x y)) size
  have subX : X≤G := by
    cases j
    · exact le_trans (network_le_union B gates s) (le_trans le_sup_left sub)
    · exact le_trans (network_le_union C gates s) (le_trans le_sup_right sub)
  obtain ⟨pack,legal,apart,covers⟩ := hX
  exact ⟨s,j,⟨pack,legal,apart,covers⟩,pack,fun R m=>by
    obtain ⟨ct,c,cm,adjs⟩ := legal R m
    exact ⟨ct,c,cm,fun x xm ne=>subX (adjs x xm ne)⟩,apart,covers⟩

#print axioms square_then_six
#print axioms square_then_six_one_slot
end KelmansCactus.AtomicBridge.RemoteSquareThenSix
