import RemoteRungLadder
import RemoteSpacedPrismWidth
import PrismCore

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteLadderPrismDomain
open RemoteSubdivisionCore (Marks)
open RemoteSpacedPrismHandle (Port Host V4 pole endThird embed)
open SquareCap (HasFactor SmallTrivial ThreeConnected NontrivialSide boundary)
variable {n : ℕ} (hm : 6≤n) (M : Marks (Prism.core n hm) Port)

theorem any_six_rungs_factor (div : 3∣n)
    (rungs : ∀ i,(M.a i).1=(M.b i).1) : HasFactor M.expanded := by
  apply RemoteRungLadder.factor_of_any_rung_subdivisions M
  · intro c
    exact Or.inr ⟨rfl,by change false≠true; decide⟩
  · intro j hj b
    exact Or.inl ⟨rfl,Or.inl (Nat.mod_eq_of_lt hj)⟩
  · exact rungs
  · rw [show Fintype.card Port=6 by decide]
    obtain ⟨k,hk⟩ := div
    exact ⟨2*k+2,by omega⟩

theorem genuine_remote_ladder (div : 3∣n) (rungs : ∀ i,(M.a i).1=(M.b i).1) :
    HasFactor M.expanded ∧
    SmallTrivial (Host M) ∧ ThreeConnected (Host M) ∧ Fintype.card (V4 (Fin n×Bool))%6=2 ∧
    (Host M).Adj (pole false) (pole true) ∧
    (Host M).Adj (endThird false) (endThird true) ∧
    RemoteT2Scope.Remote (Host M) (pole false) (endThird false) (endThird true) ∧
    (∀ x y : (Fin n×Bool)⊕Port, M.expanded.Adj x y ↔
      (RemoteT2CompletionTransfer.eraseEdge (Host M) (endThird false) (endThird true)).Adj
        (embed x) (embed y)) ∧
    ∀ (c : ((Fin n×Bool)⊕Port)→Bool), (∀ b,NontrivialSide c b) →
      3≤(boundary M.expanded c).card := by
  have cub (v : Fin n×Bool) : (Prism.core n hm).degree v=3 := Prism.core_cubic n hm v
  have cyc : SmallTrivial (Prism.core n hm) := Prism.core_small n hm
  have hos := RemoteSpacedPrismHandle.small_trivial M cub cyc
  have size : Fintype.card (V4 (Fin n×Bool))=2*n+8 := by
    rw [RemoteSpacedPrismHandle.order_card]
    simp [Fintype.card_prod,Nat.mul_comm]
  have nontriv : 4≤Fintype.card (V4 (Fin n×Bool)) := by omega
  have mod6 : Fintype.card (V4 (Fin n×Bool))%6=2 := by
    rw [size]
    obtain ⟨k,hk⟩ := div
    omega
  exact ⟨any_six_rungs_factor hm M div rungs, hos,
    SquareCap.three_connected_of_small_trivial _ (RemoteSpacedPrismHandle.cubic M cub) nontriv hos,
    mod6, RemoteSpacedPrismHandle.pole_join M,RemoteSpacedPrismHandle.remote_edge M,
    RemoteSpacedPrismHandle.remote M,RemoteSpacedPrismHandle.exact_survivor M,
    RemoteSpacedPrismWidth.expanded_wide M cub cyc⟩

#print axioms any_six_rungs_factor
#print axioms genuine_remote_ladder
end KelmansCactus.AtomicBridge.RemoteLadderPrismDomain
