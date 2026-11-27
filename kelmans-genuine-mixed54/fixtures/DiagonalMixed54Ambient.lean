import DiagonalMixed54Core
import RemoteGapRunPacking
set_option maxHeartbeats 0

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (HasFactor FactorOn)
open RemoteGapRunPacking (run_factor biUnion_factor)

private def tilePath (i : Fin 18) : List Board :=
  route ([[1,0,48],[3,2,8],[5,6,7],[4,39,44],[47,40,53],[9,10,11],[45,37,52],[38,41,42],[30,51,46],[24,25,50],[13,12,15],[14,17,16],[43,36,49],[18,19,20],[21,22,23],[26,27,28],[29,34,33],[31,32,35]] : List (List Nat))[i.val]!

set_option maxRecDepth 15000 in
theorem ambient_factor : HasFactor board := by
  have paths : ∀ i : Fin 18,(tilePath i).Nodup ∧
      (tilePath i).Chain' board.Adj ∧ 3 ∣ (tilePath i).length := by decide
  have apart : ∀ i j : Fin 18,i≠j →
      Disjoint (tilePath i).toFinset (tilePath j).toFinset := by decide
  have cover : (univ : Finset (Fin 18)).biUnion (fun i=>(tilePath i).toFinset)=univ := by decide
  change FactorOn board univ
  rw [←cover]
  exact biUnion_factor _ _ (fun i _=>run_factor _ (paths i).1 (paths i).2.1 (paths i).2.2)
    (fun i _ j _ ne=>apart i j ne)

#print axioms ambient_factor
end KelmansCactus.AtomicBridge.DiagonalMixed54
