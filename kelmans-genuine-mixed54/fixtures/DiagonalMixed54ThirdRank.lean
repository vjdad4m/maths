import DiagonalMixed54Core
import RemoteGapRunPacking
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (HasFactor FactorOn)
open RemoteSpacedPrismHandle (Port)
open RemoteGapRunPacking (run_factor biUnion_factor)
set_option maxHeartbeats 0
set_option maxRecDepth 12000

def otherMate (v : Core) : Core := ([1,0,3,2,5,4,40,8,7,10,9,12,11,14,13,16,15,18,17,20,19,22,21,26,25,24,23,36,29,28,31,30,35,34,33,32,27,45,41,44,6,38,43,42,39,37,47,46] : List Core)[v.val]!
theorem other_involutive : Function.Involutive otherMate := by
  intro v
  fin_cases v <;> decide
theorem other_adjacent (v : Core) : core.Adj v (otherMate v) := by fin_cases v <;> decide
theorem other_no_charge : ∀ i : Port, otherMate (a i)≠b i := by decide

def otherRank : SimpleGraph Board where
  Adj x y := board.Adj x y ∧ match x,y with
    | .inl u,.inl v => otherMate u≠v
    | _,_ => True
  symm := by
    rintro (x|i) (y|j) h
    · exact ⟨h.1.symm,fun e=>h.2 (by rw [←e,other_involutive])⟩
    all_goals exact ⟨h.1.symm,trivial⟩
  loopless x h := board.loopless x h.1
instance : DecidableRel otherRank.Adj := by
  rintro (x|i) (y|j)
  all_goals change Decidable (_ ∧ _)
  all_goals infer_instance

private def routeOther (i : Fin 18) := route ([[35,0,48],[2,8,9],[1,7,6],[5,38,52],[30,29,34],[4,3,37],[39,53,40],[32,33,47],[27,28,31],[26,25,50],[20,44,45],[21,24,23],[18,19,22],[43,36,49],[14,17,16],[13,12,15],[10,11,41],[42,46,51]] : List (List Nat))[i.val]!
theorem other_rank_factors : HasFactor otherRank := by
  have each (i : Fin 18) : (routeOther i).Nodup ∧ (routeOther i).Chain' otherRank.Adj ∧
       3 ∣ (routeOther i).length := by fin_cases i <;> decide
  have apart : ∀ i j : Fin 18,i≠j →
      Disjoint (routeOther i).toFinset (routeOther j).toFinset := by decide
  have cover : (univ : Finset (Fin 18)).biUnion (fun i=>(routeOther i).toFinset)=univ := by decide
  change FactorOn otherRank univ
  rw [←cover]
  exact biUnion_factor _ _ (fun i _=>run_factor _ (each i).1 (each i).2.1 (each i).2.2)
    (fun i _ j _ ne=>apart i j ne)

#print axioms other_involutive
#print axioms other_no_charge
#print axioms other_rank_factors
end KelmansCactus.AtomicBridge.DiagonalMixed54
