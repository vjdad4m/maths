import Proof384b
namespace Graffiti384b.OddStars.PairExample
open Finset SimpleGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
def neighborsG : Fin 9 → Finset (Fin 9)
  | 0 => {5,6,7,8}
  | 1 => {5,6,8}
  | 2 => {6,7,8}
  | 3 => {7,8}
  | 4 => {8}
  | 5 => {0,1,7,8}
  | 6 => {0,1,2,7,8}
  | 7 => {0,2,3,5,6,8}
  | 8 => {0,1,2,3,4,5,6,7}

def graphG : SimpleGraph (Fin 9) where
  Adj u v := v∈neighborsG u
  symm := by
    have h : ∀u v : Fin 9, v∈neighborsG u → u∈neighborsG v := by decide
    exact fun _ _ e => h _ _ e
  loopless := by
    have h : ∀v : Fin 9, v∉neighborsG v := by decide
    exact h
instance : DecidableRel graphG.Adj := fun u v => inferInstanceAs (Decidable (v∈neighborsG u))

def neighborsE : Fin 10 → Finset (Fin 10)
  | 0 => {5,6,7,8,9}
  | 1 => {5,6,8,9}
  | 2 => {6,7,8}
  | 3 => {7,8}
  | 4 => {8}
  | 5 => {0,1,7,8}
  | 6 => {0,1,2,7,8}
  | 7 => {0,2,3,5,6,8}
  | 8 => {0,1,2,3,4,5,6,7}
  | 9 => {0,1}

def graphE : SimpleGraph (Fin 10) where
  Adj u v := v∈neighborsE u
  symm := by
    have h : ∀u v : Fin 10, v∈neighborsE u → u∈neighborsE v := by decide
    exact fun _ _ e => h _ _ e
  loopless := by
    have h : ∀v : Fin 10, v∉neighborsE v := by decide
    exact h
instance : DecidableRel graphE.Adj := fun u v => inferInstanceAs (Decidable (v∈neighborsE u))

theorem attachment : (∀i j : Fin 9, graphE.Adj i.castSucc j.castSucc ↔ graphG.Adj i j) ∧
    graphE.neighborFinset 9={0,1} ∧ ¬graphG.Adj 0 1 := by decide

theorem scores : List.ofFn (trianglesAt graphG)=[5,2,3,1,0,4,6,8,10] ∧
    List.ofFn (trianglesAt graphE)=[5,2,3,1,0,4,6,8,10,0] ∧
    graphG.degree 4=1 ∧ bound graphG=4 ∧ bound graphE=5 := by decide

theorem connected : graphG.Connected := by
  apply (connected_iff_exists_forall_reachable graphG).mpr
  refine ⟨8,fun v => ?_⟩
  have star : ∀v : Fin 9, v=8 ∨ graphG.Adj 8 v := by decide
  rcases star v with rfl | edge
  · exact Reachable.refl _
  · exact edge.reachable

private def small {n : ℕ} (J : SimpleGraph (Fin n)) [DecidableRel J.Adj] :=
  (univ : Finset (Fin n)).powerset.filter (fun S => S.card≤4 ∧ ∀v, v∉S → 2≤nbr J v S)

theorem original_sets : small graphG={{1,4,7,8},{4,5,7,8},{4,6,7,8}} := by decide
theorem extended_sets : small graphE={{4,7,8,9}} := by decide

theorem optimum : gamma graphG=4 ∧ gamma graphE=4 := by
  have min_eq {n : ℕ} (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
      (exists4 : ∃S, TwoDominates J S ∧ S.card=4)
      (all4 : ∀S∈small J,S.card=4) : gamma J=4 := by
    apply le_antisymm (Nat.sInf_le exists4)
    apply le_csInf ⟨4,exists4⟩
    rintro k ⟨S,dom,rfl⟩
    by_contra! lt
    have h := all4 S (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),lt.le,dom⟩)
    omega
  constructor
  · apply min_eq _ ⟨{1,4,7,8},(by decide : ∀v : Fin 9, v∉({1,4,7,8}:Finset (Fin 9)) → 2≤nbr graphG v {1,4,7,8}),by decide⟩
    rw [original_sets]
    decide
  · apply min_eq _ ⟨{4,7,8,9},(by decide : ∀v : Fin 10, v∉({4,7,8,9}:Finset (Fin 10)) → 2≤nbr graphE v {4,7,8,9}),by decide⟩
    rw [extended_sets]
    decide

theorem no_joint_optimum : ∀S : Finset (Fin 9), TwoDominates graphG S → S.card=gamma graphG →
    ¬(0∈S ∧ 1∈S) := by
  intro S dom size
  have mem : S∈small graphG := mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), by rw [size,optimum.1],dom⟩
  have avoid : ∀U∈({{1,4,7,8},{4,5,7,8},{4,6,7,8}} : Finset (Finset (Fin 9))), ¬(0∈U ∧ 1∈U) := by decide
  exact avoid S (original_sets ▸ mem)

theorem failed_restriction : nbr graphG 1 {4,7,8}=1 ∧ 1∉({4,7,8}:Finset (Fin 9)) := by decide
end Graffiti384b.OddStars.PairExample
#print axioms Graffiti384b.OddStars.PairExample.attachment
#print axioms Graffiti384b.OddStars.PairExample.scores
#print axioms Graffiti384b.OddStars.PairExample.connected
#print axioms Graffiti384b.OddStars.PairExample.optimum
#print axioms Graffiti384b.OddStars.PairExample.original_sets
#print axioms Graffiti384b.OddStars.PairExample.extended_sets
#print axioms Graffiti384b.OddStars.PairExample.no_joint_optimum
#print axioms Graffiti384b.OddStars.PairExample.failed_restriction
