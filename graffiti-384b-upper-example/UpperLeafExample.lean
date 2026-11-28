import UpperExample
namespace Graffiti384b.OddStars.UpperExample
open Finset SimpleGraph
open private IsolateBasic.minimum from IsolateBasic384b
set_option maxHeartbeats 50000000
set_option maxRecDepth 65536
/-- Adjoin a single leaf at the score-three cubic. -/
def leafNeighbors : Fin 11 → Finset (Fin 11)
  | 0 => {1,8,9,10}
  | 1 => {0,3,5,6,7,8,9}
  | 2 => {4,6,7,8,9}
  | 3 => {1,7,8,9}
  | 4 => {2,5,6,7,8,9}
  | 5 => {1,4,8}
  | 6 => {1,2,4,9}
  | 7 => {1,2,3,4,8}
  | 8 => {0,1,2,3,4,5,7,9}
  | 9 => {0,1,2,3,4,6,8}
  | 10 => {0}
def leafGraph : SimpleGraph (Fin 11) where
  Adj u v := v∈leafNeighbors u
  symm := by
    have h : ∀u v : Fin 11,v∈leafNeighbors u → u∈leafNeighbors v := by decide
    exact fun _ _ e => h _ _ e
  loopless := by
    have h : ∀u : Fin 11,u∉leafNeighbors u := by decide
    exact h
instance : DecidableRel leafGraph.Adj := fun u v => inferInstanceAs (Decidable (v∈leafNeighbors u))

theorem leaf_scores : List.ofFn (trianglesAt leafGraph)=[3,9,7,5,8,2,4,6,14,11,0] ∧
    (types leafGraph).card=11 ∧ leafGraph.neighborFinset 10={0} ∧ bound leafGraph=5 := by decide

theorem leaf_skeleton : (∀u v : Fin 10, (patch leafGraph ∅).Adj u.castSucc v.castSucc ↔ graph.Adj u v) ∧
    (patch leafGraph ∅).neighborFinset 10=∅ ∧ (high (patch leafGraph ∅)).card=10 := by decide

theorem leaf_connected : leafGraph.Connected := by
  apply (connected_iff_exists_forall_reachable leafGraph).mpr
  refine ⟨8,fun v => ?_⟩
  have dist : ∀v : Fin 11,v=8 ∨ leafGraph.Adj 8 v ∨ ∃w,leafGraph.Adj 8 w ∧ leafGraph.Adj w v := by decide
  rcases dist v with rfl|e|⟨w,f,g⟩
  · exact Reachable.refl _
  · exact e.reachable
  · exact f.reachable.trans g.reachable

theorem leaf_optimum : gamma leafGraph=4 := by
  obtain ⟨D,dom,size⟩ := IsolateBasic.minimum leafGraph
  have up : gamma leafGraph≤4 := Nat.sInf_le (s:={k : ℕ | ∃D,TwoDominates leafGraph D ∧ D.card=k})
    ⟨{1,4,7,10},(by decide : ∀v : Fin 11,v∉({1,4,7,10}:Finset (Fin 11)) → 2≤nbr leafGraph v {1,4,7,10}),by decide⟩
  have census : ((univ : Finset (Fin 11)).powerset.filter
    (fun S => S.card≤3 ∧ ∀v∉S,2≤nbr leafGraph v S))=∅ := by decide
  have large : ¬D.card≤3 := by
    intro small
    exact not_mem_empty D (census ▸ mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),small,dom⟩)
  omega

theorem unbalanced_core_cut : ∃S : Finset V, S.card=3 ∧ TwoDominates graph S ∧ TwoDominates graph Sᶜ := by
  refine ⟨{1,2,8},by decide,?_,?_⟩ <;> unfold TwoDominates <;> decide

end Graffiti384b.OddStars.UpperExample
#print axioms Graffiti384b.OddStars.UpperExample.leaf_scores
#print axioms Graffiti384b.OddStars.UpperExample.leaf_skeleton
#print axioms Graffiti384b.OddStars.UpperExample.leaf_connected
#print axioms Graffiti384b.OddStars.UpperExample.leaf_optimum

#print axioms Graffiti384b.OddStars.UpperExample.unbalanced_core_cut
