import LeafCritical
import IsolateBasic384b
import Mathlib.Combinatorics.SimpleGraph.Clique
namespace Graffiti384b.OddStars.UpperExample
open Finset SimpleGraph LeafCritical
open private Graffiti384b.cut from Proof384b
open private IsolateBasic.minimum from IsolateBasic384b
set_option maxRecDepth 65536
set_option maxHeartbeats 50000000
abbrev V := Fin 10
def neighbors : V → Finset V
  | 0 => {1,8,9}
  | 1 => {0,3,5,6,7,8,9}
  | 2 => {4,6,7,8,9}
  | 3 => {1,7,8,9}
  | 4 => {2,5,6,7,8,9}
  | 5 => {1,4,8}
  | 6 => {1,2,4,9}
  | 7 => {1,2,3,4,8}
  | 8 => {0,1,2,3,4,5,7,9}
  | 9 => {0,1,2,3,4,6,8}

def graph : SimpleGraph V where
  Adj u v := v∈neighbors u
  symm := by
    have h : ∀u v : V,v∈neighbors u → u∈neighbors v := by decide
    exact fun _ _ e => h _ _ e
  loopless := by
    have h : ∀v : V,v∉neighbors v := by decide
    exact h
instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v∈neighbors u))

def A : Finset V := {0,1,2,3,4}
theorem scores : List.ofFn (trianglesAt graph)=[3,9,7,5,8,2,4,6,14,11] := by decide
theorem supported : ∀u v,graph.Adj u v → ∃w,graph.Adj u w ∧ graph.Adj v w := by decide
theorem cubic : univ.filter (fun u : V => graph.degree u=3)={0,5} ∧ ¬graph.Adj 0 5 := by decide
theorem connected : graph.Connected := by
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨8,fun v => ?_⟩
  have dist : ∀v : V,v=8 ∨ graph.Adj 8 v ∨ ∃w,graph.Adj 8 w ∧ graph.Adj w v := by decide
  rcases dist v with rfl|e|⟨w,f,g⟩
  · exact Reachable.refl _
  · exact e.reachable
  · exact f.reachable.trans g.reachable
theorem five_free : ∀C,¬graph.IsNClique 5 C := by
  have census : ((univ : Finset V).powersetCard 5).filter
    (fun C => ∀u∈C,∀v∈C,u≠v → graph.Adj u v)=∅ := by decide
  intro C cl
  exact not_mem_empty C (census ▸ mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,cl.2⟩,cl.1⟩)

private theorem cut_census :
    ∀S : Finset V,Graffiti384b.cut graph S Sᶜ≤19 ∧
      (Graffiti384b.cut graph S Sᶜ=19 ↔ S=A ∨ S=Aᶜ) := by decide

theorem maximum_cuts (S : Finset V) : Maximum graph S ↔ S=A ∨ S=Aᶜ := by
  have val : Graffiti384b.cut graph A Aᶜ=19 := (cut_census A).2.mpr (Or.inl rfl)
  constructor
  · intro m; exact (cut_census S).2.mp (le_antisymm (cut_census S).1 (val ▸ m A))
  · intro choice; intro T; exact ((cut_census S).2.mpr choice) ▸ (cut_census T).1

theorem critical_all {S : Finset V} (mx : Maximum graph S) : critical graph S={0,5} := by
  rcases (maximum_cuts S).mp mx with rfl|rfl <;> decide

theorem domination : gamma graph=3 := by
  obtain ⟨D,dom,size⟩ := IsolateBasic.minimum graph
  have upper : gamma graph≤3 := Nat.sInf_le (s:={k : ℕ | ∃D,TwoDominates graph D ∧ D.card=k})
    ⟨{1,2,8},(by decide : ∀v : V,v∉({1,2,8}:Finset V) → 2≤nbr graph v {1,2,8}),by decide⟩
  have census : ((univ : Finset V).powerset.filter
    (fun S => S.card≤2 ∧ ∀v∉S,2≤nbr graph v S))=∅ := by decide
  have large : ¬D.card≤2 := by
    intro small
    exact not_mem_empty D (census ▸ mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),small,dom⟩)
  omega
end Graffiti384b.OddStars.UpperExample
#print axioms Graffiti384b.OddStars.UpperExample.scores
#print axioms Graffiti384b.OddStars.UpperExample.supported
#print axioms Graffiti384b.OddStars.UpperExample.cubic
#print axioms Graffiti384b.OddStars.UpperExample.connected
#print axioms Graffiti384b.OddStars.UpperExample.five_free
#print axioms Graffiti384b.OddStars.UpperExample.maximum_cuts
#print axioms Graffiti384b.OddStars.UpperExample.critical_all
#print axioms Graffiti384b.OddStars.UpperExample.domination
