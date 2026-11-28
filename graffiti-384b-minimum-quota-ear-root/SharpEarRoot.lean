import RootedMinimumQuota
namespace Graffiti384b.EarRooted.Example
open Finset SimpleGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Move the leaf 4 of the published PairExample graph from 8 to its unique score-one vertex 3. -/
def neighbors : Fin 9 → Finset (Fin 9)
  | 0 => {5,6,7,8}
  | 1 => {5,6,8}
  | 2 => {6,7,8}
  | 3 => {4,7,8}
  | 4 => {3}
  | 5 => {0,1,7,8}
  | 6 => {0,1,2,7,8}
  | 7 => {0,2,3,5,6,8}
  | 8 => {0,1,2,3,5,6,7}

def graph : SimpleGraph (Fin 9) where
  Adj u v := v∈neighbors u
  symm := fun _ _ h => (show ∀u v : Fin 9,v∈neighbors u → u∈neighbors v by decide) _ _ h
  loopless := (show ∀v : Fin 9,v∉neighbors v by decide)
instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v∈neighbors u))

theorem profile : (nonleaves graph).card=8 ∧ (types graph).card=9 ∧
    List.ofFn (trianglesAt graph)=[5,2,3,1,0,4,6,8,10] ∧ graph.degree 4=1 ∧ graph.Adj 3 4 ∧
    bound graph=4 := by decide

theorem connected : graph.Connected := by
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨8,fun v => ?_⟩
  have all : ∀v : Fin 9,v=8 ∨ graph.Adj 8 v ∨ (graph.Adj 8 3 ∧ graph.Adj 3 v) := by decide
  rcases all v with rfl|h|⟨h,k⟩
  · exact Reachable.refl _
  · exact h.reachable
  · exact h.reachable.trans k.reachable

theorem sharp : gamma graph=4 := by
  have dom : TwoDominates graph ({0,4,6,8}:Finset (Fin 9)) :=
    (by decide : ∀v : Fin 9,v∉({0,4,6,8}:Finset (Fin 9)) → 2≤nbr graph v {0,4,6,8})
  have ex : ∃D : Finset (Fin 9),TwoDominates graph D ∧ D.card=4 := ⟨_,dom,by decide⟩
  apply le_antisymm (Nat.sInf_le ex) (le_csInf ⟨4,ex⟩ ?_)
  rintro k ⟨D,good,rfl⟩
  by_contra! small
  have empty : (univ : Finset (Fin 9)).powerset.filter
      (fun S => S.card<4 ∧ ∀v,v∉S → 2≤nbr graph v S)=∅ := by decide
  have mem : D ∈ (univ : Finset (Fin 9)).powerset.filter
      (fun S => S.card<4 ∧ ∀v,v∉S → 2≤nbr graph v S) :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ D),small,good⟩
  exact not_mem_empty _ (empty ▸ mem)

end Graffiti384b.EarRooted.Example
#print axioms Graffiti384b.EarRooted.Example.profile
#print axioms Graffiti384b.EarRooted.Example.connected
#print axioms Graffiti384b.EarRooted.Example.sharp
