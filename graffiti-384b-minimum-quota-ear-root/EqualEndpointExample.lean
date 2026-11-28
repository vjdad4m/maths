import PrescribedEdge
namespace Graffiti384b.EarRooted.EqualEndpoints
open Finset SimpleGraph Exterior
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Attach a triangle on 8,10,11 to the ten-vertex published rich-core example. -/
def neighbors : Fin 12 → Finset (Fin 12)
  | 0 => {1,8,9}
  | 1 => {0,3,5,6,7,8,9}
  | 2 => {4,6,7,8,9}
  | 3 => {1,7,8,9}
  | 4 => {2,5,6,7,8,9}
  | 5 => {1,4,8}
  | 6 => {1,2,4,9}
  | 7 => {1,2,3,4,8}
  | 8 => {0,1,2,3,4,5,7,9,10,11}
  | 9 => {0,1,2,3,4,6,8}
  | 10 => {8,11}
  | 11 => {8,10}

def graph : SimpleGraph (Fin 12) where
  Adj u v := v∈neighbors u
  symm := fun _ _ h => (show ∀u v : Fin 12,v∈neighbors u → u∈neighbors v by decide) _ _ h
  loopless := (show ∀v : Fin 12,v∉neighbors v by decide)
instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v∈neighbors u))

theorem profile : graph.Adj 10 11 ∧
    List.ofFn (trianglesAt graph)=[3,9,7,5,8,2,4,6,15,11,1,1] := by decide

/-- Opposite colors on 10 and 11 would force their common neighbor 8 onto both shores. -/
theorem cannot_separate : ¬∃P Q : Finset (Fin 12),10∈P ∧ 11∈Q ∧ Protected graph P Q := by
  rintro ⟨P,Q,l,r,apart,lp,rq⟩
  have need {v w : Fin 12} {S : Finset (Fin 12)} (shape : graph.neighborFinset v={8,w})
      (two : 2≤nbr graph v S) : 8∈S := by
    by_contra out
    have sub : S.filter (graph.Adj v)⊆{w} := by
      intro x xm
      obtain ⟨xs,adj⟩ := mem_filter.mp xm
      have neigh := (graph.mem_neighborFinset ..).mpr adj
      rw [shape,mem_insert,mem_singleton] at neigh
      exact mem_singleton.mpr (neigh.resolve_left (fun eq => out (eq ▸ xs)))
    have le := card_le_card sub
    rw [card_singleton] at le
    change 2≤(S.filter (graph.Adj v)).card at two; omega
  exact disjoint_left.mp apart (need (w:=10) (by decide) (rq 11 r)) (need (w:=11) (by decide) (lp 10 l))

end Graffiti384b.EarRooted.EqualEndpoints
#print axioms Graffiti384b.EarRooted.EqualEndpoints.profile
#print axioms Graffiti384b.EarRooted.EqualEndpoints.cannot_separate
