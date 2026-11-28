import MarkedWingSat189
import GraphRup189
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.MarkedWingSat.Core60
open Graffiti189LongestPath.GraphSat
open SimpleGraph
def rules : List (MarkedWingSat.Rule 6) := [
  .degree 0 [1],
  .degree 1 [0,2,3],
  .degree 3 [0,1,2],
  .degree 3 [0,2,4],
  .degree 3 [0,2,5],
  .degree 3 [2,4,5],
  .degree 4 [0,1,2],
  .degree 4 [0,2,3],
  .degree 4 [1,2,5],
  .degree 4 [1,3,5],
  .degree 5 [0,1,2],
  .degree 5 [1,2,3],
  .degree 5 [1,2,4],
  .degree 5 [2,3,4],
  .route [0,2,4,5,1],
  .route [0,3,4,5,1],
  .route [0,4,3,5,1],
  .route [0,4,5,3,1],
  .route [0,5,3,4,1],
  .route [0,5,4,3,1]
]
graph_rup certificate (include_str "core60.cnf") (include_str "core60.lrat")
theorem fixed {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (degrees : ∀ i, (if i=0 then 2 else 4)≤G.degree i) :
    ∃ p : G.Walk 0 1,p.IsPath ∧ 4≤p.length := by
  have equality : certificate.formula = rules.map MarkedWingSat.clause := rfl
  have valid : rules.all (fun r => decide (WF 0 0 1 r)) = true := by decide
  have prf := certificate
  rw [equality] at prf
  exact transfer (by decide) 0 0 1 degrees rules
    (fun r hr => of_decide_eq_true (List.all_eq_true.mp valid r hr)) prf
#print axioms fixed
end Graffiti189LongestPath.MarkedWingSat.Core60
