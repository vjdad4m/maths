import MarkedWingSat189
import GraphRup189
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.MarkedWingSat.Core72
open Graffiti189LongestPath.GraphSat
open SimpleGraph
def rules : List (MarkedWingSat.Rule 7) := [
  .degree 0 [1,2,3],
  .degree 0 [1,2,4],
  .degree 0 [1,2,6],
  .degree 0 [1,4,5],
  .degree 0 [1,5,6],
  .degree 1 [0,2,3],
  .degree 1 [0,2,4],
  .degree 1 [0,2,5],
  .degree 1 [0,3,4],
  .degree 1 [0,4,5],
  .degree 3 [0,1,2],
  .degree 3 [0,2,4],
  .degree 3 [0,2,6],
  .degree 3 [1,2,4],
  .degree 3 [1,2,6],
  .degree 3 [2,4,6],
  .degree 4 [0,1,2],
  .degree 4 [0,1,3],
  .degree 4 [0,2,3],
  .degree 4 [0,2,6],
  .degree 4 [1,2,3],
  .degree 4 [1,2,5],
  .degree 4 [1,2,6],
  .degree 4 [2,3,5],
  .degree 4 [2,3,6],
  .degree 5 [0,1,2],
  .degree 5 [0,1,3],
  .degree 5 [0,1,4],
  .degree 5 [0,1,6],
  .degree 5 [0,2,6],
  .degree 5 [1,2,3],
  .degree 5 [1,2,4],
  .degree 5 [1,2,6],
  .degree 5 [2,3,4],
  .degree 5 [2,3,6],
  .degree 5 [2,4,6],
  .degree 5 [3,4,6],
  .degree 6 [0,1,2],
  .degree 6 [0,1,3],
  .degree 6 [0,1,4],
  .degree 6 [0,2,3],
  .degree 6 [0,2,4],
  .degree 6 [0,3,5],
  .degree 6 [1,2,3],
  .degree 6 [1,2,4],
  .degree 6 [2,3,4],
  .degree 6 [2,4,5],
  .degree 6 [3,4,5],
  .route [0,2,6,5,1],
  .route [0,3,4,5,1],
  .route [0,3,5,6,1],
  .route [0,3,6,4,1],
  .route [0,3,6,5,1],
  .route [0,4,3,5,1],
  .route [0,4,5,3,1],
  .route [0,4,5,6,1],
  .route [0,4,6,3,1],
  .route [0,4,6,5,1],
  .route [0,5,2,4,1],
  .route [0,5,2,6,1],
  .route [0,5,3,4,1],
  .route [0,5,3,6,1],
  .route [0,5,4,3,1],
  .route [0,5,4,6,1],
  .route [0,5,6,3,1],
  .route [0,5,6,4,1],
  .route [0,6,3,4,1],
  .route [0,6,3,5,1],
  .route [0,6,4,3,1],
  .route [0,6,4,5,1],
  .route [0,6,5,2,1],
  .route [0,6,5,3,1],
  .route [0,6,5,4,1],
  .route [0,2,5,6,4,1],
  .route [0,2,6,3,5,1],
  .route [0,3,4,6,5,1],
  .route [0,3,6,5,4,1],
  .route [0,4,3,5,6,1],
  .route [0,4,5,3,6,1],
  .route [0,4,5,6,2,1],
  .route [0,4,5,6,3,1],
  .route [0,5,3,6,4,1],
  .route [0,5,4,3,6,1],
  .route [0,5,4,6,3,1],
  .route [0,5,6,4,3,1]
]
graph_rup certificate (include_str "core72.cnf") (include_str "core72.lrat")
theorem fixed {G : SimpleGraph (Fin 7)} [DecidableRel G.Adj]
    (degrees : ∀ i, (if i=2 then 2 else 4)≤G.degree i) :
    ∃ p : G.Walk 0 1,p.IsPath ∧ 4≤p.length := by
  have equality : certificate.formula = rules.map MarkedWingSat.clause := rfl
  have valid : rules.all (fun r => decide (WF 2 0 1 r)) = true := by decide
  have prf := certificate
  rw [equality] at prf
  exact transfer (by decide) 2 0 1 degrees rules
    (fun r hr => of_decide_eq_true (List.all_eq_true.mp valid r hr)) prf
#print axioms fixed
end Graffiti189LongestPath.MarkedWingSat.Core72
