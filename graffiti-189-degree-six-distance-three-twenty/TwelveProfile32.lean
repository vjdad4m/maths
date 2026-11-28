import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile32
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,3,6,6] : Array (Fin 8))[i.val]!,some 9⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 1 9,
  .forbidden 2 9,
  .degree 2 [0,1,3,10],
  .degree 2 [0,1,3,11],
  .forbidden 3 9,
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .visible 4 true,
  .degree 4 [0,1,2,9],
  .degree 4 [0,1,3,9],
  .degree 4 [0,1,9,11],
  .degree 4 [0,2,9,10],
  .degree 4 [0,3,9,10],
  .degree 4 [1,2,9,10],
  .degree 4 [1,2,9,11],
  .degree 4 [1,3,9,10],
  .degree 4 [1,9,10,11],
  .degree 4 [3,9,10,11],
  .cap 4 [0,1,5],
  .cap 9 [0,1,10],
  .cap 9 [0,2,3],
  .cap 9 [0,2,11],
  .cap 9 [0,3,11],
  .cap 9 [0,10,11],
  .cap 9 [1,2,3],
  .cap 9 [1,3,11],
  .cap 9 [2,3,5],
  .cap 9 [2,3,11],
  .cap 9 [2,10,11],
  .cap 9 [3,10,11],
  .same 0 4 false,
  .lower 0 9 4,
  .same 1 4 false,
  .lower 1 9 4,
  .lower 2 9 4,
  .lower 2 9 10,
  .lower 2 9 11,
  .lower 3 9 4,
  .lower 3 9 10,
  .lower 3 9 11,
  .lower 4 5 9,
  .same 5 9 true,
  .lower 9 10 4,
  .lower 9 11 4
]
graph_rup certificate (include_str "twelve-certs/twelve32.cnf") (include_str "twelve-certs/twelve32.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile32
