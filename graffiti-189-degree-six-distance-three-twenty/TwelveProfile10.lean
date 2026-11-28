import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile10
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,0,2,2,2,2,2,5,6,6] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 7,
  .forbidden 1 8,
  .forbidden 1 9,
  .degree 1 [0,2,3,10],
  .degree 1 [0,2,3,11],
  .degree 1 [2,3,10,11],
  .forbidden 2 4,
  .forbidden 2 5,
  .forbidden 2 7,
  .forbidden 2 8,
  .forbidden 2 9,
  .degree 2 [0,1,3,10],
  .degree 2 [0,1,3,11],
  .forbidden 3 4,
  .forbidden 3 5,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 9,
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
  .degree 4 [6,7,8,10],
  .cap 4 [1,2,3],
  .degree 5 [6,7,8,10],
  .cap 5 [1,2,3],
  .cap 7 [1,2,3],
  .degree 8 [4,5,6,9],
  .degree 8 [5,6,7,10],
  .cap 8 [1,2,3],
  .degree 9 [4,5,6,7,8],
  .degree 9 [4,5,6,7,10],
  .degree 9 [4,5,6,8,10],
  .degree 9 [4,5,7,8,10],
  .degree 9 [4,6,7,8,10],
  .degree 9 [5,6,7,8,10],
  .degree 9 [6,7,8,10,11],
  .cap 9 [0,1,2,3],
  .cap 9 [1,2,3,4],
  .cap 9 [1,2,3,5],
  .cap 9 [1,2,3,7],
  .cap 9 [1,2,3,8],
  .cap 9 [1,2,3,11],
  .visible 11 true,
  .cap 11 [0,4,5,7,8],
  .lower 0 9 11,
  .lower 0 11 1,
  .lower 1 4 11,
  .lower 1 5 11,
  .lower 1 7 11,
  .lower 1 8 10,
  .lower 1 8 11,
  .lower 1 9 10,
  .lower 1 9 11,
  .lower 2 4 11,
  .lower 2 5 11,
  .lower 2 7 11,
  .lower 2 8 10,
  .lower 2 8 11,
  .lower 2 9 10,
  .lower 2 9 11,
  .lower 3 4 11,
  .lower 3 5 11,
  .lower 3 7 11,
  .lower 3 8 10,
  .lower 3 8 11,
  .lower 3 9 10,
  .lower 3 9 11,
  .lower 4 9 5,
  .lower 4 11 9,
  .lower 5 9 4,
  .lower 5 11 9,
  .lower 7 9 8,
  .lower 7 11 9,
  .lower 8 9 4,
  .lower 8 11 9,
  .lower 9 11 4,
  .lower 9 11 5,
  .lower 9 11 6,
  .lower 9 11 7,
  .lower 9 11 8
]
graph_rup certificate (include_str "twelve-certs/twelve10.cnf") (include_str "twelve-certs/twelve10.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile10
