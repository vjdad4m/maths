import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile33
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,3,6,6] : Array (Fin 8))[i.val]!,some 10⟩
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
  .degree 4 [2,9,10,11],
  .cap 4 [0,1,5],
  .cap 4 [2,5,8],
  .degree 9 [4,5,6,7],
  .degree 9 [4,5,6,8],
  .degree 9 [4,5,7,8],
  .degree 9 [4,6,7,8],
  .cap 9 [0,2,3],
  .cap 9 [0,2,10],
  .cap 9 [1,2,3],
  .cap 9 [1,2,10],
  .cap 9 [2,3,5],
  .visible 10 true,
  .same 0 4 false,
  .lower 0 9 4,
  .same 1 4 false,
  .lower 1 9 4,
  .same 2 4 false,
  .lower 2 9 4,
  .lower 2 9 10,
  .lower 2 9 11,
  .lower 3 9 4,
  .lower 3 9 10,
  .lower 3 9 11,
  .lower 4 5 9,
  .lower 4 8 9,
  .same 5 9 true,
  .lower 9 10 5,
  .lower 9 10 6,
  .lower 9 10 7,
  .lower 9 10 8
]
graph_rup certificate (include_str "twelve-certs/twelve33.cnf") (include_str "twelve-certs/twelve33.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile33
