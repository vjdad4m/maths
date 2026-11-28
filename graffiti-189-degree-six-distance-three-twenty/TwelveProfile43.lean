import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile43
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,0,2,2,2,2,4,6,6] : Array (Fin 8))[i.val]!,some 9⟩
def rules : List Rule := [
  .forbidden 0 5,
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .cap 0 [5,6,7,8],
  .forbidden 1 5,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .cap 1 [5,6,7,8],
  .forbidden 2 5,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .cap 2 [5,6,7,8],
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .cap 3 [5,6,7,8],
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .cap 4 [5,6,7,8],
  .degree 5 [6,7,8,11],
  .degree 6 [5,7,8,11],
  .degree 7 [5,6,8,11],
  .degree 8 [5,6,7,11],
  .visible 10 false,
  .lower 0 5 10,
  .lower 0 6 10,
  .lower 0 7 10,
  .lower 0 8 10,
  .lower 1 5 10,
  .lower 1 6 10,
  .lower 1 7 10,
  .lower 1 8 10,
  .lower 2 5 10,
  .lower 2 6 10,
  .lower 2 7 10,
  .lower 2 8 10,
  .lower 3 5 10,
  .lower 3 6 10,
  .lower 3 7 10,
  .lower 3 8 10,
  .lower 4 5 10,
  .lower 4 6 10,
  .lower 4 7 10,
  .lower 4 8 10
]
graph_rup certificate (include_str "twelve-certs/twelve43.cnf") (include_str "twelve-certs/twelve43.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile43
