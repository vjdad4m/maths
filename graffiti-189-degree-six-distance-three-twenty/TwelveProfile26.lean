import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile26
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,2,2,2,2,2,5,6,6] : Array (Fin 8))[i.val]!,some 9⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .degree 0 [1,2,3,11],
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .degree 1 [0,2,3,11],
  .forbidden 2 4,
  .forbidden 2 5,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .degree 2 [0,1,3,11],
  .forbidden 3 4,
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .degree 3 [0,1,2,11],
  .cap 4 [0,1,2,3],
  .cap 5 [0,1,2,3],
  .cap 6 [0,1,2,3],
  .cap 7 [0,1,2,3],
  .cap 8 [0,1,2,3],
  .visible 10 true,
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 6 10,
  .lower 0 7 10,
  .lower 0 8 10,
  .lower 1 4 10,
  .lower 1 5 10,
  .lower 1 6 10,
  .lower 1 7 10,
  .lower 1 8 10,
  .lower 2 4 10,
  .lower 2 5 10,
  .lower 2 6 10,
  .lower 2 7 10,
  .lower 2 8 10,
  .lower 3 4 10,
  .lower 3 5 10,
  .lower 3 6 10,
  .lower 3 7 10,
  .lower 3 8 10
]
graph_rup certificate (include_str "twelve-certs/twelve26.cnf") (include_str "twelve-certs/twelve26.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile26
