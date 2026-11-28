import SixTwelveSat189
import GraphRup189
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixTwelveSat.TwelveProfile37
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,2,6,6] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .visible 4 true
]
graph_rup certificate (include_str "twelve-certs/twelve37.cnf") (include_str "twelve-certs/twelve37.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixTwelveSat.TwelveProfile37
