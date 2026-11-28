import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile50
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,3,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 1 9,
  .forbidden 2 9,
  .forbidden 3 9,
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .visible 4 true,
  .degree 4 [3,9,10,11],
  .cap 4 [3,5,8],
  .cap 4 [5,7,8],
  .forbidden 9 12,
  .degree 9 [4,5,6,7],
  .degree 9 [4,5,6,8],
  .degree 9 [4,6,7,8],
  .cap 9 [0,3,12],
  .cap 9 [1,3,12],
  .cap 9 [2,3,12],
  .degree 12 [10],
  .degree 12 [11],
  .lower 0 9 4,
  .lower 1 9 4,
  .lower 2 9 4,
  .same 3 4 false,
  .lower 3 9 4,
  .lower 3 9 10,
  .lower 3 9 11,
  .lower 4 5 9,
  .lower 4 7 9,
  .lower 4 8 9,
  .lower 9 12 10,
  .lower 9 12 11
]
graph_rup certificate (include_str "thirteen-certs/thirteen50.cnf") (include_str "thirteen-certs/thirteen50.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile50

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile51
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,2,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .visible 4 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen51.cnf") (include_str "thirteen-certs/thirteen51.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile51

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile52
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,0,2,2,2,2,6,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 5,
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .degree 0 [1,2,3,4],
  .degree 0 [1,2,3,9],
  .degree 0 [1,2,3,10],
  .degree 0 [1,2,3,11],
  .degree 0 [1,2,4,9],
  .degree 0 [1,2,4,10],
  .degree 0 [1,2,4,11],
  .degree 0 [1,3,4,9],
  .degree 0 [1,3,4,10],
  .degree 0 [1,3,4,11],
  .degree 0 [2,3,4,9],
  .degree 0 [2,3,4,10],
  .degree 0 [2,3,4,11],
  .cap 0 [5,6,7,8],
  .forbidden 1 5,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .degree 1 [0,2,3,4],
  .degree 1 [0,2,3,9],
  .degree 1 [0,2,3,10],
  .degree 1 [0,2,3,11],
  .degree 1 [0,2,4,9],
  .degree 1 [0,2,4,10],
  .degree 1 [0,2,4,11],
  .degree 1 [0,3,4,9],
  .degree 1 [0,3,4,10],
  .degree 1 [0,3,4,11],
  .degree 1 [2,3,4,9],
  .degree 1 [2,3,4,10],
  .degree 1 [2,3,4,11],
  .cap 1 [5,6,7,8],
  .forbidden 2 5,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .degree 2 [0,1,3,4],
  .degree 2 [0,1,3,9],
  .degree 2 [0,1,3,10],
  .degree 2 [0,1,3,11],
  .degree 2 [0,1,4,9],
  .degree 2 [0,1,4,10],
  .degree 2 [0,1,4,11],
  .degree 2 [0,3,4,9],
  .degree 2 [0,3,4,10],
  .degree 2 [0,3,4,11],
  .degree 2 [1,3,4,9],
  .degree 2 [1,3,4,10],
  .degree 2 [1,3,4,11],
  .cap 2 [5,6,7,8],
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .degree 3 [0,1,2,4],
  .degree 3 [0,1,2,9],
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
  .degree 3 [0,1,4,9],
  .degree 3 [0,1,4,10],
  .degree 3 [0,1,4,11],
  .degree 3 [0,2,4,9],
  .degree 3 [0,2,4,10],
  .degree 3 [0,2,4,11],
  .degree 3 [1,2,4,9],
  .degree 3 [1,2,4,10],
  .degree 3 [1,2,4,11],
  .cap 3 [5,6,7,8],
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .degree 4 [0,1,2,3],
  .degree 4 [0,1,2,9],
  .degree 4 [0,1,2,10],
  .degree 4 [0,1,2,11],
  .degree 4 [0,1,3,9],
  .degree 4 [0,1,3,10],
  .degree 4 [0,1,3,11],
  .degree 4 [0,2,3,9],
  .degree 4 [0,2,3,10],
  .degree 4 [0,2,3,11],
  .degree 4 [1,2,3,9],
  .degree 4 [1,2,3,10],
  .degree 4 [1,2,3,11],
  .cap 4 [5,6,7,8],
  .forbidden 5 12,
  .degree 5 [6,7,8,9],
  .degree 5 [6,7,8,10],
  .degree 5 [6,7,8,11],
  .degree 5 [6,7,9,10],
  .degree 5 [6,7,9,11],
  .degree 5 [6,7,10,11],
  .degree 5 [6,8,9,10],
  .degree 5 [6,8,9,11],
  .degree 5 [6,8,10,11],
  .degree 5 [7,8,9,10],
  .degree 5 [7,8,9,11],
  .degree 5 [7,8,10,11],
  .cap 5 [0,1,9,12],
  .cap 5 [0,1,10,12],
  .cap 5 [0,1,11,12],
  .cap 5 [0,2,9,12],
  .cap 5 [0,2,10,12],
  .cap 5 [0,2,11,12],
  .cap 5 [0,3,9,12],
  .cap 5 [0,3,10,12],
  .cap 5 [0,3,11,12],
  .cap 5 [0,4,9,12],
  .cap 5 [0,4,10,12],
  .cap 5 [0,4,11,12],
  .cap 5 [1,2,3,12],
  .cap 5 [1,2,9,12],
  .cap 5 [1,2,10,12],
  .cap 5 [1,2,11,12],
  .cap 5 [1,3,9,12],
  .cap 5 [1,3,10,12],
  .cap 5 [1,3,11,12],
  .cap 5 [1,4,9,12],
  .cap 5 [1,4,10,12],
  .cap 5 [1,4,11,12],
  .cap 5 [2,3,9,12],
  .cap 5 [2,3,10,12],
  .cap 5 [2,3,11,12],
  .cap 5 [2,4,9,12],
  .cap 5 [2,4,10,12],
  .cap 5 [2,4,11,12],
  .cap 5 [3,4,9,12],
  .cap 5 [3,4,10,12],
  .cap 5 [3,4,11,12],
  .cap 5 [4,9,11,12],
  .cap 5 [4,10,11,12],
  .degree 6 [5,7,9,10],
  .degree 6 [5,8,9,10],
  .degree 6 [7,8,9,10],
  .forbidden 7 12,
  .degree 7 [5,6,8,9],
  .degree 7 [5,6,8,10],
  .degree 7 [5,6,8,11],
  .degree 7 [5,6,9,10],
  .degree 7 [5,8,9,10],
  .degree 7 [6,8,9,10],
  .cap 7 [0,2,3,12],
  .cap 7 [0,4,11,12],
  .cap 7 [1,4,11,12],
  .cap 7 [2,3,11,12],
  .cap 7 [2,4,11,12],
  .cap 7 [3,4,9,12],
  .cap 7 [3,4,11,12],
  .visible 9 false,
  .visible 9 true,
  .cap 9 [0,1,2,3,6],
  .cap 9 [0,1,2,3,8],
  .cap 9 [0,1,2,4,6],
  .cap 9 [0,1,2,4,7],
  .cap 9 [0,1,2,4,8],
  .cap 9 [0,1,3,4,6],
  .cap 9 [0,1,3,4,8],
  .cap 9 [0,2,3,4,6],
  .cap 9 [0,2,3,4,8],
  .cap 9 [1,2,3,4,6],
  .cap 9 [1,2,3,4,8],
  .visible 10 false,
  .visible 10 true,
  .cap 10 [0,1,2,4,6],
  .cap 10 [0,1,2,4,7],
  .cap 10 [0,1,2,4,8],
  .visible 11 false,
  .visible 11 true,
  .degree 11 [0,1,2,4,12],
  .cap 11 [0,1,2,3,6],
  .cap 11 [0,1,2,3,8],
  .cap 11 [0,1,2,4,6],
  .cap 11 [0,1,2,4,7],
  .cap 11 [0,1,2,4,8],
  .cap 11 [0,1,3,4,6],
  .cap 11 [0,1,3,4,8],
  .cap 11 [0,2,3,4,6],
  .cap 11 [0,2,3,4,8],
  .cap 11 [1,2,3,4,6],
  .cap 11 [1,2,3,4,8],
  .degree 12 [9],
  .degree 12 [10],
  .degree 12 [11],
  .lower 0 5 9,
  .lower 0 5 10,
  .lower 0 5 11,
  .lower 0 6 9,
  .lower 0 6 11,
  .lower 0 7 9,
  .lower 0 7 10,
  .lower 0 7 11,
  .lower 0 8 9,
  .lower 0 8 11,
  .lower 0 9 1,
  .lower 0 9 2,
  .lower 0 9 3,
  .lower 0 9 4,
  .lower 0 10 3,
  .lower 0 11 1,
  .lower 0 11 2,
  .lower 0 11 3,
  .lower 0 11 4,
  .lower 1 5 9,
  .lower 1 5 10,
  .lower 1 5 11,
  .lower 1 6 9,
  .lower 1 6 11,
  .lower 1 7 9,
  .lower 1 7 10,
  .lower 1 7 11,
  .lower 1 8 9,
  .lower 1 8 11,
  .lower 1 9 0,
  .lower 1 9 2,
  .lower 1 9 3,
  .lower 1 9 4,
  .lower 1 10 3,
  .lower 1 11 0,
  .lower 1 11 2,
  .lower 1 11 3,
  .lower 1 11 4,
  .lower 2 5 9,
  .lower 2 5 10,
  .lower 2 5 11,
  .lower 2 6 9,
  .lower 2 6 11,
  .lower 2 7 9,
  .lower 2 7 10,
  .lower 2 7 11,
  .lower 2 8 9,
  .lower 2 8 11,
  .lower 2 9 0,
  .lower 2 9 1,
  .lower 2 9 3,
  .lower 2 9 4,
  .lower 2 10 3,
  .lower 2 11 0,
  .lower 2 11 1,
  .lower 2 11 3,
  .lower 2 11 4,
  .lower 3 5 9,
  .lower 3 5 10,
  .lower 3 5 11,
  .lower 3 6 9,
  .lower 3 6 10,
  .lower 3 6 11,
  .lower 3 7 9,
  .lower 3 7 10,
  .lower 3 7 11,
  .lower 3 8 9,
  .lower 3 8 10,
  .lower 3 8 11,
  .lower 3 9 0,
  .lower 3 9 1,
  .lower 3 9 2,
  .lower 3 9 4,
  .lower 3 11 0,
  .lower 3 11 1,
  .lower 3 11 2,
  .lower 3 11 4,
  .lower 4 5 9,
  .lower 4 5 10,
  .lower 4 5 11,
  .lower 4 6 9,
  .lower 4 6 11,
  .lower 4 7 9,
  .lower 4 7 10,
  .lower 4 7 11,
  .lower 4 8 9,
  .lower 4 8 11,
  .lower 4 9 0,
  .lower 4 9 1,
  .lower 4 9 2,
  .lower 4 9 3,
  .lower 4 10 3,
  .lower 4 11 0,
  .lower 4 11 1,
  .lower 4 11 2,
  .lower 4 11 3,
  .lower 5 9 6,
  .lower 5 9 7,
  .lower 5 9 8,
  .lower 5 10 6,
  .lower 5 10 7,
  .lower 5 10 8,
  .lower 5 11 6,
  .lower 5 11 7,
  .lower 5 11 8,
  .lower 5 11 9,
  .lower 5 11 10,
  .lower 5 12 9,
  .lower 5 12 10,
  .lower 5 12 11,
  .lower 6 9 5,
  .lower 6 10 5,
  .lower 6 11 5,
  .lower 6 11 7,
  .lower 6 11 8,
  .lower 7 9 5,
  .lower 7 10 5,
  .lower 7 11 5,
  .lower 7 11 6,
  .lower 7 11 8,
  .lower 7 12 9,
  .lower 7 12 10,
  .lower 7 12 11,
  .lower 8 9 5,
  .lower 8 10 5,
  .lower 8 11 5
]
graph_rup certificate (include_str "thirteen-certs/thirteen52.cnf") (include_str "thirteen-certs/thirteen52.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile52

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile53
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,0,2,2,2,2,4,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 12,
  .forbidden 1 12,
  .forbidden 2 12,
  .forbidden 3 12,
  .forbidden 4 12,
  .forbidden 5 9,
  .forbidden 5 12,
  .degree 5 [6,7,8,10],
  .degree 5 [6,7,8,11],
  .forbidden 6 9,
  .forbidden 6 12,
  .degree 6 [5,7,8,10],
  .degree 6 [5,7,8,11],
  .forbidden 7 9,
  .degree 7 [5,6,8,10],
  .degree 7 [5,6,8,11],
  .degree 9 [0,1,2,3,4],
  .degree 9 [0,1,2,3,12],
  .degree 9 [0,1,2,4,12],
  .degree 9 [0,1,3,4,12],
  .degree 9 [0,2,3,4,12],
  .degree 9 [1,2,3,4,12],
  .cap 9 [5,6,7],
  .cap 9 [5,6,10],
  .cap 9 [5,10,11],
  .visible 10 false,
  .visible 11 false,
  .degree 12 [9],
  .cap 12 [0,1,2,3,4,5,6],
  .lower 0 12 9,
  .lower 1 12 9,
  .lower 2 12 9,
  .lower 3 12 9,
  .lower 4 12 9,
  .lower 5 9 10,
  .lower 5 9 11,
  .lower 5 12 10,
  .lower 5 12 11,
  .lower 6 9 10,
  .lower 6 9 11,
  .lower 6 12 10,
  .lower 6 12 11,
  .lower 7 9 10,
  .lower 7 9 11,
  .lower 9 10 0,
  .lower 9 10 1,
  .lower 9 10 2,
  .lower 9 10 3,
  .lower 9 10 4,
  .lower 9 11 0,
  .lower 9 11 1,
  .lower 9 11 2,
  .lower 9 11 3,
  .lower 9 11 4
]
graph_rup certificate (include_str "thirteen-certs/thirteen53.cnf") (include_str "thirteen-certs/thirteen53.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile53

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile54
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,0,2,2,2,2,3,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 1 9,
  .forbidden 2 9,
  .forbidden 3 9,
  .forbidden 4 9,
  .visible 9 false
]
graph_rup certificate (include_str "thirteen-certs/thirteen54.cnf") (include_str "thirteen-certs/thirteen54.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile54

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile55
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,0,2,2,2,2,2,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 12,
  .degree 0 [1,2,3,4],
  .forbidden 1 12,
  .degree 1 [0,2,3,4],
  .forbidden 5 12,
  .degree 5 [6,7,8,9],
  .forbidden 6 12,
  .degree 6 [5,7,8,9],
  .forbidden 7 12,
  .degree 7 [5,6,8,9],
  .forbidden 8 12,
  .degree 8 [5,6,7,9],
  .forbidden 9 12,
  .degree 9 [5,6,7,8],
  .degree 12 [10],
  .degree 12 [11],
  .cap 12 [0,1,5,6,7,8,9],
  .lower 0 12 10,
  .lower 0 12 11,
  .lower 1 12 10,
  .lower 1 12 11,
  .lower 5 12 10,
  .lower 5 12 11,
  .lower 6 12 10,
  .lower 6 12 11,
  .lower 7 12 10,
  .lower 7 12 11,
  .lower 8 12 10,
  .lower 8 12 11,
  .lower 9 12 10,
  .lower 9 12 11
]
graph_rup certificate (include_str "thirteen-certs/thirteen55.cnf") (include_str "thirteen-certs/thirteen55.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile55
