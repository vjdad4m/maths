import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile40
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 3⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 11,
  .forbidden 0 12,
  .degree 0 [1,2,6,7],
  .degree 0 [1,2,7,10],
  .cap 0 [4,5,11,12],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 11 [7,8,9,10,12],
  .degree 12 [7,8,9,10,11],
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 11 6,
  .lower 0 12 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen40.cnf") (include_str "thirteen-certs/thirteen40.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile40

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile41
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 6⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 11,
  .degree 0 [1,2,6,7],
  .degree 0 [1,2,7,10],
  .cap 0 [3,4,5,11],
  .degree 3 [4,5,8,9],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 11 [7,8,9,10,12],
  .lower 0 3 10,
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen41.cnf") (include_str "thirteen-certs/thirteen41.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile41

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile42
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 8⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 11,
  .degree 0 [1,2,6,7],
  .degree 0 [1,2,7,10],
  .cap 0 [3,4,5,11],
  .degree 3 [4,5,8,9],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 11 [7,8,9,10,12],
  .lower 0 3 10,
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen42.cnf") (include_str "thirteen-certs/thirteen42.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile42

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile43
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 10⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 11,
  .degree 0 [1,2,6,7],
  .degree 0 [1,2,7,10],
  .cap 0 [3,4,5,11],
  .degree 3 [4,5,8,9],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 11 [7,8,9,10,12],
  .lower 0 3 10,
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen43.cnf") (include_str "thirteen-certs/thirteen43.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile43

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile44
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 11⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 12,
  .degree 0 [1,2,6,7],
  .degree 0 [1,2,7,10],
  .cap 0 [3,4,5,12],
  .degree 3 [4,5,8,9],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 12 [7,8,9,10,11],
  .lower 0 3 10,
  .lower 0 4 10,
  .lower 0 5 10,
  .lower 0 12 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen44.cnf") (include_str "thirteen-certs/thirteen44.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile44

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile45
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,2,2,2,2,4,5,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 0 12,
  .degree 0 [1,2,3,8],
  .degree 0 [1,2,3,10],
  .forbidden 1 9,
  .forbidden 1 12,
  .degree 1 [0,2,3,8],
  .degree 1 [0,2,3,10],
  .forbidden 2 9,
  .forbidden 2 12,
  .degree 2 [0,1,3,8],
  .degree 2 [0,1,3,10],
  .forbidden 3 12,
  .forbidden 4 8,
  .forbidden 4 12,
  .degree 4 [5,6,7,9],
  .degree 4 [5,6,7,10],
  .forbidden 5 8,
  .forbidden 5 12,
  .degree 5 [4,6,7,9],
  .forbidden 6 8,
  .forbidden 6 12,
  .forbidden 7 8,
  .forbidden 7 12,
  .degree 8 [0,1,2,3,10],
  .degree 8 [0,1,2,3,11],
  .degree 8 [0,1,2,10,12],
  .degree 8 [0,1,2,11,12],
  .degree 8 [0,1,3,10,12],
  .degree 8 [0,1,3,11,12],
  .degree 8 [0,2,3,10,12],
  .degree 8 [0,2,3,11,12],
  .degree 8 [1,2,3,10,12],
  .degree 8 [1,2,3,11,12],
  .cap 8 [4,5,6],
  .cap 8 [4,5,7],
  .cap 8 [4,5,9],
  .cap 8 [4,6,7],
  .cap 8 [4,9,10],
  .cap 8 [4,9,12],
  .cap 8 [5,6,7],
  .cap 8 [5,9,10],
  .cap 8 [6,9,10],
  .cap 8 [7,9,10],
  .degree 9 [4,5,6,7,10],
  .degree 9 [4,5,6,7,11],
  .degree 9 [4,5,6,7,12],
  .degree 9 [4,5,6,10,12],
  .degree 9 [4,5,6,11,12],
  .degree 9 [4,5,7,8,12],
  .degree 9 [4,5,7,10,12],
  .degree 9 [4,5,7,11,12],
  .degree 9 [4,5,8,10,12],
  .degree 9 [4,6,7,8,12],
  .degree 9 [4,6,7,10,12],
  .degree 9 [4,6,7,11,12],
  .degree 9 [4,6,8,10,12],
  .degree 9 [4,7,8,10,12],
  .degree 9 [5,6,7,8,12],
  .degree 9 [5,6,7,10,11],
  .degree 9 [5,6,7,10,12],
  .degree 9 [5,6,7,11,12],
  .degree 9 [5,6,8,10,12],
  .degree 9 [5,7,8,10,12],
  .degree 9 [6,7,8,10,12],
  .cap 9 [0,1,2],
  .cap 9 [0,1,8],
  .cap 9 [0,4,8],
  .cap 9 [1,8,10],
  .cap 9 [1,8,11],
  .visible 10 false,
  .visible 10 true,
  .visible 11 true,
  .degree 12 [9],
  .cap 12 [0,1,2,3,4,6,7],
  .cap 12 [0,1,3,4,5,6,7],
  .lower 0 9 8,
  .lower 0 9 10,
  .lower 0 9 11,
  .lower 0 12 8,
  .lower 1 9 8,
  .lower 1 9 10,
  .lower 1 9 11,
  .lower 1 12 8,
  .lower 2 9 8,
  .lower 2 9 10,
  .lower 2 9 11,
  .lower 2 12 8,
  .lower 3 12 8,
  .lower 4 8 9,
  .lower 4 8 10,
  .lower 4 8 11,
  .lower 4 9 11,
  .lower 4 12 9,
  .lower 5 8 9,
  .lower 5 8 10,
  .lower 5 8 11,
  .lower 5 12 9,
  .lower 6 8 9,
  .lower 6 8 11,
  .lower 6 12 9,
  .lower 7 8 9,
  .lower 7 8 11,
  .lower 7 12 9,
  .lower 8 9 10,
  .lower 8 9 11,
  .lower 8 9 12,
  .lower 8 10 0,
  .lower 8 10 1,
  .lower 8 10 2,
  .lower 8 10 3,
  .lower 8 12 10,
  .lower 8 12 11,
  .lower 9 10 4,
  .lower 9 10 5,
  .lower 9 10 6,
  .lower 9 10 7,
  .lower 9 11 4,
  .lower 9 11 5,
  .lower 9 11 6,
  .lower 9 11 7
]
graph_rup certificate (include_str "thirteen-certs/thirteen45.cnf") (include_str "thirteen-certs/thirteen45.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile45

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile46
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,2,2,2,2,3,5,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 8,
  .forbidden 1 8,
  .forbidden 2 8,
  .forbidden 3 8,
  .visible 8 false
]
graph_rup certificate (include_str "thirteen-certs/thirteen46.cnf") (include_str "thirteen-certs/thirteen46.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile46

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile47
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,2,2,2,2,2,6,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 12,
  .degree 0 [1,2,3,9],
  .degree 0 [1,2,3,10],
  .degree 0 [1,2,3,11],
  .degree 0 [1,2,9,10],
  .degree 0 [1,2,9,11],
  .degree 0 [1,2,10,11],
  .degree 0 [1,3,9,10],
  .degree 0 [1,3,9,11],
  .degree 0 [1,3,10,11],
  .degree 0 [2,3,9,10],
  .degree 0 [2,3,9,11],
  .degree 0 [2,3,10,11],
  .cap 0 [1,4,5,12],
  .cap 0 [1,4,8,12],
  .cap 0 [1,5,8,12],
  .cap 0 [1,6,8,12],
  .cap 0 [2,4,5,12],
  .cap 0 [2,4,8,12],
  .cap 0 [2,5,6,12],
  .cap 0 [2,5,8,12],
  .cap 0 [2,6,8,12],
  .cap 0 [3,4,5,12],
  .cap 0 [3,4,8,12],
  .cap 0 [3,5,6,12],
  .cap 0 [3,5,8,12],
  .cap 0 [3,6,8,12],
  .cap 0 [4,5,6,12],
  .cap 0 [4,5,7,12],
  .cap 0 [4,5,8,12],
  .cap 0 [4,5,9,12],
  .cap 0 [4,5,10,12],
  .cap 0 [4,5,11,12],
  .cap 0 [4,6,9,12],
  .cap 0 [4,6,10,12],
  .cap 0 [4,6,11,12],
  .cap 0 [4,7,9,12],
  .cap 0 [4,7,10,12],
  .cap 0 [4,7,11,12],
  .cap 0 [4,8,9,12],
  .cap 0 [4,8,10,12],
  .cap 0 [4,8,11,12],
  .cap 0 [5,6,7,12],
  .cap 0 [5,6,8,12],
  .cap 0 [5,6,9,12],
  .cap 0 [5,6,10,12],
  .cap 0 [5,6,11,12],
  .cap 0 [5,7,9,12],
  .cap 0 [5,7,10,12],
  .cap 0 [5,7,11,12],
  .cap 0 [5,8,9,12],
  .cap 0 [5,8,10,12],
  .cap 0 [5,8,11,12],
  .cap 0 [6,7,9,12],
  .cap 0 [6,7,10,12],
  .cap 0 [6,7,11,12],
  .cap 0 [6,8,9,12],
  .cap 0 [6,8,10,12],
  .cap 0 [6,8,11,12],
  .cap 0 [7,8,9,12],
  .cap 0 [7,8,10,12],
  .cap 0 [7,8,11,12],
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .forbidden 1 12,
  .degree 1 [0,2,3,9],
  .degree 1 [0,2,3,10],
  .degree 1 [0,2,3,11],
  .degree 1 [0,2,9,10],
  .degree 1 [2,3,9,10],
  .cap 1 [4,5,6,12],
  .cap 1 [4,6,11,12],
  .cap 1 [4,7,11,12],
  .cap 1 [5,6,7,12],
  .cap 1 [5,6,8,12],
  .forbidden 2 4,
  .forbidden 2 5,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .forbidden 2 12,
  .degree 2 [0,1,3,9],
  .degree 2 [0,1,3,10],
  .degree 2 [0,1,3,11],
  .degree 2 [0,1,9,10],
  .degree 2 [0,3,9,10],
  .degree 2 [1,3,9,10],
  .cap 2 [4,5,6,8],
  .cap 2 [4,5,6,12],
  .cap 2 [4,6,7,8],
  .cap 2 [5,7,8,12],
  .forbidden 3 4,
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 12,
  .degree 3 [0,1,2,9],
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
  .cap 3 [4,5,7,12],
  .cap 3 [4,6,7,12],
  .cap 3 [4,7,8,12],
  .cap 3 [4,7,10,12],
  .forbidden 4 12,
  .degree 4 [5,6,7,8],
  .degree 4 [5,6,7,9],
  .degree 4 [5,6,7,10],
  .degree 4 [5,6,7,11],
  .degree 4 [5,6,8,9],
  .degree 4 [5,6,8,10],
  .degree 4 [5,6,8,11],
  .degree 4 [5,7,8,9],
  .degree 4 [5,7,8,10],
  .degree 4 [5,7,8,11],
  .degree 4 [6,7,8,9],
  .degree 4 [6,7,8,10],
  .degree 4 [6,7,8,11],
  .cap 4 [0,1,2,3],
  .cap 4 [0,1,2,12],
  .cap 4 [0,1,9,12],
  .cap 4 [0,1,10,12],
  .cap 4 [0,2,3,12],
  .cap 4 [0,2,9,12],
  .cap 4 [0,3,9,12],
  .cap 4 [0,9,10,12],
  .cap 4 [1,2,9,12],
  .cap 4 [1,2,10,12],
  .cap 4 [1,9,11,12],
  .cap 4 [2,3,9,12],
  .cap 4 [2,9,10,12],
  .forbidden 5 12,
  .degree 5 [4,6,7,8],
  .degree 5 [4,6,7,9],
  .degree 5 [4,6,7,10],
  .degree 5 [4,6,7,11],
  .degree 5 [4,6,8,9],
  .degree 5 [4,6,8,10],
  .degree 5 [4,6,8,11],
  .degree 5 [4,7,8,9],
  .degree 5 [4,7,8,10],
  .degree 5 [4,7,8,11],
  .degree 5 [6,7,8,9],
  .degree 5 [6,7,8,10],
  .degree 5 [6,7,8,11],
  .cap 5 [0,1,2,3],
  .cap 5 [0,2,3,12],
  .cap 5 [1,2,3,12],
  .cap 5 [1,9,10,12],
  .cap 5 [1,9,11,12],
  .cap 5 [1,10,11,12],
  .cap 5 [2,9,10,12],
  .cap 5 [2,9,11,12],
  .cap 5 [2,10,11,12],
  .cap 5 [3,9,10,12],
  .cap 5 [3,9,11,12],
  .cap 5 [3,10,11,12],
  .forbidden 6 12,
  .degree 6 [4,5,7,8],
  .degree 6 [4,5,7,9],
  .degree 6 [4,5,7,10],
  .degree 6 [4,5,7,11],
  .degree 6 [4,5,8,9],
  .degree 6 [4,5,8,10],
  .degree 6 [4,5,8,11],
  .degree 6 [4,7,8,9],
  .degree 6 [4,7,8,10],
  .degree 6 [4,7,8,11],
  .degree 6 [5,7,8,9],
  .degree 6 [5,7,8,10],
  .degree 6 [5,7,8,11],
  .cap 6 [0,1,2,3],
  .cap 6 [0,1,11,12],
  .cap 6 [0,3,11,12],
  .cap 6 [0,10,11,12],
  .cap 6 [1,10,11,12],
  .cap 6 [2,10,11,12],
  .cap 6 [3,10,11,12],
  .forbidden 7 12,
  .degree 7 [4,5,6,8],
  .degree 7 [4,5,6,9],
  .degree 7 [4,5,6,10],
  .degree 7 [4,5,6,11],
  .degree 7 [4,5,8,9],
  .degree 7 [4,5,8,10],
  .degree 7 [4,5,8,11],
  .degree 7 [4,6,8,9],
  .degree 7 [4,6,8,10],
  .degree 7 [4,6,8,11],
  .degree 7 [5,6,8,9],
  .degree 7 [5,6,8,10],
  .degree 7 [5,6,8,11],
  .cap 7 [0,1,2,3],
  .cap 7 [0,1,2,12],
  .cap 7 [0,1,3,12],
  .cap 7 [0,1,10,12],
  .cap 7 [2,3,10,12],
  .forbidden 8 12,
  .degree 8 [4,5,6,7],
  .degree 8 [4,5,6,9],
  .degree 8 [4,5,6,10],
  .degree 8 [4,5,6,11],
  .degree 8 [4,5,7,9],
  .degree 8 [4,5,7,10],
  .degree 8 [4,5,7,11],
  .degree 8 [4,6,7,9],
  .degree 8 [4,6,7,10],
  .degree 8 [4,6,7,11],
  .degree 8 [5,6,7,9],
  .degree 8 [5,6,7,10],
  .degree 8 [5,6,7,11],
  .cap 8 [0,1,2,12],
  .cap 8 [0,1,10,12],
  .cap 8 [0,2,3,12],
  .visible 9 false,
  .visible 9 true,
  .degree 9 [0,1,2,3,12],
  .degree 9 [0,4,5,6,7],
  .visible 10 false,
  .visible 10 true,
  .degree 10 [0,1,2,3,5],
  .degree 10 [0,1,2,3,12],
  .degree 10 [0,1,2,5,7],
  .degree 10 [0,1,3,5,7],
  .degree 10 [0,2,3,5,7],
  .degree 10 [0,2,6,9,12],
  .degree 10 [1,2,3,5,7],
  .cap 10 [0,4,5,6,7],
  .cap 10 [0,4,5,6,8],
  .cap 10 [0,4,5,7,8],
  .cap 10 [0,4,6,7,8],
  .cap 10 [0,5,6,7,8],
  .cap 10 [1,4,5,6,8],
  .cap 10 [1,4,5,7,8],
  .cap 10 [1,4,6,7,8],
  .cap 10 [1,5,6,7,8],
  .cap 10 [2,4,6,7,8],
  .cap 10 [3,4,5,6,7],
  .cap 10 [3,4,5,6,8],
  .cap 10 [3,4,5,7,8],
  .cap 10 [3,4,6,7,8],
  .cap 10 [3,5,6,7,8],
  .visible 11 false,
  .visible 11 true,
  .degree 11 [0,1,2,3,6],
  .degree 11 [0,1,2,3,7],
  .degree 11 [0,1,2,5,6],
  .degree 11 [0,1,3,5,6],
  .degree 11 [0,1,7,9,12],
  .degree 11 [0,2,3,5,6],
  .degree 11 [0,2,4,7,12],
  .degree 11 [0,2,4,10,12],
  .degree 11 [0,3,4,5,6],
  .degree 11 [0,4,5,6,7],
  .degree 11 [0,4,7,9,12],
  .degree 11 [1,2,3,5,6],
  .degree 11 [2,3,5,6,7],
  .degree 11 [2,3,5,6,8],
  .degree 11 [2,3,7,9,12],
  .degree 11 [2,4,7,9,12],
  .degree 11 [2,4,7,10,12],
  .degree 11 [2,7,9,10,12],
  .degree 11 [3,4,5,6,8],
  .degree 11 [3,5,6,7,8],
  .degree 11 [3,7,9,10,12],
  .degree 11 [4,5,6,7,12],
  .degree 11 [4,7,9,10,12],
  .cap 11 [0,1,5,6,8],
  .cap 11 [0,2,5,6,8],
  .cap 11 [0,5,6,7,8],
  .cap 11 [1,4,5,6,7],
  .cap 11 [1,4,5,6,8],
  .cap 11 [1,4,5,7,8],
  .cap 11 [1,4,6,7,8],
  .cap 11 [2,4,5,6,7],
  .cap 11 [2,4,5,7,8],
  .cap 11 [2,4,6,7,8],
  .cap 11 [2,5,6,7,8],
  .cap 11 [3,4,5,6,7],
  .cap 11 [3,4,5,7,8],
  .cap 11 [3,4,6,7,8],
  .cap 11 [4,5,6,7,9],
  .cap 11 [4,5,6,7,12],
  .cap 11 [4,5,6,8,12],
  .cap 11 [4,5,7,8,12],
  .cap 11 [4,6,7,8,10],
  .cap 11 [4,6,7,8,12],
  .cap 11 [5,6,7,8,12],
  .cap 11 [5,7,8,10,12],
  .degree 12 [9],
  .degree 12 [10],
  .degree 12 [11],
  .cap 12 [0,1,2,3,4,5,11],
  .cap 12 [0,1,2,3,4,6,10],
  .cap 12 [0,1,2,3,4,6,11],
  .cap 12 [0,1,2,3,4,7,8],
  .cap 12 [0,1,2,3,4,7,10],
  .cap 12 [0,1,2,3,4,7,11],
  .cap 12 [0,1,2,3,4,8,9],
  .cap 12 [0,1,2,3,4,8,10],
  .cap 12 [0,1,2,3,4,8,11],
  .cap 12 [0,1,2,3,4,10,11],
  .cap 12 [0,1,2,3,5,6,7],
  .cap 12 [0,1,2,3,5,6,8],
  .cap 12 [0,1,2,3,5,6,11],
  .cap 12 [0,1,2,3,5,7,11],
  .cap 12 [0,1,2,3,5,8,11],
  .cap 12 [0,1,2,3,5,10,11],
  .cap 12 [0,1,2,3,6,7,8],
  .cap 12 [0,1,2,3,6,7,11],
  .cap 12 [0,1,2,3,6,8,11],
  .cap 12 [0,1,2,3,6,10,11],
  .cap 12 [0,1,2,3,7,8,9],
  .cap 12 [0,1,2,3,7,8,11],
  .cap 12 [0,1,2,3,7,10,11],
  .cap 12 [0,1,2,3,8,10,11],
  .same 0 1 false,
  .same 0 2 false,
  .same 0 3 false,
  .lower 0 4 9,
  .lower 0 4 10,
  .lower 0 4 11,
  .lower 0 5 9,
  .lower 0 5 10,
  .lower 0 5 11,
  .lower 0 6 9,
  .lower 0 6 10,
  .lower 0 6 11,
  .lower 0 7 9,
  .lower 0 7 10,
  .lower 0 7 11,
  .lower 0 8 9,
  .lower 0 8 10,
  .lower 0 8 11,
  .lower 0 9 1,
  .lower 0 9 2,
  .lower 0 9 3,
  .lower 0 10 1,
  .lower 0 10 2,
  .lower 0 10 3,
  .lower 0 11 1,
  .lower 0 11 2,
  .lower 0 11 3,
  .lower 0 11 9,
  .lower 0 11 10,
  .lower 0 12 9,
  .lower 0 12 10,
  .lower 0 12 11,
  .lower 1 4 9,
  .lower 1 4 10,
  .lower 1 4 11,
  .lower 1 5 9,
  .lower 1 5 10,
  .lower 1 5 11,
  .lower 1 6 9,
  .lower 1 6 10,
  .lower 1 6 11,
  .lower 1 7 9,
  .lower 1 7 10,
  .lower 1 7 11,
  .lower 1 8 11,
  .lower 1 10 0,
  .lower 1 10 2,
  .lower 1 11 0,
  .lower 1 11 3,
  .lower 1 12 9,
  .lower 1 12 10,
  .lower 1 12 11,
  .lower 2 4 9,
  .lower 2 4 10,
  .lower 2 4 11,
  .lower 2 5 9,
  .lower 2 5 10,
  .lower 2 5 11,
  .lower 2 6 9,
  .lower 2 6 10,
  .lower 2 6 11,
  .lower 2 7 10,
  .lower 2 7 11,
  .lower 2 8 10,
  .lower 2 8 11,
  .lower 2 10 0,
  .lower 2 11 0,
  .lower 2 11 1,
  .lower 2 11 3,
  .lower 2 11 9,
  .lower 2 11 10,
  .lower 2 12 9,
  .lower 2 12 10,
  .lower 2 12 11,
  .lower 3 4 10,
  .lower 3 4 11,
  .lower 3 5 9,
  .lower 3 5 10,
  .lower 3 5 11,
  .lower 3 6 9,
  .lower 3 6 10,
  .lower 3 6 11,
  .lower 3 7 10,
  .lower 3 7 11,
  .lower 3 8 10,
  .lower 3 8 11,
  .lower 3 10 0,
  .lower 3 10 1,
  .lower 3 10 2,
  .lower 3 11 0,
  .lower 3 12 9,
  .lower 3 12 10,
  .lower 3 12 11,
  .lower 4 9 5,
  .lower 4 9 6,
  .lower 4 9 7,
  .lower 4 9 8,
  .lower 4 9 11,
  .lower 4 10 5,
  .lower 4 10 6,
  .lower 4 10 7,
  .lower 4 10 8,
  .lower 4 10 11,
  .lower 4 11 5,
  .lower 4 11 6,
  .lower 4 11 7,
  .lower 4 11 8,
  .lower 4 12 9,
  .lower 4 12 10,
  .lower 4 12 11,
  .lower 5 9 6,
  .lower 5 9 8,
  .lower 5 10 4,
  .lower 5 10 6,
  .lower 5 10 7,
  .lower 5 10 8,
  .lower 5 11 4,
  .lower 5 11 6,
  .lower 5 11 7,
  .lower 5 11 8,
  .lower 5 12 9,
  .lower 5 12 10,
  .lower 5 12 11,
  .lower 6 10 4,
  .lower 6 10 5,
  .lower 6 10 7,
  .lower 6 10 8,
  .lower 6 11 4,
  .lower 6 11 5,
  .lower 6 11 7,
  .lower 6 11 8,
  .lower 6 12 9,
  .lower 6 12 10,
  .lower 6 12 11,
  .lower 7 10 4,
  .lower 7 10 5,
  .lower 7 10 6,
  .lower 7 10 8,
  .lower 7 10 11,
  .lower 7 11 4,
  .lower 7 11 5,
  .lower 7 11 6,
  .lower 7 11 8,
  .lower 7 12 9,
  .lower 7 12 10,
  .lower 7 12 11,
  .lower 8 10 4,
  .lower 8 10 5,
  .lower 8 10 6,
  .lower 8 10 7,
  .lower 8 11 4,
  .lower 8 11 5,
  .lower 8 11 6,
  .lower 8 11 7,
  .lower 8 12 9,
  .lower 8 12 10,
  .lower 8 12 11,
  .lower 9 11 1,
  .lower 9 11 2,
  .lower 9 11 3,
  .lower 9 11 8,
  .lower 9 12 10,
  .lower 9 12 11,
  .lower 10 11 4,
  .lower 10 11 5,
  .lower 10 12 9,
  .lower 10 12 11,
  .lower 11 12 9,
  .lower 11 12 10
]
graph_rup certificate (include_str "thirteen-certs/thirteen47.cnf") (include_str "thirteen-certs/thirteen47.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile47

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile48
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,2,2,2,2,2,5,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 0 9,
  .forbidden 0 12,
  .degree 0 [1,2,3,10],
  .degree 0 [1,2,3,11],
  .forbidden 1 9,
  .forbidden 1 12,
  .degree 1 [0,2,3,10],
  .degree 1 [0,2,3,11],
  .forbidden 2 9,
  .degree 2 [0,1,3,10],
  .degree 2 [0,1,3,11],
  .forbidden 4 12,
  .forbidden 5 12,
  .forbidden 6 12,
  .forbidden 7 12,
  .forbidden 8 12,
  .degree 9 [4,5,6,7,8],
  .degree 9 [4,5,6,7,12],
  .degree 9 [4,5,6,8,12],
  .degree 9 [4,5,7,8,12],
  .degree 9 [4,6,7,8,12],
  .degree 9 [5,6,7,8,12],
  .cap 9 [0,1,2],
  .cap 9 [0,1,10],
  .cap 9 [0,10,11],
  .visible 10 true,
  .visible 11 true,
  .degree 12 [9],
  .cap 12 [0,1,4,5,6,7,8],
  .lower 0 9 10,
  .lower 0 9 11,
  .lower 0 12 10,
  .lower 0 12 11,
  .lower 1 9 10,
  .lower 1 9 11,
  .lower 1 12 10,
  .lower 1 12 11,
  .lower 2 9 10,
  .lower 2 9 11,
  .lower 4 12 9,
  .lower 5 12 9,
  .lower 6 12 9,
  .lower 7 12 9,
  .lower 8 12 9,
  .lower 9 10 4,
  .lower 9 10 5,
  .lower 9 10 6,
  .lower 9 10 7,
  .lower 9 10 8,
  .lower 9 11 4,
  .lower 9 11 5,
  .lower 9 11 6,
  .lower 9 11 7,
  .lower 9 11 8
]
graph_rup certificate (include_str "thirteen-certs/thirteen48.cnf") (include_str "thirteen-certs/thirteen48.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile48

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile49
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,0,1,2,2,2,2,4,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .visible 4 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen49.cnf") (include_str "thirteen-certs/thirteen49.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile49
