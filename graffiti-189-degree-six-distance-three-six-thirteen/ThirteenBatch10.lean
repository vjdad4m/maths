import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile10
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[1,1,1,1,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 9,
  .forbidden 0 10,
  .forbidden 0 11,
  .forbidden 0 12,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .forbidden 1 9,
  .forbidden 1 10,
  .forbidden 1 11,
  .forbidden 1 12,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .forbidden 2 9,
  .forbidden 2 10,
  .forbidden 2 11,
  .forbidden 2 12,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 9,
  .forbidden 3 10,
  .forbidden 3 11,
  .forbidden 3 12,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .forbidden 4 10,
  .forbidden 4 11,
  .forbidden 4 12,
  .forbidden 5 6,
  .forbidden 5 7,
  .forbidden 5 8,
  .forbidden 5 9,
  .forbidden 5 10,
  .forbidden 5 11,
  .forbidden 5 12,
  .link
]
graph_rup certificate (include_str "thirteen-certs/thirteen10.cnf") (include_str "thirteen-certs/thirteen10.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile10

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile11
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[1,1,1,1,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 4⟩
def rules : List Rule := [
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 9,
  .forbidden 0 10,
  .forbidden 0 11,
  .forbidden 0 12,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .forbidden 1 9,
  .forbidden 1 10,
  .forbidden 1 11,
  .forbidden 1 12,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .forbidden 2 9,
  .forbidden 2 10,
  .forbidden 2 11,
  .forbidden 2 12,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 9,
  .forbidden 3 10,
  .forbidden 3 11,
  .forbidden 3 12,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .forbidden 4 10,
  .forbidden 4 11,
  .forbidden 4 12,
  .forbidden 5 6,
  .forbidden 5 7,
  .forbidden 5 8,
  .forbidden 5 9,
  .forbidden 5 10,
  .forbidden 5 11,
  .forbidden 5 12,
  .link
]
graph_rup certificate (include_str "thirteen-certs/thirteen11.cnf") (include_str "thirteen-certs/thirteen11.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile11

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile12
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[1,1,1,1,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 6⟩
def rules : List Rule := [
  .forbidden 0 6,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 9,
  .forbidden 0 10,
  .forbidden 0 11,
  .forbidden 0 12,
  .forbidden 1 6,
  .forbidden 1 7,
  .forbidden 1 8,
  .forbidden 1 9,
  .forbidden 1 10,
  .forbidden 1 11,
  .forbidden 1 12,
  .forbidden 2 6,
  .forbidden 2 7,
  .forbidden 2 8,
  .forbidden 2 9,
  .forbidden 2 10,
  .forbidden 2 11,
  .forbidden 2 12,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 9,
  .forbidden 3 10,
  .forbidden 3 11,
  .forbidden 3 12,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .forbidden 4 10,
  .forbidden 4 11,
  .forbidden 4 12,
  .forbidden 5 6,
  .forbidden 5 7,
  .forbidden 5 8,
  .forbidden 5 9,
  .forbidden 5 10,
  .forbidden 5 11,
  .forbidden 5 12,
  .link
]
graph_rup certificate (include_str "thirteen-certs/thirteen12.cnf") (include_str "thirteen-certs/thirteen12.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile12

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile13
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[1,1,1,1,2,3,4,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 4⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 9,
  .visible 0 true,
  .degree 0 [1,2,3,5],
  .cap 0 [4,7,8,9],
  .degree 4 [],
  .degree 7 [8,9,10,11,12],
  .degree 8 [7,9,10,11,12],
  .degree 9 [7,8,10,11,12],
  .lower 0 4 5,
  .lower 0 7 6,
  .lower 0 8 6,
  .lower 0 9 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen13.cnf") (include_str "thirteen-certs/thirteen13.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile13

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile14
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,1,1,1,3,3,5,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 0 4,
  .degree 1 [0,2,3,5],
  .degree 1 [2,3,4,5],
  .forbidden 4 7,
  .degree 4 [1,2,3,5],
  .cap 4 [0,7],
  .degree 7 [8,9,10,11,12],
  .lower 0 4 1,
  .lower 4 7 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen14.cnf") (include_str "thirteen-certs/thirteen14.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile14

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile15
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,1,2,2,2,2,2,5,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 3 4,
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .visible 3 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen15.cnf") (include_str "thirteen-certs/thirteen15.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile15

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile16
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,1,1,2,2,2,2,2,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 3 5,
  .forbidden 3 6,
  .forbidden 3 7,
  .forbidden 3 8,
  .forbidden 3 9,
  .visible 3 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen16.cnf") (include_str "thirteen-certs/thirteen16.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile16

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile17
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,0,2,2,2,2,2,5,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
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
  .forbidden 3 9,
  .degree 3 [0,1,2,10],
  .degree 3 [0,1,2,11],
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
  .cap 9 [0,1,2,3],
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
  .lower 3 9 10,
  .lower 3 9 11,
  .lower 4 12 9,
  .lower 5 12 9,
  .lower 6 12 9,
  .lower 7 12 9,
  .lower 8 12 9
]
graph_rup certificate (include_str "thirteen-certs/thirteen17.cnf") (include_str "thirteen-certs/thirteen17.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile17

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile18
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,0,1,2,2,2,2,2,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
def rules : List Rule := [
  .forbidden 4 5,
  .forbidden 4 6,
  .forbidden 4 7,
  .forbidden 4 8,
  .forbidden 4 9,
  .visible 4 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen18.cnf") (include_str "thirteen-certs/thirteen18.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile18

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile19
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[0,0,0,0,0,2,2,2,2,2,6,6,7] : Array (Fin 8))[i.val]!,some 12⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen19.cnf") (include_str "thirteen-certs/thirteen19.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile19
