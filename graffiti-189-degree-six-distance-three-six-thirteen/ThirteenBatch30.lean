import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile30
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,6,6,6,7,7,7,7] : Array (Fin 8))[i.val]!,some 9⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .degree 0 [1,2,7,8],
  .cap 0 [3,4,5,10],
  .degree 3 [4,5,7,8],
  .degree 4 [3,5,7,8],
  .degree 5 [3,4,7,8],
  .degree 10 [7,8,9,11,12],
  .lower 0 3 6,
  .lower 0 4 6,
  .lower 0 5 6,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen30.cnf") (include_str "thirteen-certs/thirteen30.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile30

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile31
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,none⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [3,4,5,10],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .lower 0 3 8,
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen31.cnf") (include_str "thirteen-certs/thirteen31.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile31

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile32
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 1 3,
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 10,
  .degree 1 [0,2,6,9],
  .degree 1 [0,2,8,9],
  .cap 1 [3,4,5,10],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .lower 1 3 8,
  .lower 1 4 8,
  .lower 1 5 8,
  .lower 1 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen32.cnf") (include_str "thirteen-certs/thirteen32.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile32

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile33
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 3⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .forbidden 0 11,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [4,5,10,11],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .degree 11 [7,8,9,10,12],
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 10 6,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen33.cnf") (include_str "thirteen-certs/thirteen33.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile33

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile34
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 6⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [3,4,5,10],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .lower 0 3 8,
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen34.cnf") (include_str "thirteen-certs/thirteen34.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile34

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile35
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 7⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [3,4,5,10],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .lower 0 3 8,
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen35.cnf") (include_str "thirteen-certs/thirteen35.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile35

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile36
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 8⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 10,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [3,4,5,10],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 10 [7,8,9,11,12],
  .lower 0 3 8,
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen36.cnf") (include_str "thirteen-certs/thirteen36.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile36

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile37
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,5,6,6,7,7,7] : Array (Fin 8))[i.val]!,some 10⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 11,
  .degree 0 [1,2,6,9],
  .degree 0 [1,2,8,9],
  .cap 0 [3,4,5,11],
  .degree 3 [4,5,7,9],
  .degree 4 [3,5,7,9],
  .degree 5 [3,4,7,9],
  .degree 11 [7,8,9,10,12],
  .lower 0 3 8,
  .lower 0 4 8,
  .lower 0 5 8,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen37.cnf") (include_str "thirteen-certs/thirteen37.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile37

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile38
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,none⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen38.cnf") (include_str "thirteen-certs/thirteen38.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile38

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile39
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,4,4,5,5,6,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 1 3,
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 11,
  .degree 1 [0,2,6,7],
  .degree 1 [0,2,7,10],
  .cap 1 [3,4,5,11],
  .degree 3 [4,5,8,9],
  .degree 4 [3,5,8,9],
  .degree 5 [3,4,8,9],
  .degree 11 [7,8,9,10,12],
  .lower 1 3 10,
  .lower 1 4 10,
  .lower 1 5 10,
  .lower 1 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen39.cnf") (include_str "thirteen-certs/thirteen39.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile39
