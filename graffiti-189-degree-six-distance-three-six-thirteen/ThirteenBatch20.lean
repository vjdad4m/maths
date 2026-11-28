import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile20
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[1,1,1,3,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,none⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen20.cnf") (include_str "thirteen-certs/thirteen20.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile20

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile21
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[1,1,1,3,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen21.cnf") (include_str "thirteen-certs/thirteen21.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile21

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile22
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[1,1,1,3,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 3⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen22.cnf") (include_str "thirteen-certs/thirteen22.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile22

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile23
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[1,1,1,3,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 6⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen23.cnf") (include_str "thirteen-certs/thirteen23.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile23

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile24
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[1,1,1,2,3,3,4,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 3⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 7,
  .forbidden 0 8,
  .degree 0 [1,2,4,5],
  .degree 0 [1,2,5,6],
  .cap 0 [3,7,8],
  .degree 4 [0,1,2,5],
  .degree 7 [8,9,10,11,12],
  .degree 8 [7,9,10,11,12],
  .lower 0 3 4,
  .lower 0 7 6,
  .lower 0 8 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen24.cnf") (include_str "thirteen-certs/thirteen24.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile24

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile25
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,1,1,3,3,3,5,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 0 3,
  .degree 1 [0,2,4,5],
  .degree 1 [2,3,4,5],
  .forbidden 3 7,
  .forbidden 3 8,
  .degree 3 [1,2,4,5],
  .cap 3 [0,7,8],
  .degree 7 [8,9,10,11,12],
  .degree 8 [7,9,10,11,12],
  .lower 0 3 1,
  .lower 3 7 6,
  .lower 3 8 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen25.cnf") (include_str "thirteen-certs/thirteen25.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile25

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile26
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,6,6,6,7,7,7,7] : Array (Fin 8))[i.val]!,none⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 9,
  .degree 0 [1,2,7,8],
  .cap 0 [3,4,5,9],
  .degree 3 [4,5,7,8],
  .degree 4 [3,5,7,8],
  .degree 5 [3,4,7,8],
  .degree 9 [7,8,10,11,12],
  .lower 0 3 6,
  .lower 0 4 6,
  .lower 0 5 6,
  .lower 0 9 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen26.cnf") (include_str "thirteen-certs/thirteen26.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile26

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile27
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,6,6,6,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
def rules : List Rule := [
  .forbidden 1 3,
  .forbidden 1 4,
  .forbidden 1 5,
  .forbidden 1 9,
  .degree 1 [0,2,7,8],
  .cap 1 [3,4,5,9],
  .degree 3 [4,5,7,8],
  .degree 4 [3,5,7,8],
  .degree 5 [3,4,7,8],
  .degree 9 [7,8,10,11,12],
  .lower 1 3 6,
  .lower 1 4 6,
  .lower 1 5 6,
  .lower 1 9 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen27.cnf") (include_str "thirteen-certs/thirteen27.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile27

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile28
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,6,6,6,7,7,7,7] : Array (Fin 8))[i.val]!,some 3⟩
def rules : List Rule := [
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 9,
  .forbidden 0 10,
  .degree 0 [1,2,7,8],
  .cap 0 [4,5,9,10],
  .degree 4 [3,5,7,8],
  .degree 5 [3,4,7,8],
  .degree 9 [7,8,10,11,12],
  .degree 10 [7,8,9,11,12],
  .lower 0 4 6,
  .lower 0 5 6,
  .lower 0 9 6,
  .lower 0 10 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen28.cnf") (include_str "thirteen-certs/thirteen28.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile28

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile29
open SimpleGraph
def profile : Profile := ⟨3,3,fun i=> (#[0,0,0,2,2,2,6,6,6,7,7,7,7] : Array (Fin 8))[i.val]!,some 6⟩
def rules : List Rule := [
  .forbidden 0 3,
  .forbidden 0 4,
  .forbidden 0 5,
  .forbidden 0 9,
  .degree 0 [1,2,7,8],
  .cap 0 [3,4,5,9],
  .degree 3 [4,5,7,8],
  .degree 4 [3,5,7,8],
  .degree 5 [3,4,7,8],
  .degree 9 [7,8,10,11,12],
  .lower 0 3 6,
  .lower 0 4 6,
  .lower 0 5 6,
  .lower 0 9 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen29.cnf") (include_str "thirteen-certs/thirteen29.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile29
