import SixThirteenSat189
import GraphRup189

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile00
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[1,1,1,1,1,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,none⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen00.cnf") (include_str "thirteen-certs/thirteen00.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile00

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile01
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[1,1,1,1,1,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 0⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen01.cnf") (include_str "thirteen-certs/thirteen01.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile01

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile02
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[1,1,1,1,1,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen02.cnf") (include_str "thirteen-certs/thirteen02.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile02

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile03
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[1,1,1,1,1,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 6⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen03.cnf") (include_str "thirteen-certs/thirteen03.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile03

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile04
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[0,1,1,1,1,2,6,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 1 5,
  .visible 1 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen04.cnf") (include_str "thirteen-certs/thirteen04.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile04

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile05
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[0,0,1,1,1,2,6,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 2 5,
  .visible 2 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen05.cnf") (include_str "thirteen-certs/thirteen05.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile05

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile06
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[0,0,0,1,1,2,6,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 3 5,
  .visible 3 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen06.cnf") (include_str "thirteen-certs/thirteen06.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile06

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile07
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[0,0,0,0,1,2,6,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 4 5,
  .visible 4 true
]
graph_rup certificate (include_str "thirteen-certs/thirteen07.cnf") (include_str "thirteen-certs/thirteen07.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile07

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile08
open SimpleGraph
def profile : Profile := ⟨1,5,fun i=> (#[0,0,0,0,0,2,6,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,some 5⟩
def rules : List Rule := [
  .forbidden 0 5,
  .forbidden 0 7,
  .forbidden 0 8,
  .forbidden 0 9,
  .forbidden 0 10,
  .forbidden 0 11,
  .degree 0 [1,2,3,4],
  .cap 0 [5,7,8,9,10,11],
  .degree 5 [],
  .degree 7 [8,9,10,11,12],
  .degree 8 [7,9,10,11,12],
  .degree 9 [7,8,10,11,12],
  .degree 10 [7,8,9,11,12],
  .degree 11 [7,8,9,10,12],
  .lower 0 5 6,
  .lower 0 7 6,
  .lower 0 8 6,
  .lower 0 9 6,
  .lower 0 10 6,
  .lower 0 11 6
]
graph_rup certificate (include_str "thirteen-certs/thirteen08.cnf") (include_str "thirteen-certs/thirteen08.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile08

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
namespace Graffiti189LongestPath.SixThirteenSat.ThirteenProfile09
open SimpleGraph
def profile : Profile := ⟨2,4,fun i=> (#[1,1,1,1,3,3,7,7,7,7,7,7,7] : Array (Fin 8))[i.val]!,none⟩
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
graph_rup certificate (include_str "thirteen-certs/thirteen09.cnf") (include_str "thirteen-certs/thirteen09.lrat")
theorem impossible {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model profile G Near) : False := by
  have eq : certificate.formula = rules.map (Rule.clause profile) := rfl
  have wf : rules.all (fun r=>decide (r.WF profile)) = true := by decide
  have pr := certificate
  rw [eq] at pr
  exact transfer M rules (fun r hr => of_decide_eq_true (List.all_eq_true.mp wf r hr)) pr
#print axioms impossible
end Graffiti189LongestPath.SixThirteenSat.ThirteenProfile09
