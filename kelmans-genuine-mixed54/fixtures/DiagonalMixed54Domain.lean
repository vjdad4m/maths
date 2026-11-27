import DiagonalMixed54Core
import DiagonalMixed54HandleChain4

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (SmallTrivial ThreeConnected NontrivialSide boundary)
open RemoteSpacedPrismHandle (Port pole endThird embed)
open DiagonalMixed54HandleChain (T48 cert48)

private def forwardLabel (x : Core) : Core :=
  ([0,1,2,3,4,9,5,37,6,10,7,8,11,27,12,13,14,15,16,17,18,36,19,22,20,21,23,24,25,26,28,29,30,31,32,33,34,35,38,41,39,40,42,43,44,45,46,47] : List Core)[x.val]!
private def inverseLabel (x : Core) : Core :=
  ([0,1,2,3,4,6,8,10,11,5,9,12,14,15,16,17,18,19,20,22,24,25,23,26,27,28,29,13,30,31,32,33,34,35,36,37,21,7,38,40,41,39,42,43,44,45,46,47] : List Core)[x.val]!
private def permute : Core ≃ Core where
  toFun := forwardLabel
  invFun := inverseLabel
  left_inv := by
    have h : ∀ x : Core,inverseLabel (forwardLabel x)=x := by decide
    exact h
  right_inv := by
    have h : ∀ x : Core,forwardLabel (inverseLabel x)=x := by decide
    exact h

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private def construction_iso : T48.graph ≃g core := by
  apply RemoteNumericHandleChecks.relabel T48 edgeTable permute
  · intro e he
    have check : T48.edges.all (fun a=>decide (core.Adj (forwardLabel a.1) (forwardLabel a.2)))=true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp check e he)
  · intro e he
    have check : edgeTable.edges.all (fun a=>decide (T48.graph.Adj (inverseLabel a.1) (inverseLabel a.2)))=true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp check e he)

theorem core_cyclic_four : SmallTrivial core :=
  RemoteFourCutTransport.transfer_small construction_iso.symm cert48.2

open RemoteT2CompletionTransfer (eraseEdge)
abbrev Host := RemoteSpacedPrismHandle.Host marks
abbrev HostV := RemoteSpacedPrismHandle.V4 Core
theorem host_cube : ∀ v, Host.degree v=3 := RemoteSpacedPrismHandle.cubic marks core_cube
theorem host_small : SmallTrivial Host :=
  RemoteSpacedPrismHandle.small_trivial marks core_cube core_cyclic_four
theorem host_three_connected : ThreeConnected Host :=
  SquareCap.three_connected_of_small_trivial _ host_cube (by decide) host_small
theorem exact_order : Fintype.card HostV=56 ∧ Fintype.card Board=54 := by decide
theorem exact_remote :
    Host.Adj (pole false) (pole true) ∧ Host.Adj (endThird false) (endThird true) ∧
    RemoteT2Scope.Remote Host (pole false) (endThird false) (endThird true) :=
  ⟨RemoteSpacedPrismHandle.pole_join marks,RemoteSpacedPrismHandle.remote_edge marks,
    RemoteSpacedPrismHandle.remote marks⟩
theorem exact_board :
    Function.Injective (embed (V:=Core)) ∧
    (∀ x : HostV,x≠pole false∧x≠pole true ↔ ∃ y : Board,embed y=x) ∧
    (∀ a b : Board,board.Adj a b ↔
      (eraseEdge Host (endThird false) (endThird true)).Adj (embed a) (embed b)) :=
  ⟨RemoteSpacedPrismHandle.embed_injective,RemoteSpacedPrismHandle.embed_range,
    RemoteSpacedPrismHandle.exact_survivor marks⟩

theorem wide (c : Board→Bool) (h : ∀ b,NontrivialSide c b) :
    3≤(boundary board c).card :=
  RemoteSpacedPrismWidth.expanded_wide marks core_cube core_cyclic_four c h

#print axioms host_three_connected
#print axioms exact_board
#print axioms wide
end KelmansCactus.AtomicBridge.DiagonalMixed54
