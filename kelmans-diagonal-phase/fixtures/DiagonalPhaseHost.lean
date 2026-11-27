import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.DiagonalPhaseFixture
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 24
def edgeTable : RemoteCutCertificate.Table 24 where
  edges := [(0,1),(0,6),(0,11),(1,2),(1,12),(2,3),(2,13),(3,4),(3,23),(4,5),(4,10),(5,6),(5,11),(6,7),(7,8),(7,12),(8,9),(8,14),(9,10),(9,15),(10,11),(12,18),(13,14),(13,19),(14,20),(15,16),(15,23),(16,17),(16,22),(17,18),(17,21),(18,19),(19,20),(20,21),(21,22),(22,23)]
  sorted := by decide
  nodup := by decide

abbrev core : SimpleGraph Core := edgeTable.graph
theorem core_cube : ∀ v,core.degree v=3 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem cut_valid :
    edgeTable.cert 4 1 [15,22,23,21,17,18,20,19,13,14,2,3,8,9,7,12,1,10,4,5,11,0,6] (RemoteCutCertificate.Table.base 16)=true := by
  have glue (v : Core) (vs : List Core) (shade : RemoteCutCertificate.Table.Shade 24)
      (red : edgeTable.cert 4 1 vs (RemoteCutCertificate.Table.update shade v false)=true)
      (blue : edgeTable.cert 4 1 vs (RemoteCutCertificate.Table.update shade v true)=true) :
      edgeTable.cert 4 1 (v::vs) shade=true := by
    simp [RemoteCutCertificate.Table.cert,red,blue]
  apply glue <;> apply glue <;> apply glue <;> decide

theorem core_cyclic_four : SmallTrivial core := edgeTable.cyclic_four cut_valid

def a : Port → Core
  | .inl (.inl false) => 4
  | .inl (.inl true) => 7
  | .inl (.inr false) => 2
  | .inl (.inr true) => 17
  | .inr false => 19
  | .inr true => 3
def b : Port → Core
  | .inl (.inl false) => 10
  | .inl (.inl true) => 12
  | .inl (.inr false) => 13
  | .inl (.inr true) => 18
  | .inr false => 20
  | .inr true => 23
def marks : Marks core Port where
  a := a
  b := b
  edge := by decide
  separated := by
    intro i j x
    have h : ∀ i j : Port, ∀ x : Core, x=a i∨x=b i → x=a j∨x=b j → i=j := by decide
    exact h i j x

abbrev board := marks.expanded
abbrev Board := Core ⊕ Port

instance : DecidableRel board.Adj := by
  rintro (x|i) (y|j)
  · change Decidable (core.Adj x y ∧ ¬∃ i : Port, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i))
    infer_instance
  · change Decidable (x=a j ∨ x=b j); infer_instance
  · change Decidable (y=a i ∨ y=b i); infer_instance
  · change Decidable False; infer_instance

def slot (i : Fin 6) : Port :=
  if i=0 then .inl (.inl false) else if i=1 then .inl (.inl true) else
  if i=2 then .inl (.inr false) else if i=3 then .inl (.inr true) else
  if i=4 then .inr false else .inr true
def decode (n : Nat) : Board := if n<24 then .inl (Fin.ofNat' 24 n) else .inr (slot (Fin.ofNat' 6 (n-24)))
def route (l : List Nat) : List Board := l.map decode

open RemoteT2CompletionTransfer (eraseEdge)
abbrev Host := RemoteSpacedPrismHandle.Host marks
abbrev HostV := RemoteSpacedPrismHandle.V4 Core
theorem host_cube : ∀ v, Host.degree v=3 := RemoteSpacedPrismHandle.cubic marks core_cube
theorem host_small : SmallTrivial Host :=
  RemoteSpacedPrismHandle.small_trivial marks core_cube core_cyclic_four
theorem host_three_connected : ThreeConnected Host :=
  SquareCap.three_connected_of_small_trivial _ host_cube (by decide) host_small
theorem exact_order : Fintype.card HostV=32 ∧ Fintype.card Board=30 := by decide
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
end KelmansCactus.AtomicBridge.DiagonalPhaseFixture
