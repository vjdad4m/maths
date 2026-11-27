import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 48
private def edgeList : List (Core×Core) := [(0,1),(0,9),(0,35),(1,2),(1,7),(2,3),(2,8),(3,4),(3,37),(4,5),(4,39),(5,6),(5,38),(6,7),(6,40),(7,8),(8,9),(9,10),(10,11),(10,13),(11,12),(11,41),(12,13),(12,15),(13,14),(14,15),(14,17),(15,16),(16,17),(16,43),(17,18),(18,19),(18,36),(19,20),(19,22),(20,21),(20,44),(21,22),(21,24),(22,23),(23,24),(23,26),(24,25),(25,26),(25,45),(26,27),(27,28),(27,36),(28,29),(28,31),(29,30),(29,34),(30,31),(30,46),(31,32),(32,33),(32,35),(33,34),(33,47),(34,35),(36,43),(37,38),(37,45),(38,41),(39,40),(39,44),(40,47),(41,42),(42,43),(42,46),(44,45),(46,47)]
private def edgeCode (e : Core×Core) := 48*e.1.val+e.2.val

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def edgeTable : RemoteCutCertificate.Table 48 where
  edges := edgeList
  sorted := by
    have yes : edgeList.all (fun e=>decide (e.1<e.2))=true := by decide
    intro a b m
    exact of_decide_eq_true (List.all_eq_true.mp yes (a,b) m)
  nodup := by
    have yes : (edgeList.map edgeCode).Chain' (fun x y : Nat => x<y) := by decide
    exact List.Nodup.of_map edgeCode ((List.chain'_iff_pairwise.mp yes).imp Nat.ne_of_lt)

abbrev core : SimpleGraph Core := edgeTable.graph
private def edgeNeighbors (v : Core) : Finset Core :=
  ((edgeTable.edges.filter (fun e=>decide (e.1=v ∨ e.2=v))).map
    (fun e=>if e.1=v then e.2 else e.1)).toFinset

private theorem edgeNeighbors_eq (v : Core) : edgeNeighbors v = core.neighborFinset v := by
  ext u
  constructor
  · intro mem
    obtain ⟨⟨a,b⟩,p,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
    obtain ⟨edge,pos⟩:=List.mem_filter.mp p
    apply (core.mem_neighborFinset _ _).mpr
    rcases of_decide_eq_true pos with q|q
    · change a=v at q
      subst a
      have r : b=u := by simpa using eq
      exact Or.inl (r ▸ edge)
    · change b=v at q
      subst b
      have ne : a≠v := (edgeTable.sorted a v edge).ne
      have r : a=u := by simpa [ne] using eq
      exact Or.inr (r ▸ edge)
  · intro mem
    have ad := (core.mem_neighborFinset _ _).mp mem
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    rcases ad with e|e
    · exact ⟨(v,u),List.mem_filter.mpr ⟨e,decide_eq_true (Or.inl rfl)⟩,by simp⟩
    · have ne : u≠v := (edgeTable.sorted u v e).ne
      exact ⟨(u,v),List.mem_filter.mpr ⟨e,decide_eq_true (Or.inr rfl)⟩,by simp [ne]⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem core_cube : ∀ v,core.degree v=3 := by
  have count (v : Core) : (edgeNeighbors v).card=3 := by
    fin_cases v <;> decide
  intro v
  rw [←core.card_neighborFinset_eq_degree,←edgeNeighbors_eq]
  exact count v


def a : Port → Core
  | .inl (.inl false) => 0
  | .inl (.inl true) => 18
  | .inl (.inr false) => 25
  | .inl (.inr true) => 30
  | .inr false => 37
  | .inr true => 39
def b : Port → Core
  | .inl (.inl false) => 9
  | .inl (.inl true) => 36
  | .inl (.inr false) => 45
  | .inl (.inr true) => 46
  | .inr false => 38
  | .inr true => 40
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
def decode (n : Nat) : Board := if n<48 then .inl (Fin.ofNat' 48 n) else .inr (slot (Fin.ofNat' 6 (n-48)))
def route (l : List Nat) : List Board := l.map decode


#print axioms core_cube
end KelmansCactus.AtomicBridge.DiagonalMixed54
