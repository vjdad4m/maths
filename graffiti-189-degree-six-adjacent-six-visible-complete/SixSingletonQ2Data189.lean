import SixSingletonQ1TemplateWalk189
import SixSingletonFiveAllLowCert189
import TwoCutDistanceCaps189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open SimpleGraph SimpleGraph.Walk Finset Sat Graffiti189Ore ArticulationPair
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

abbrev Vertex := Fin 16

def fixedEdges : List (Vertex × Vertex) := [(0,6),(1,7),(2,7),(3,6),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7),(6,8),(7,8)]
def variableEdges : List (Vertex × Vertex) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,10),(0,14),(0,15),(1,2),(1,3),(1,4),(1,5),(1,11),(1,12),(1,13),(1,14),(1,15),(2,3),(2,4),(2,5),(2,11),(2,12),(2,13),(2,14),(2,15),(3,4),(3,5),(3,14),(3,15),(4,5),(4,14),(4,15),(5,14),(5,15),(9,10),(9,11),(9,12),(9,13),(9,14),(9,15),(10,11),(10,12),(10,13),(10,14),(10,15),(11,12),(11,13),(11,14),(11,15),(12,13),(12,14),(12,15),(13,14),(13,15),(14,15)]
def allPairs : List (Vertex × Vertex) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(4,15),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(5,13),(5,14),(5,15),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(6,13),(6,14),(6,15),(7,8),(7,9),(7,10),(7,11),(7,12),(7,13),(7,14),(7,15),(8,9),(8,10),(8,11),(8,12),(8,13),(8,14),(8,15),(9,10),(9,11),(9,12),(9,13),(9,14),(9,15),(10,11),(10,12),(10,13),(10,14),(10,15),(11,12),(11,13),(11,14),(11,15),(12,13),(12,14),(12,15),(13,14),(13,15),(14,15)]

inductive Tag
  | forb
  | fixed
  | variable (i : Nat)
  deriving DecidableEq

inductive Atom
  | edge (u v : Vertex)
  | atTwo (u v : Vertex)
  deriving DecidableEq

def canonical (u v : Vertex) : Vertex × Vertex := if u ≤ v then (u,v) else (v,u)

def tag (u v : Vertex) : Tag :=
  let p := canonical u v
  if p∈fixedEdges then .fixed else
    let i := variableEdges.idxOf p
    if i<56 then .variable i else .forb

def two (u v : Vertex) : ℕ := 56 + allPairs.idxOf (canonical u v)

def atomList : List Atom :=
  variableEdges.map (fun (u,v)=>.edge u v) ++ allPairs.map (fun (u,v)=>.atTwo u v)

def value (G : SimpleGraph Vertex) : Valuation := fun i=>
  match atomList[i]? with
  | some (.edge u v) => G.Adj u v
  | some (.atTwo u v) => G.dist u v=2
  | none=>False

private def edgeCompatible (u v : Vertex) : Prop :=
  match tag u v with
  | .variable i => atomList[i]? = some (.edge u v) ∨ atomList[i]? = some (.edge v u)
  | _=>True

private instance (u v : Vertex) : Decidable (edgeCompatible u v) := by
  unfold edgeCompatible
  split <;> infer_instance

private theorem edge_spec_index : ∀ u v : Vertex,edgeCompatible u v := by decide

private theorem two_spec_index :
    ∀ u v : Vertex,u≠v →
      atomList[two u v]? = some (.atTwo u v) ∨ atomList[two u v]? = some (.atTwo v u) := by decide

theorem edge_atom (G : SimpleGraph Vertex) {u v : Vertex} {i : ℕ}
    (h : tag u v=.variable i) : value G i ↔ G.Adj u v := by
  have e := edge_spec_index u v
  unfold edgeCompatible at e
  rw [h] at e
  rcases e with e|e
  · simp [value,e]
  simp [value,e,adj_comm]

theorem two_atom (G : SimpleGraph Vertex) {u v : Vertex} (ne : u≠v) :
    value G (two u v) ↔ G.dist u v=2 := by
  rcases two_spec_index u v ne with e|e
  · simp [value,e]
  simp [value,e,dist_comm]

def neighborsAllowed (u : Vertex) : Finset Vertex := univ.filter (fun v=>tag u v≠.forb)

structure Data (G : SimpleGraph Vertex) [DecidableRel G.Adj] : Prop where
  allowed : ∀ u v, G.Adj u v → tag u v≠.forb
  fixed : ∀ u v,tag u v=.fixed → G.Adj u v
  degree : ∀ u : Vertex,u≠8 → 6≤G.degree u
  cap : ∀ u,(EvenFrom G u).card≤7
  l9 : G.Adj 0 9
  l10 : G.Adj 0 10
  r11 : G.Adj 1 11 ∨ G.Adj 2 11
  r12 : G.Adj 1 12 ∨ G.Adj 2 12
  r13 : G.Adj 1 13 ∨ G.Adj 2 13
  b14a : ∃ p∈({0,3,4,5}:Finset Vertex),G.Adj p 14
  b15a : ∃ p∈({0,3,4,5}:Finset Vertex),G.Adj p 15
  b14b : ∃ p∈({1,2,3,4,5}:Finset Vertex),G.Adj p 14
  b15b : ∃ p∈({1,2,3,4,5}:Finset Vertex),G.Adj p 15

end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
