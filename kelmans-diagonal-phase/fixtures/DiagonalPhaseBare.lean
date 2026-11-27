import DiagonalPhaseFixture
import RemoteMixedDissociation
import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.DiagonalPhaseBare
open SimpleGraph Finset
open SquareCap (HasFactor FactorOn)
open RemoteGapRunPacking (run_factor biUnion_factor)
open RemoteMixedDissociation (Sparse no_factor_if_sparse_large)

abbrev V := Fin 15

def along : List (V×V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),
   (10,13),(13,4),(7,14),(14,12),(12,1)]
def pairLinks (reverse : Bool) : List (V×V) :=
  if reverse then [(5,11),(6,0)] else [(5,6),(11,0)]
def oneSide (reverse side : Bool) : V×V :=
  if reverse then (if side then (11,0) else (5,6))
  else (if side then (5,11) else (0,6))
def edges (reverse : Bool) (extra : Option Bool) : List (V×V) :=
  along ++ pairLinks reverse ++ (extra.map (oneSide reverse)).toList

def Adj (k : Bool) (o : Option Bool) (x y : V) : Prop :=
  (x,y)∈edges k o ∨ (y,x)∈edges k o
instance (k : Bool) (o : Option Bool) (x y : V) : Decidable (Adj k o x y) := by
  unfold Adj
  infer_instance

def graph (reverse : Bool) (extra : Option Bool) : SimpleGraph V where
  Adj := Adj reverse extra
  symm := fun _ _ h=>h.symm
  loopless := by
    have h : ∀ x : V,¬Adj reverse extra x x := by
      cases reverse <;> cases extra with
      | none => decide
      | some s => cases s <;> decide
    exact h
instance (k : Bool) (o : Option Bool) : DecidableRel (graph k o).Adj :=
  fun _ _=>inferInstanceAs (Decidable (Adj k o _ _))

def sparse : Finset V := {0,2,3,5,6,8,9,11,12,13,14}

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem sparse_geometry (k : Bool) : Sparse (graph k none) sparse := by
  have cards : ∀ c∈sparse,(sparse.filter (fun x=>Adj k none c x)).card≤1 := by
    cases k <;> decide
  intro c hc x hx y hy cx cy
  exact Finset.card_le_one.mp (cards c hc) x (mem_filter.mpr ⟨hx,cx⟩) y (mem_filter.mpr ⟨hy,cy⟩)

theorem bare_fails (reverse : Bool) : ¬HasFactor (graph reverse none) :=
  no_factor_if_sparse_large (sparse_geometry reverse) (by decide)

def embed (x : V) : DiagonalPhaseFixture.Board :=
  DiagonalPhaseFixture.decode (if x.val=13 then 24 else if x.val=14 then 25 else x.val)
set_option maxRecDepth 15000 in
theorem embed_injective : Function.Injective embed := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem subgraph_of_genuine (k : Bool) (o : Option Bool) :
    ∀ x y,(graph k o).Adj x y → DiagonalPhaseFixture.pairUnion.Adj (embed x) (embed y) :=
  by
    cases k <;> cases o with
    | none => decide
    | some b => cases b <;> decide

theorem omitted_side (k s : Bool) :
    ¬ (graph k none).Adj (oneSide k s).1 (oneSide k s).2 ∧
    (graph k (some s)).Adj (oneSide k s).1 (oneSide k s).2 := by
  cases k <;> cases s <;> decide

private def pathCase (k s : Bool) (i : Fin 5) : List V :=
  (if k=s then ([[2,1,12],[3,4,5],[9,10,13],[6,0,11],[8,7,14]] : List (List V))
   else [[0,1,2],[7,14,12],[8,9,10],[3,4,13],[6,5,11]])[i.val]!

set_option maxRecDepth 10000 in
theorem either_side_repairs (reverse side : Bool) : HasFactor (graph reverse (some side)) := by
  have paths : ∀ i : Fin 5,(pathCase reverse side i).Nodup ∧
      (pathCase reverse side i).Chain' (graph reverse (some side)).Adj ∧
      3 ∣ (pathCase reverse side i).length := by cases reverse <;> cases side <;> decide
  have apart : ∀ i j : Fin 5,i≠j →
      Disjoint (pathCase reverse side i).toFinset (pathCase reverse side j).toFinset := by
    cases reverse <;> cases side <;> decide
  have complete : (univ : Finset (Fin 5)).biUnion (fun i=>(pathCase reverse side i).toFinset)=univ :=
    by cases reverse <;> cases side <;> decide
  change FactorOn (graph reverse (some side)) univ
  rw [←complete]
  exact biUnion_factor _ _ (fun i _=>run_factor _ (paths i).1 (paths i).2.1 (paths i).2.2)
    (fun i _ j _ n=>apart i j n)

#print axioms bare_fails
#print axioms subgraph_of_genuine
#print axioms either_side_repairs
end KelmansCactus.AtomicBridge.DiagonalPhaseBare
