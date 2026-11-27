import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace GraphPathLift
open SimpleGraph

variable {V W : Type*}

/-- A Mathlib path that visits every vertex. -/
def HasSpanningPath (G : SimpleGraph V) : Prop :=
  ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v, v ∈ p.support

/-- Precisely the consecutive pairs of this vertex sequence, in list order. -/
def edgePairs : List V → List (V × V)
  | a :: (b :: t) => (a,b) :: edgePairs (b::t)
  | _ => []

@[simp] theorem edgePairs_singleton (a : V) : edgePairs [a] = [] := rfl

theorem walk_of_list (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ edgePairs (a::l), G.Adj e.1 e.2) :
    ∃ b, ∃ p : G.Walk a b, p.support = a::l := by
  induction l generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b t ih =>
    have hab : G.Adj a b := h (a,b) (by simp [edgePairs])
    have ht : ∀ e ∈ edgePairs (b::t), G.Adj e.1 e.2 := by
      intro e he
      exact h e (by simp [edgePairs,he])
    obtain ⟨c,p,hp⟩ := ih b ht
    exact ⟨c,.cons hab p,by simp [hp]⟩

theorem spanningPath_of_list (G : SimpleGraph V) (l : List V) (hn : l ≠ [])
    (hd : l.Nodup) (hc : ∀ v, v ∈ l) (h : ∀ e ∈ edgePairs l, G.Adj e.1 e.2) :
    HasSpanningPath G := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons a t =>
    obtain ⟨b,p,hp⟩ := walk_of_list G a t h
    exact ⟨a,b,p,Walk.IsPath.mk' (hp.symm ▸ hd),hp.symm ▸ hc⟩

theorem hasSpanningPath_map (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hf : Function.Bijective f) (h : HasSpanningPath G) :
    HasSpanningPath H := by
  obtain ⟨a,b,p,hp,hmem⟩ := h
  refine ⟨f a,f b,p.map f,(Walk.map_isPath_iff_of_injective hf.injective).mpr hp,?_⟩
  intro w
  obtain ⟨v,rfl⟩ := hf.surjective w
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨v,hmem v,rfl⟩

theorem hasSpanningPath_iso_iff (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) :
    HasSpanningPath G ↔ HasSpanningPath H :=
  ⟨hasSpanningPath_map G H f.toHom f.bijective,
   hasSpanningPath_map H G f.symm.toHom f.symm.bijective⟩

/-- Boolean adjacency matrix, with a value for every ordered pair. -/
def adjBit (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) : Bool :=
  decide (G.Adj e.1 e.2)

/-- DIMACS cage variable order: (0,1), (0,2), ..., (1,2), (1,3), ... . -/
def edgeTable (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j).map fun j => (i,j)

/-- Assign the one-based edge IDs in the cage to the graph adjacency bits.
Outside the edge-ID range this returns false; cage auxiliary variables may
be assigned independently. -/
def edgeBit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Bool :=
  (((edgeTable n)[k-1]?).map (adjBit G)).getD false

def canonical {n : ℕ} (e : Fin n × Fin n) : Fin n × Fin n :=
  if e.1 ≤ e.2 then e else (e.2,e.1)

@[simp] theorem adjBit_eq_true (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) :
    adjBit G e = true ↔ G.Adj e.1 e.2 := by simp [adjBit]

theorem edgeBit_at {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k : ℕ} {e : Fin n × Fin n} (hk : (edgeTable n)[k-1]? = some e) :
    edgeBit G k = adjBit G e := by simp [edgeBit,hk]

theorem adjBit_canonical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin n × Fin n) : adjBit G (canonical e) = adjBit G e := by
  unfold canonical
  split
  · rfl
  · simp [adjBit,G.adj_comm]

/-- A literal clause excluding a certified permutation as a spanning path.
The only verification on the list is nonemptiness, pairwise distinctness,
coverage, and the graph-free table lookup certificate for its edge IDs. -/
theorem path_clause {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : ¬ HasSpanningPath G) (l : List (Fin n)) (hl : l ≠ [])
    (hd : l.Nodup) (hc : ∀ v, v ∈ l) (ids : List ℕ)
    (hids : ∀ e ∈ edgePairs l, ∃ k ∈ ids, (edgeTable n)[k-1]? = some (canonical e))
    (htrue : ∀ k ∈ ids, edgeBit G k = true) : False := by
  apply hn
  apply spanningPath_of_list G l hl hd hc
  intro e he
  obtain ⟨k,hk,he'⟩ := hids e he
  have h := htrue k hk
  rw [edgeBit_at G he',adjBit_canonical] at h
  exact (adjBit_eq_true G e).mp h

/-- A path clause under an arbitrary full (edge and auxiliary) SAT valuation.
The table certificate covers all consecutive pairs; graph edges can be supplied
by literals inside the clause or already-fixed true premises (such as the root
edges in a BFS cage). -/
theorem path_clause_valuation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : ¬ HasSpanningPath G) (l : List (Fin n)) (hl : l ≠ [])
    (hd : l.Nodup) (hc : ∀ v, v ∈ l) (ids : List ℕ)
    (hids : ∀ e ∈ edgePairs l, ∃ k ∈ ids, (edgeTable n)[k-1]? = some (canonical e))
    (x : ℕ → Bool) (clause : List (ℕ × Bool))
    (hx : ∀ k ∈ ids, x k = edgeBit G k)
    (hcover : ∀ k ∈ ids, x k = true ∨ (k,true) ∈ clause)
    (hfalsified : ∀ lit ∈ clause, x lit.1 = lit.2) : False := by
  apply path_clause G hn l hl hd hc ids hids
  intro k hk
  rw [← hx k hk]
  rcases hcover k hk with h | h
  · exact h
  · exact hfalsified (k,true) h

#print axioms path_clause
#print axioms path_clause_valuation
#print axioms hasSpanningPath_iso_iff
end GraphPathLift
