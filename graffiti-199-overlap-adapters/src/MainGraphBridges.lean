import CutAndOrder
import SameHalfSplice
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Preconnectedness of a smaller induced graph gives reachability within a larger one. -/
theorem reachable_of_preconnected_induce {s t : Set V} (inc : s ⊆ t)
    (connected : (G.induce s).Preconnected) {x y : t} (xs : x.val ∈ s) (ys : y.val ∈ s) :
    (G.induce t).Reachable x y :=
  (connected ⟨x.val,xs⟩ ⟨y.val,ys⟩).map (G.induceHomOfLE inc).toHom

/-- The main cut bridge is stated on induced subgraphs of the original graph.
After a cut of size three the second alternative removes the isolated vertex
from that induced graph. -/
theorem edgeReach_of_induced_singleton_cuts
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : V, s ∉ D ∧ (∀ t : V, t ∉ D → ¬ G.Adj s t) ∧
          (G.induce {v | v ∉ D ∧ v ≠ s}).Preconnected) :
    EdgeReachAfterSmallDeletion G := by
  refine edgeReach_of_singleton_cuts below ?_
  intro D size
  rcases three D size with connected|⟨s,hs,isolated,whole⟩
  · exact Or.inl connected
  · refine Or.inr ⟨⟨s,hs⟩,fun t => isolated t.val t.property,?_⟩
    intro x y notX notY
    exact reachable_of_preconnected_induce (fun _ hv => hv.1) whole
      ⟨x.property,fun e => notX (Subtype.ext e)⟩ ⟨y.property,fun e => notY (Subtype.ext e)⟩

/-- An adjacency chain with a specified first vertex yields a Mathlib walk
with exactly that chain as its support. -/
private theorem walk_with_support (a : V) (tail : List V) (chain : List.Chain G.Adj a tail) :
    ∃ b : V, ∃ w : G.Walk a b, w.support = a :: tail := by
  induction tail generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons c tail ih =>
    obtain ⟨ac,rest⟩ := List.chain_cons.mp chain
    obtain ⟨b,w,support⟩ := ih c rest
    exact ⟨b,.cons ac w,by simp [support]⟩

/-- The spanning list representation and Mathlib Hamiltonian paths are equivalent. -/
theorem pathOn_univ_iff_hamiltonian_walk [DecidableEq V] :
    Nonempty (PathOn G Set.univ) ↔ ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  constructor
  · rintro ⟨p⟩
    cases h : p.vertices with
    | nil => exact (p.nonempty h).elim
    | cons a tail =>
      have adjacent : List.Chain G.Adj a tail := by simpa [h] using p.chain
      obtain ⟨b,w,support⟩ := walk_with_support a tail adjacent
      have exactSupport : w.support = p.vertices := support.trans h.symm
      have path : w.IsPath := by
        rw [SimpleGraph.Walk.isPath_def,exactSupport]
        exact p.nodup
      exact ⟨a,b,w,path.isHamiltonian_of_mem (fun v => exactSupport.symm ▸ (p.covers v).mpr trivial)⟩
  · rintro ⟨a,b,w,ham⟩
    exact ⟨⟨w.support,w.support_ne_nil,w.chain'_adj_support,ham.isPath.support_nodup,
      fun v => ⟨fun _ => trivial,fun _ => ham.mem_support v⟩⟩⟩


/-- The finite-set independence bound also accepts the six-vertex
embedding formulation used by the structural reductions. -/
theorem noIndependentSix_iff_no_independent_embedding :
    NoIndependentSix G ↔ ¬ ∃ f : Fin 6 ↪ V, ∀ i j, ¬ G.Adj (f i) (f j) := by
  classical
  constructor
  · intro h
    rintro ⟨f,independent⟩
    let S := Finset.univ.map f
    have size : S.card = 6 := by simp [S]
    obtain ⟨_,x,_,y,adj⟩ := h S size
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp x
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp y
    exact independent i j adj
  · intro h S size
    by_contra no
    have count : Fintype.card {v // v ∈ S} = 6 := by simpa using size
    let e := (Fintype.equivFinOfCardEq count).symm
    let f : Fin 6 ↪ V := e.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
    exact h ⟨f,fun i j adj => no ⟨f i,(e i).property,f j,(e j).property,adj⟩⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- Degree three and an explicit three-element neighborhood are equivalent. -/
theorem degree_three_iff_three_neighbors (v : V) :
    G.degree v = 3 ↔ ∃ N : Finset V, N.card = 3 ∧ ∀ u : V, G.Adj v u ↔ u ∈ N := by
  constructor
  · intro h
    exact ⟨G.neighborFinset v, (G.card_neighborFinset_eq_degree v).trans h,
      fun u => (G.mem_neighborFinset v u).symm⟩
  · rintro ⟨N,hN,neighbors⟩
    have eq : G.neighborFinset v = N :=
      Finset.ext fun u => (G.mem_neighborFinset v u).trans (neighbors u)
    rw [← G.card_neighborFinset_eq_degree,eq,hN]

#print axioms reachable_of_preconnected_induce
#print axioms edgeReach_of_induced_singleton_cuts
#print axioms pathOn_univ_iff_hamiltonian_walk
#print axioms noIndependentSix_iff_no_independent_embedding
#print axioms degree_three_iff_three_neighbors

end Graffiti199Depleted
