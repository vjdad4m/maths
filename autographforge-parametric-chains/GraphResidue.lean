import ChainDegrees
import PageCounts

namespace TwinForcing
open SimpleGraph Finset

def degreeBag {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Multiset ℕ := (univ : Finset V).val.map (fun v => G.degree v)

def graphResidue {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ := Graffiti324.residueSequence ((degreeBag G).sort (· ≥ ·))

theorem graphResidue_of_list {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (l : List ℕ) (h : degreeBag G = (l : Multiset ℕ)) :
    graphResidue G = Graffiti324.residueSequence l := by
  apply ResiduePhases.residue_perm
  exact Quotient.exact ((Multiset.sort_eq _ _).trans h)

theorem page_degree_bag {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj] :
    degreeBag (@pageGraph n m H) =
      (degreeBag H).map (· + m) + Multiset.replicate (n*m) 2 := by
  simp only [degreeBag]
  change ((univ : Finset (Fin n × Bool)).val.map Sum.inl +
      (univ : Finset (Fin n × Fin m)).val.map Sum.inr).map _ = _
  simp only [Multiset.map_add,Multiset.map_map, Function.comp_def]
  have a : (fun x : Fin n × Bool => (@pageGraph n m H).degree (Sum.inl x)) =
      (fun x => H.degree x + m) := funext (fun ⟨i,b⟩ => hub_degree H i b)
  have b : (fun x : Fin n × Fin m => (@pageGraph n m H).degree (Sum.inr x)) =
      (fun _ => 2) := funext (fun ⟨i,j⟩ => page_degree H i j)
  rw [a,b,Multiset.map_const',← Finset.card_def]
  simp

/-- Shift every hub degree by the page count, then append one 2 per page.
    The result does not depend on how the hub vertices were enumerated. -/
theorem page_graph_residue {n m : ℕ} (H : SimpleGraph (Fin n × Bool))
    [DecidableRel H.Adj] (ds : List ℕ) (h : degreeBag H = (ds : Multiset ℕ)) :
    graphResidue (@pageGraph n m H) =
      Graffiti324.residueSequence (ds.map (· + m) ++ List.replicate (n*m) 2) := by
  apply graphResidue_of_list
  rw [page_degree_bag, h]
  rfl

/-- Matching-shaped hub degree multiset: two isolated hubs, all others degree one. -/
theorem fan_residue_of_hub_degrees (j : ℕ) (H : SimpleGraph (Fin (j+3) × Bool))
    [DecidableRel H.Adj]
    (h : degreeBag H = ((List.replicate (2*j+4) 1 ++ List.replicate 2 0 : List ℕ) : Multiset ℕ)) :
    graphResidue (@pageGraph (j+3) (4*j+9) H) = 2*j*j+11*j+14 := by
  rw [page_graph_residue H _ h, List.map_append, List.map_replicate, List.map_replicate]
  rw [show 1 + (4*j+9) = 4*j+10 by omega, Nat.zero_add]
  exact ResiduePhases.fan_chain_degree_list j

/-- Path-shaped hub degree multiset: two degree-one hubs, all others degree two. -/
theorem book_residue_of_hub_degrees (j : ℕ) (H : SimpleGraph (Fin (j+3) × Bool))
    [DecidableRel H.Adj]
    (h : degreeBag H = ((List.replicate (2*j+4) 2 ++ List.replicate 2 1 : List ℕ) : Multiset ℕ)) :
    graphResidue (@pageGraph (j+3) (4*j+9) H) = 2*j*j+12*j+17 := by
  rw [page_graph_residue H _ h, List.map_append, List.map_replicate, List.map_replicate]
  rw [show 2 + (4*j+9) = 4*j+11 by omega, show 1 + (4*j+9) = 4*j+10 by omega]
  exact ResiduePhases.book_chain_degree_list j

/-- Exact forcing excess over residue for any graph with the book hub degrees. -/
theorem book_forcing_excess (j : ℕ) (H : SimpleGraph (Fin (j+3) × Bool))
    [DecidableRel H.Adj]
    (h : degreeBag H = ((List.replicate (2*j+4) 2 ++ List.replicate 2 1 : List ℕ) : Multiset ℕ)) :
    StarCone.forcing (@pageGraph (j+3) (4*j+9) H) 2 =
      graphResidue (@pageGraph (j+3) (4*j+9) H) + (2*j*j+7*j+4) := by
  rw [page_two_forcing_exact (by omega), book_residue_of_hub_degrees j H h,
    show (4*j+9)-2 = 4*j+7 by omega]
  ring

/-- Exact forcing excess over residue for any graph with the fan hub degrees. -/
theorem fan_forcing_excess (j : ℕ) (H : SimpleGraph (Fin (j+3) × Bool))
    [DecidableRel H.Adj]
    (h : degreeBag H = ((List.replicate (2*j+4) 1 ++ List.replicate 2 0 : List ℕ) : Multiset ℕ)) :
    StarCone.forcing (@pageGraph (j+3) (4*j+9) H) 2 =
      graphResidue (@pageGraph (j+3) (4*j+9) H) + (2*j*j+8*j+7) := by
  rw [page_two_forcing_exact (by omega), fan_residue_of_hub_degrees j H h,
    show (4*j+9)-2 = 4*j+7 by omega]
  ring

#print axioms page_degree_bag
#print axioms page_graph_residue
#print axioms fan_residue_of_hub_degrees
#print axioms book_residue_of_hub_degrees
#print axioms book_forcing_excess
#print axioms fan_forcing_excess
end TwinForcing
