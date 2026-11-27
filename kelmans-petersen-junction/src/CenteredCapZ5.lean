import RoutedLeafFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCyclicEquivalence
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The specified unordered pair of neighbors can form the two ends of
a factor tile centered at r. -/
def CenteredPair (G : SimpleGraph V) (r u w : V) : Prop :=
  u≠w ∧ G.Adj r u ∧ G.Adj r w ∧ Closed G (univ\{r,u,w})

/-- A forced leaf supplies a centered tile at its only neighbor; adapt the
complement factor monotonically to any graph containing the original edges. -/
theorem centered_pair_of_forced_leaf {G K : SimpleGraph V} {u r : V}
    (h : KelmansStarter.HasP3Factor K)
    (only : ∀ v,K.Adj u v → v=r)
    (lift : ∀ v w,K.Adj v w → G.Adj v w) :
    ∃ w,CenteredPair G r u w := by
  obtain ⟨P,tiles,disj,cov⟩ := h
  have part : Assemble.LocalPart K P univ := ⟨tiles,disj,cov⟩
  obtain ⟨T,TP,uT⟩ := mem_biUnion.mp (cov.symm ▸ mem_univ u)
  change u∈T at uT
  have t := tiles T TP
  obtain ⟨a,b,c,ab,ac,bc,e1,e2,shape⟩ := (Kelmans.tile_iff_path K T t.1).mp t.2
  have rest := change_edges (G:=G) (remove_tile part TP) (fun v _ w _ e=>lift v w e)
  rw [shape] at uT
  simp only [mem_insert,mem_singleton] at uT
  rcases uT with ua|ub|uc
  · have br := only b (ua.symm ▸ e1)
    refine ⟨c,ua.trans_ne ac,lift r u ?_,lift r c ?_,?_⟩
    · exact br ▸ ua.symm ▸ e1.symm
    · exact br ▸ e2
    · have eq : T={r,u,c} := by rw [shape,ua,←br,insert_comm]
      rw [eq] at rest
      exact ⟨_,rest⟩
  · have ar := only a (ub.symm ▸ e1.symm)
    have cr := only c (ub.symm ▸ e2)
    exact (ac (ar.trans cr.symm)).elim
  · have br := only b (uc.symm ▸ e2.symm)
    refine ⟨a,uc.trans_ne ac.symm,lift r u ?_,lift r a ?_,?_⟩
    · exact br ▸ uc.symm ▸ e2
    · exact br ▸ e1.symm
    · have eq : T={r,u,a} := by
        rw [shape,uc,←br]
        ext v
        simp only [mem_insert,mem_singleton]
        tauto
      rw [eq] at rest
      exact ⟨_,rest⟩

/-- In every qualifying cyclic-four cap, any one designated neighbor u
of r can be included in a centered pair at r, assuming ordinary
cyclic-four factors. Prescribe the leaf at u, not at r. -/
theorem cyclic4_centered_pair_at_neighbor
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V} [DecidableRel G.Adj]
    (dom : CyclicDomain G) {r u : V} (ru : G.Adj r u) :
    ∃ w,CenteredPair G r u w := by
  let N := G.neighborFinset u
  have rN : r∈N := (mem_neighborFinset G u r).mpr ru.symm
  have cN : N.card=3 := (card_neighborFinset_eq_degree G u).trans (dom.1.1 u)
  have c2 : (N.erase r).card=2 := by rw [card_erase_of_mem rN,cN]
  obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp c2
  have aN : a∈N.erase r := eq.symm ▸ mem_insert_self _ _
  have bN : b∈N.erase r := eq.symm ▸ mem_insert_of_mem (mem_singleton_self _)
  have ua : G.Adj u a := (mem_neighborFinset G u a).mp (mem_erase.mp aN).2
  have ub : G.Adj u b := (mem_neighborFinset G u b).mp (mem_erase.mp bN).2
  let K := avoidAt G u a b
  have only (w : V) (e : K.Adj u w) : w=r := by
    by_contra ne
    have h : w∈N.erase r := mem_erase.mpr ⟨ne,(mem_neighborFinset G u w).mpr e.1⟩
    rw [eq] at h
    rcases mem_insert.mp h with wa|wb
    · exact e.2 (Or.inl ⟨rfl,Or.inl wa⟩)
    · exact e.2 (Or.inl ⟨rfl,Or.inr (mem_singleton.mp wb)⟩)
  exact centered_pair_of_forced_leaf (cyclic4_factor_avoids_adjacent promise dom ua ub ab)
    only (fun _ _ e=>e.1)

/-- The ordinary cyclic-four statement implies the cyclic-four analogue
of Kelmans (z5): at every prescribed root there are at least two
different unordered viable pairs of ports. This does not assert all three. -/
theorem cyclic4_two_centered_pairs
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V} [DecidableRel G.Adj]
    (dom : CyclicDomain G) (r : V) :
    ∃ a b c d, CenteredPair G r a b ∧ CenteredPair G r c d ∧
      ({a,b}:Finset V)≠{c,d} := by
  let N := G.neighborFinset r
  have cN : N.card=3 := (card_neighborFinset_eq_degree G r).trans (dom.1.1 r)
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<N.card)
  obtain ⟨b,good⟩ := cyclic4_centered_pair_at_neighbor promise dom
    ((mem_neighborFinset G r a).mp ha)
  have c2 : ({a,b}:Finset V).card=2 := by simp [good.1]
  have exists_out : ¬ N ⊆ ({a,b}:Finset V) := by
    intro inc
    have h := card_le_card inc
    omega
  obtain ⟨c,hc,hout⟩ := not_subset.mp exists_out
  obtain ⟨d,more⟩ := cyclic4_centered_pair_at_neighbor promise dom
    ((mem_neighborFinset G r c).mp hc)
  exact ⟨a,b,c,d,good,more,fun eq=>hout (eq.symm ▸ mem_insert_self _ _)⟩

#print axioms centered_pair_of_forced_leaf
#print axioms cyclic4_centered_pair_at_neighbor
#print axioms cyclic4_two_centered_pairs
end KelmansCactus.AtomicBridge
