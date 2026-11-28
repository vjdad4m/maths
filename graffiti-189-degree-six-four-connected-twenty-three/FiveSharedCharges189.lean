import FiveCheapBudget189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.FiveCheapBudget
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000

namespace Graffiti189LongestPath.FiveSharedCharges
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H : Finset V} {i j s t : ℕ}

theorem not_adj_outside_allowed (A : PairData p H x y i j s t) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
    {m v : ℕ} (mij : m=i ∨ m=j) (hv : v≤17) (hn : v∉allowed i j s t) :
    ¬ G.Adj (p.getVert m) (p.getVert v) := by
  intro ed
  rcases cheap_neighbors A hc hp cap mij ed with eq|mm
  · exact A.off _ A.xH (eq ▸ p.getVert_mem_support v)
  obtain ⟨k,km,ke⟩ := mem_image.mp mm
  have eq := hp.1.getVert_injOn
    (A.pathLen.symm ▸ index_bound A km) (A.pathLen.symm ▸ hv) ke
  exact hn (eq ▸ km)

theorem shared_indices (A : PairData p H x y i j s t) {m k : ℕ}
    (mij : m=i ∨ m=j) (kst : k=s ∨ k=t) :
    0<k ∧ k<17 ∧ m≤17 ∧ m≠k-1 ∧ m≠k+1 ∧
      k-1∉allowed i j s t ∧ k+1∉allowed i j s t := by
  rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;>
    rcases mij with rfl|rfl <;> rcases kst with rfl|rfl <;> decide

theorem shared_charges (A : PairData p H x y i j s t) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
    {m k : ℕ} (mij : m=i ∨ m=j) (kst : k=s ∨ k=t)
    (ed : G.Adj (p.getVert m) (p.getVert k)) :
    p.getVert (k-1)∈residual G H (p.getVert m) ∧
      p.getVert (k+1)∈residual G H (p.getVert m) := by
  obtain ⟨kp,kl,ml,ne1,ne2,n1,n2⟩ := shared_indices A mij kst
  have left : G.Adj (p.getVert k) (p.getVert (k-1)) := by
    have z := (adjacency_on_spine A (k-1) (by omega)).symm
    rwa [show k-1+1=k by omega] at z
  exact ⟨charge_on_spine A hc (distinct_get A hp ml (by omega) ne1) ed left
      (not_adj_outside_allowed A hc hp cap mij (by omega) n1),
    charge_on_spine A hc (distinct_get A hp ml (by omega) ne2) ed
      (adjacency_on_spine A k kl) (not_adj_outside_allowed A hc hp cap mij (by omega) n2)⟩

theorem exhaust_shared (A : PairData p H x y i j s t) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
    {m k : ℕ} (mij : m=i ∨ m=j) (kst : k=s ∨ k=t)
    (ed : G.Adj (p.getVert m) (p.getVert k)) :
    residual G H (p.getVert m) = {p.getVert (k-1),p.getVert (k+1)} := by
  classical
  obtain ⟨_,kl,_,_,_,_,_⟩ := shared_indices A mij kst
  obtain ⟨q,r⟩ := shared_charges A hc hp cap mij kst ed
  have hc2 : ({p.getVert (k-1),p.getVert (k+1)} : Finset V).card=2 := by
    simp [distinct_get A hp (show k-1≤17 by omega) (show k+1≤17 by omega) (show k-1≠k+1 by omega)]
  refine (eq_of_subset_of_card_le ?_ ?_).symm
  · intro u hu
    rcases mem_insert.mp hu with e|e
    · exact e.symm ▸ q
    · exact (mem_singleton.mp e).symm ▸ r
  · rw [hc2]
    exact residual_cap A hc hp cap mij

#print axioms shared_charges
#print axioms exhaust_shared
end Graffiti189LongestPath.FiveSharedCharges
