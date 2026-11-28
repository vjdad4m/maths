import FiveSharedCharges189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FiveCheapBudget Graffiti189LongestPath.FiveSharedCharges
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000

namespace Graffiti189LongestPath.FiveEdgeBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H U : Finset V} {i j s t m : ℕ}

theorem at_endpoint (A : PairData p H x y i j s t) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
    (mij : m=i ∨ m=j) (e : V) (ep : G.Adj (p.getVert m) e)
    (eH : ∀ v∈H, ¬G.Adj e v) (um : p.getVert m∈U) (u3 : U.card≤3)
    (covers : ∀ v, G.Adj e v → G.Adj (p.getVert m) v →
      v∈U ∨ v=p.getVert s ∨ v=p.getVert t)
    (away : ∀ k, (k=s ∨ k=t) →
      ¬G.Adj e (p.getVert (k-1)) ∨ ¬G.Adj e (p.getVert (k+1))) :
    G.degree e≤5 := by
  classical
  let R := residual G H (p.getVert m)
  have R2 : R.card≤2 := residual_cap A hc hp cap mij
  have s0 : ∀ v, G.Adj e v → v≠p.getVert m →
      ¬G.Adj (p.getVert m) v → v∈R := fun v ev ne no =>
    mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc ne.symm no ep ev),fun h => eH v h ev⟩
  have disj : ¬ (G.Adj (p.getVert m) (p.getVert s) ∧
      G.Adj (p.getVert m) (p.getVert t)) := by
    rintro ⟨se,te⟩
    have good : t-1≤17 ∧ s-1≤17 ∧ s+1≤17 ∧ t-1≠s-1 ∧ t-1≠s+1 := by
      rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;> decide
    obtain ⟨ql,sl,sr,qe1,qe2⟩ := good
    have hm := (shared_charges A hc hp cap mij (Or.inr rfl) te).1
    rw [exhaust_shared A hc hp cap mij (Or.inl rfl) se] at hm
    rcases mem_insert.mp hm with eq|eq
    · exact distinct_get A hp ql sl qe1 eq
    · exact distinct_get A hp ql sr qe2 (mem_singleton.mp eq)
  have count0 (hs : ¬G.Adj (p.getVert m) (p.getVert s))
      (ht : ¬G.Adj (p.getVert m) (p.getVert t)) : G.degree e≤5 := by
    have sub : G.neighborFinset e⊆U∪R := by
      intro v hv
      have ev := (G.mem_neighborFinset e v).mp hv
      by_cases uv : v=p.getVert m
      · exact mem_union_left _ (uv.symm ▸ um)
      by_cases ed : G.Adj (p.getVert m) v
      · rcases covers v ev ed with c|c|c
        · exact mem_union_left _ c
        · exact (hs (c ▸ ed)).elim
        · exact (ht (c ▸ ed)).elim
      · exact mem_union_right _ (s0 v ev uv ed)
    have q := (card_le_card sub).trans (card_union_le U R)
    rw [G.card_neighborFinset_eq_degree] at q
    omega
  have count1 (k l : ℕ) (hk : k=s ∨ k=t)
      (cov : ∀ v, G.Adj e v → G.Adj (p.getVert m) v →
        v∈U ∨ v=p.getVert k ∨ v=p.getVert l)
      (ke : G.Adj (p.getVert m) (p.getVert k))
      (le : ¬G.Adj (p.getVert m) (p.getVert l)) : G.degree e≤5 := by
    obtain ⟨w,wR,wE⟩ : ∃ w∈R, ¬G.Adj e w := by
      have q := shared_charges A hc hp cap mij hk ke
      exact (away k hk).elim (fun n => ⟨_,q.1,n⟩) (fun n => ⟨_,q.2,n⟩)
    have sub : G.neighborFinset e⊆insert (p.getVert k) U∪R.erase w := by
      intro v hv
      have ev := (G.mem_neighborFinset e v).mp hv
      by_cases uv : v=p.getVert m
      · exact mem_union_left _ (mem_insert_of_mem (uv.symm ▸ um))
      by_cases ed : G.Adj (p.getVert m) v
      · rcases cov v ev ed with c|c|c
        · exact mem_union_left _ (mem_insert_of_mem c)
        · exact mem_union_left _ (mem_insert.mpr (Or.inl c))
        · exact (le (c ▸ ed)).elim
      · exact mem_union_right _ (mem_erase.mpr ⟨fun q => wE (q ▸ ev),s0 v ev uv ed⟩)
    have q := (card_le_card sub).trans (card_union_le (insert (p.getVert k) U) (R.erase w))
    rw [G.card_neighborFinset_eq_degree, card_erase_of_mem wR] at q
    have ins := card_insert_le (p.getVert k) U
    omega
  by_cases hs : G.Adj (p.getVert m) (p.getVert s)
  · exact count1 s t (Or.inl rfl) covers hs (fun ht => disj ⟨hs,ht⟩)
  by_cases ht : G.Adj (p.getVert m) (p.getVert t)
  · exact count1 t s (Or.inr rfl)
      (fun v ev ed => (covers v ev ed).imp id Or.symm) ht hs
  exact count0 hs ht

#print axioms at_endpoint
end Graffiti189LongestPath.FiveEdgeBudget
