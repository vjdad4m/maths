import FiveSharedCharges189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FiveCheapBudget Graffiti189LongestPath.FiveSharedCharges
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
namespace Graffiti189LongestPath.FiveMidBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H : Finset V}
variable (A : PairData p H x y 7 10 1 16) (hc : G.Connected)
variable (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
include A hc hp cap

theorem outer_left : p.getVert 5∈residual G H (p.getVert 7) :=
  charge_on_spine A hc (distinct_get A hp (by decide) (by decide) (by decide))
    (adjacency_on_spine A 6 (by decide)).symm (adjacency_on_spine A 5 (by decide)).symm
    (not_adj_outside_allowed A hc hp cap (Or.inl rfl) (by decide) (by decide))

theorem outer_right : p.getVert 12∈residual G H (p.getVert 10) :=
  charge_on_spine A hc (distinct_get A hp (by decide) (by decide) (by decide))
    (adjacency_on_spine A 10 (by decide)) (adjacency_on_spine A 11 (by decide))
    (not_adj_outside_allowed A hc hp cap (Or.inr rfl) (by decide) (by decide))

theorem no_shared {m k : ℕ} (hm : m=7 ∨ m=10) (hk : k=1 ∨ k=16) :
    ¬G.Adj (p.getVert m) (p.getVert k) := by
  intro ed
  have e := exhaust_shared A hc hp cap hm hk ed
  rcases hm with rfl|rfl
  · have q := outer_left A hc hp cap
    rw [e] at q
    rcases hk with rfl|rfl <;> rcases mem_insert.mp q with q|q
    all_goals first
      | exact distinct_get A hp (by decide) (by decide) (by decide) q
      | exact distinct_get A hp (by decide) (by decide) (by decide) (mem_singleton.mp q)
  · have q := outer_right A hc hp cap
    rw [e] at q
    rcases hk with rfl|rfl <;> rcases mem_insert.mp q with q|q
    all_goals first
      | exact distinct_get A hp (by decide) (by decide) (by decide) q
      | exact distinct_get A hp (by decide) (by decide) (by decide) (mem_singleton.mp q)

def chunk : Finset ℕ := {6,7,8,9,10,11}
def nearChunk : Finset ℕ := {5,6,7,8,9,10,11,12}

theorem cheap_cover {m : ℕ} (hm : m=7 ∨ m=10) {v : V}
    (ed : G.Adj (p.getVert m) v) : v∈insert x ((chunk.erase m).image p.getVert) := by
  rcases cheap_neighbors A hc hp cap hm ed with e|ok
  · exact mem_insert.mpr (Or.inl e)
  obtain ⟨i,ii,rfl⟩ := mem_image.mp ok
  have ne : i≠m := fun e => G.irrefl (e ▸ ed)
  have ic : i∈chunk := by
    simp only [allowed,targets,flanks,mem_insert,mem_singleton] at ii
    rcases ii with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | decide | exact (no_shared A hc hp cap hm (Or.inl rfl) ed).elim |
      exact (no_shared A hc hp cap hm (Or.inr rfl) ed).elim
  exact mem_insert_of_mem (mem_image.mpr ⟨i,mem_erase.mpr ⟨ne,ic⟩,rfl⟩)

theorem cheap_high_all {m : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m))
    {j : ℕ} (hj : j∈chunk) (jn : j≠m) : G.Adj (p.getVert m) (p.getVert j) := by
  classical
  let B := insert x ((chunk.erase m).image p.getVert)
  have sub : G.neighborFinset (p.getVert m)⊆B := fun u hu =>
    cheap_cover A hc hp cap hm ((G.mem_neighborFinset _ _).mp hu)
  have cub : (chunk.erase m).card=5 := by rcases hm with rfl|rfl <;> decide
  have bo : B.card≤6 := by
    have h := card_insert_le x ((chunk.erase m).image p.getVert)
    have k : ((chunk.erase m).image p.getVert).card≤5 := card_image_le.trans (by rw [cub])
    dsimp [B]
    omega
  have eql := eq_of_subset_of_card_le sub (bo.trans (by rwa [G.card_neighborFinset_eq_degree]))
  exact (G.mem_neighborFinset _ _).mp (eql.symm ▸ mem_insert_of_mem (mem_image.mpr
    ⟨j,mem_erase.mpr ⟨jn,hj⟩,rfl⟩))

theorem high_residual {m : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m)) :
    residual G H (p.getVert m)={p.getVert 5,p.getVert 12} := by
  classical
  have n5 : m≠5 := by rcases hm with rfl|rfl <;> decide
  have n12 : m≠12 := by rcases hm with rfl|rfl <;> decide
  have ml : m≤17 := by rcases hm with rfl|rfl <;> decide
  have six : 6≠m := by rcases hm with rfl|rfl <;> decide
  have ele : 11≠m := by rcases hm with rfl|rfl <;> decide
  have h5 := charge_on_spine A hc (distinct_get A hp ml (by decide) n5)
    (cheap_high_all A hc hp cap hm high (by decide) six)
    (adjacency_on_spine A 5 (by decide)).symm
    (not_adj_outside_allowed A hc hp cap hm (by decide) (by decide))
  have h12 := charge_on_spine A hc (distinct_get A hp ml (by decide) n12)
    (cheap_high_all A hc hp cap hm high (by decide) ele)
    (adjacency_on_spine A 11 (by decide))
    (not_adj_outside_allowed A hc hp cap hm (by decide) (by decide))
  refine (eq_of_subset_of_card_le ?_ ?_).symm
  · intro u hu
    rcases mem_insert.mp hu with e|e
    · exact e.symm ▸ h5
    · exact (mem_singleton.mp e).symm ▸ h12
  · have ne := distinct_get A hp (show 5≤17 by decide) (show 12≤17 by decide) (show 5≠12 by decide)
    rw [show ({p.getVert 5,p.getVert 12}:Finset V).card=2 by simp [ne]]
    exact residual_cap A hc hp cap hm

theorem flank_cover {m : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m))
    {j : ℕ} (hj : j∈chunk) (jn : j≠m)
    (noH : ∀ z∈H, ¬G.Adj (p.getVert j) z) {v : V}
    (ed : G.Adj (p.getVert j) v) : v∈((nearChunk.erase j).image p.getVert) := by
  have vp := (A.full v).resolve_right (fun h => noH v h ed)
  obtain ⟨k,ke,kk⟩ := mem_support_iff_exists_getVert.mp vp
  subst v
  have ll := A.pathLen
  have kl : k≤17 := by omega
  have jl : j≤17 := by simp [chunk] at hj; omega
  have jm : j≠k := fun e => G.irrefl (e.symm ▸ ed)
  refine mem_image.mpr ⟨k,mem_erase.mpr ⟨Ne.symm jm,?_⟩,rfl⟩
  by_contra! kn
  have kch : k∉chunk := by
    intro z
    simp [chunk] at z
    rcases z with rfl|rfl|rfl|rfl|rfl|rfl <;> exact kn (by decide)
  have kml : k≠m := fun z => kch (z.symm ▸ (by rcases hm with rfl|rfl <;> decide : m∈chunk))
  have ml : m≤17 := by omega
  have no : ¬G.Adj (p.getVert m) (p.getVert k) := by
    intro q
    have entry := cheap_cover A hc hp cap hm q
    rcases mem_insert.mp entry with eq|eq
    · exact A.off _ A.xH (eq ▸ p.getVert_mem_support k)
    · obtain ⟨r,rr,re⟩ := mem_image.mp eq
      have rc := (mem_erase.mp rr).2
      have rl : r≤17 := by simp [chunk] at rc; omega
      have e := hp.1.getVert_injOn (ll.symm ▸ rl) (ll.symm ▸ kl) re
      exact kch (e ▸ rc)
  have t := charge_on_spine A hc (distinct_get A hp ml kl kml.symm)
    (cheap_high_all A hc hp cap hm high hj jn) ed no
  rw [high_residual A hc hp cap hm high] at t
  rcases mem_insert.mp t with e|e
  · have eq := hp.1.getVert_injOn (ll.symm ▸ kl) (ll.symm ▸ (by decide : 5≤17)) e
    exact kn (eq.symm ▸ (by decide : 5∈nearChunk))
  · have eq := hp.1.getVert_injOn (ll.symm ▸ kl) (ll.symm ▸ (by decide : 12≤17)) (mem_singleton.mp e)
    exact kn (eq.symm ▸ (by decide : 12∈nearChunk))

#print axioms cheap_high_all
#print axioms high_residual
end Graffiti189LongestPath.FiveMidBudget
