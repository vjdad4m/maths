import FiveMidBudget189
import FiveLongerWord189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FiveCheapBudget Graffiti189LongestPath.FiveMidBudget
open Graffiti189LongestPath.FiveLongerWord
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option linter.unreachableTactic false
namespace Graffiti189LongestPath.FiveMidSplice
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H : Finset V}
variable (A : PairData p H x y 7 10 1 16) (hc : G.Connected)
variable (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6)
variable (noH : ∀ j∈({6,8,9,11}:Finset ℕ),∀ z∈H,¬G.Adj (p.getVert j) z)
include A hc hp cap noH

private theorem bounded {m j : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m))
    (hf : j∈({6,8,9,11}:Finset ℕ)) (E : Finset ℕ)
    (ex : ∀ k∈E,¬G.Adj (p.getVert j) (p.getVert k)) :
    G.neighborFinset (p.getVert j) ⊆ (((nearChunk.erase j)\E).image p.getVert) := by
  have jn : j≠m := by
    simp at hf
    rcases hm with rfl|rfl <;> omega
  have hj : j∈chunk := by
    simp at hf
    rcases hf with rfl|rfl|rfl|rfl <;> decide
  intro v hv
  have h := (G.mem_neighborFinset _ _).mp hv
  obtain ⟨k,kk,rfl⟩ := mem_image.mp (flank_cover A hc hp cap hm high hj jn (noH _ hf) h)
  exact mem_image.mpr ⟨k,mem_sdiff.mpr ⟨kk,fun hk => ex k hk h⟩,rfl⟩

theorem forces {m j k r : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m))
    (hf : j∈({6,8,9,11}:Finset ℕ)) (jh : 6≤G.degree (p.getVert j))
    (lack : ¬G.Adj (p.getVert j) (p.getVert k)) (size : (((nearChunk.erase j)\{k}):Finset ℕ).card≤6)
    (rr : r∈((nearChunk.erase j)\{k})) : G.Adj (p.getVert j) (p.getVert r) := by
  classical
  have cov := bounded A hc hp cap noH hm high hf {k}
    (fun l ll => (mem_singleton.mp ll).symm ▸ lack)
  have bd : ((((nearChunk.erase j)\{k}).image p.getVert):Finset V).card≤6 :=
    card_image_le.trans size
  have d : 6≤(G.neighborFinset (p.getVert j)).card := by rwa [G.card_neighborFinset_eq_degree]
  have eq := eq_of_subset_of_card_le cov (bd.trans d)
  exact (G.mem_neighborFinset _ _).mp (eq.symm ▸ mem_image.mpr ⟨r,rr,rfl⟩)

theorem low_of_two_absent {m j k l : ℕ} (hm : m=7 ∨ m=10) (high : 6≤G.degree (p.getVert m))
    (hf : j∈({6,8,9,11}:Finset ℕ))
    (lackK : ¬G.Adj (p.getVert j) (p.getVert k)) (lackL : ¬G.Adj (p.getVert j) (p.getVert l))
    (size : (((nearChunk.erase j)\{k,l}):Finset ℕ).card≤5) : G.degree (p.getVert j)≤5 := by
  classical
  have cov := bounded A hc hp cap noH hm high hf {k,l}
    (by intro r rr; simp only [mem_insert,mem_singleton] at rr; exact rr.elim (fun e => e.symm ▸ lackK) (fun e => e.symm ▸ lackL))
  have d := (card_le_card cov).trans (card_image_le.trans size)
  rwa [G.card_neighborFinset_eq_degree] at d


theorem left
    (deg : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (high : 6≤G.degree (p.getVert 7)) : False := by
  classical
  have hx := pins_at A
  have ax : G.Adj (p.getVert 7) x := (Graffiti189LongestPath.pin_data hx.1).2.symm
  have xb : G.Adj x (p.getVert 10) := (Graffiti189LongestPath.pin_data hx.2.1).2
  have ne (i j : ℕ) (hi : i≤17) (hj : j≤17) (sep : i≠j) :=
    distinct_get A hp hi hj sep
  have d (m n : ℕ) (hm : m≤17) (hn : n≤17) (sep : m≠n) :=
    deg (p.getVert m) (p.getVert n) (ne m n hm hn sep)
  by_cases e1 : G.Adj (p.getVert 8) (p.getVert 11)
  ·
    refine impossible A hp [0,1,2,3,4,5,6,7,18,10,9,8,11,12,13,14,15,16,17] (by decide) (by decide) ?_
    simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
    dsimp only [embed]
    repeat' constructor
    all_goals first | assumption | exact e1.symm | exact (adjacency_on_spine A 0 (by decide)) | exact (adjacency_on_spine A 0 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide))
  by_cases e2 : G.Adj (p.getVert 9) (p.getVert 11)
  · have eb : G.Adj (p.getVert 10) (p.getVert 8) := by
      rcases d 10 8 (by decide) (by decide) (by decide) with bh|lh
      · exact cheap_high_all A hc hp cap (Or.inr rfl) bh (by decide) (by decide)
      · exact (forces A hc hp cap noH (Or.inl rfl) high (by decide) lh e1 (by decide) (by decide)).symm
    refine impossible A hp [0,1,2,3,4,5,6,7,18,10,8,9,11,12,13,14,15,16,17] (by decide) (by decide) ?_
    simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
    dsimp only [embed]
    repeat' constructor
    all_goals first | assumption | exact e1.symm | exact e2 | exact (adjacency_on_spine A 0 (by decide)) | exact (adjacency_on_spine A 0 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide))
  have low := low_of_two_absent A hc hp cap noH (Or.inl rfl) high
    (j:=11) (by decide) (fun ad => e1 ad.symm) (fun ad => e2 ad.symm) (by decide)
  have high8 : 6≤G.degree (p.getVert 8) :=
    (d 8 11 (by decide) (by decide) (by decide)).resolve_right (by omega)
  have high9 : 6≤G.degree (p.getVert 9) :=
    (d 9 11 (by decide) (by decide) (by decide)).resolve_right (by omega)
  have e58 : G.Adj (p.getVert 5) (p.getVert 8) :=
    (forces A hc hp cap noH (Or.inl rfl) high (by decide) high8 e1 (by decide) (by decide)).symm
  have e96 : G.Adj (p.getVert 9) (p.getVert 6) :=
    forces A hc hp cap noH (Or.inl rfl) high (by decide) high9 e2 (by decide) (by decide)
  refine impossible A hp [0,1,2,3,4,5,8,9,6,7,18,10,11,12,13,14,15,16,17] (by decide) (by decide) ?_
  simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
  dsimp only [embed]
  repeat' constructor
  all_goals first | assumption | exact e1.symm | exact e58 | exact e96 | exact (adjacency_on_spine A 0 (by decide)) | exact (adjacency_on_spine A 0 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide))
#print axioms left

theorem right
    (deg : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (high : 6≤G.degree (p.getVert 10)) : False := by
  classical
  have hx := pins_at A
  have ax : G.Adj (p.getVert 10) x := (Graffiti189LongestPath.pin_data hx.2.1).2.symm
  have xb : G.Adj x (p.getVert 7) := (Graffiti189LongestPath.pin_data hx.1).2
  have ne (i j : ℕ) (hi : i≤17) (hj : j≤17) (sep : i≠j) :=
    distinct_get A hp hi hj sep
  have d (m n : ℕ) (hm : m≤17) (hn : n≤17) (sep : m≠n) :=
    deg (p.getVert m) (p.getVert n) (ne m n hm hn sep)
  by_cases e1 : G.Adj (p.getVert 9) (p.getVert 6)
  ·
    refine impossible A hp [17,16,15,14,13,12,11,10,18,7,8,9,6,5,4,3,2,1,0] (by decide) (by decide) ?_
    simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
    dsimp only [embed]
    repeat' constructor
    all_goals first | assumption | exact e1.symm | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide)) | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 0 (by decide)).symm
  by_cases e2 : G.Adj (p.getVert 8) (p.getVert 6)
  · have eb : G.Adj (p.getVert 7) (p.getVert 9) := by
      rcases d 7 9 (by decide) (by decide) (by decide) with bh|lh
      · exact cheap_high_all A hc hp cap (Or.inl rfl) bh (by decide) (by decide)
      · exact (forces A hc hp cap noH (Or.inr rfl) high (by decide) lh e1 (by decide) (by decide)).symm
    refine impossible A hp [17,16,15,14,13,12,11,10,18,7,9,8,6,5,4,3,2,1,0] (by decide) (by decide) ?_
    simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
    dsimp only [embed]
    repeat' constructor
    all_goals first | assumption | exact e1.symm | exact e2 | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide)) | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 0 (by decide)).symm
  have low := low_of_two_absent A hc hp cap noH (Or.inr rfl) high
    (j:=6) (by decide) (fun ad => e1 ad.symm) (fun ad => e2 ad.symm) (by decide)
  have high8 : 6≤G.degree (p.getVert 9) :=
    (d 9 6 (by decide) (by decide) (by decide)).resolve_right (by omega)
  have high9 : 6≤G.degree (p.getVert 8) :=
    (d 8 6 (by decide) (by decide) (by decide)).resolve_right (by omega)
  have e58 : G.Adj (p.getVert 12) (p.getVert 9) :=
    (forces A hc hp cap noH (Or.inr rfl) high (by decide) high8 e1 (by decide) (by decide)).symm
  have e96 : G.Adj (p.getVert 8) (p.getVert 11) :=
    forces A hc hp cap noH (Or.inr rfl) high (by decide) high9 e2 (by decide) (by decide)
  refine impossible A hp [17,16,15,14,13,12,9,8,11,10,18,7,6,5,4,3,2,1,0] (by decide) (by decide) ?_
  simp only [List.map_cons, List.map_nil, List.chain'_cons, List.chain'_singleton]
  dsimp only [embed]
  repeat' constructor
  all_goals first | assumption | exact e1.symm | exact e58 | exact e96 | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 16 (by decide)) | exact (adjacency_on_spine A 16 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 15 (by decide)) | exact (adjacency_on_spine A 15 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 14 (by decide)) | exact (adjacency_on_spine A 14 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 13 (by decide)) | exact (adjacency_on_spine A 13 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 12 (by decide)) | exact (adjacency_on_spine A 12 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 11 (by decide)) | exact (adjacency_on_spine A 11 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 10 (by decide)) | exact (adjacency_on_spine A 10 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 9 (by decide)) | exact (adjacency_on_spine A 9 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 8 (by decide)) | exact (adjacency_on_spine A 8 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 7 (by decide)) | exact (adjacency_on_spine A 7 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 6 (by decide)) | exact (adjacency_on_spine A 6 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 5 (by decide)) | exact (adjacency_on_spine A 5 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 4 (by decide)) | exact (adjacency_on_spine A 4 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 3 (by decide)) | exact (adjacency_on_spine A 3 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 2 (by decide)) | exact (adjacency_on_spine A 2 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 1 (by decide)) | exact (adjacency_on_spine A 1 (by decide)).symm | exact (adjacency_on_spine A 0 (by decide)).symm
#print axioms right
end Graffiti189LongestPath.FiveMidSplice
