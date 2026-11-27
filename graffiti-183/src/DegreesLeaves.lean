import BFS
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiBFS
open scoped BigOperators
namespace GraffitiDegrees
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem deg_pos (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    0 < (nbr G v).card := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  obtain ⟨z,hz⟩ := adj_exists_of_connected G hc hw.symm
  exact Finset.card_pos.mpr ⟨z, (mem_nbr G).mpr hz⟩

theorem handshaking_nbr [DecidableRel G.Adj] :
    (∑ v : V, (nbr G v).card) = 2 * G.edgeFinset.card := by
  classical
  have he (v : V) : (nbr G v).card = G.degree v := by
    change (nbr G v).card = (G.neighborFinset v).card
    rw [SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext w
    simp
  simp_rw [he]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G

theorem tree_count (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) (r : V) :
    2 ≤ (leafSet G).card ∧ (nbr G r).card ≤ (leafSet G).card := by
  classical
  let extra (v : V) : ℕ := if v = r then (nbr G r).card-2 else 0
  let base (v : V) : ℕ := if (nbr G v).card = 1 then 1 else 2
  have hbase (v : V) : base v + extra v ≤ (nbr G v).card := by
    have hv := deg_pos G hT.isConnected hn v
    by_cases he : v = r
    · subst v
      by_cases hh : (nbr G r).card = 1
      · simp [base,extra,hh]
      · simp [base,extra,hh]
        omega
    · by_cases hh : (nbr G v).card = 1
      · simp [base,extra,he,hh]
      · simp [base,extra,he,hh]
        omega
  have extr : (∑ v : V, extra v) = (nbr G r).card-2 := by simp [extra]
  have bs (v : V) : base v = 1 + (if (nbr G v).card ≠ 1 then 1 else 0) := by
    by_cases h : (nbr G v).card = 1 <;> simp [base,h]
  have bfs : (∑ v : V, base v) =
      Fintype.card V + (Fintype.card V - (leafSet G).card) := by
    simp_rw [bs, Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun v => (nbr G v).card ≠ 1)) =
        ((Finset.univ : Finset V) \ leafSet G) := by
      ext v
      simp [leafSet]
    rw [hf, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  have hsum : Fintype.card V + (Fintype.card V - (leafSet G).card)
      + ((nbr G r).card-2) ≤ 2 * G.edgeFinset.card := by
    rw [← bfs, ← extr, ← Finset.sum_add_distrib, ← handshaking_nbr G]
    exact sum_mono_nat _ _ _ (fun v _ => hbase v)
  have he := hT.card_edgeFinset
  have hls : (leafSet G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem maxLeaves_ge_degree (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    (nbr G v).card ≤ maxLeaves G := by
  obtain ⟨par,T,hT,ht,_,_,hnbr⟩ := exists_bfs_tree G hc v
  rw [hnbr]
  exact (tree_count T ht hn v).2.trans (leaf_card_le_maxLeaves G hT ht)

theorem maxLeaves_ge_two (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  obtain ⟨T,hT,ht⟩ := hc.exists_isTree_le
  exact (tree_count T ht hn v).1.trans (leaf_card_le_maxLeaves G hT ht)

#print axioms maxLeaves_ge_degree
end GraffitiDegrees
