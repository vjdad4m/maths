import Bound
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Multiset.Sort

namespace SlaterEdges583
open Finset SimpleGraph TriangleMatching1078 EulerDom574
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The descending degree sequence and the executable prefix convention of rows 33 and 821. -/
noncomputable def degreesDesc := (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)
noncomputable def slater := sInf {k : ℕ | Fintype.card V ≤ k + ((degreesDesc G).take k).sum}

/-- The first k terms of a decreasing list bound the sum of any submultiset
of size at most k. Repeated values are counted with their multiplicities. -/
private theorem prefix_bound (l : List ℕ) (sorted : l.Sorted (· ≥ ·)) (s : Multiset ℕ)
    (sub : s ≤ (l : Multiset ℕ)) (k : ℕ) (size : s.card ≤ k) :
    s.sum ≤ (l.take k).sum := by
  induction l generalizing s k with
  | nil =>
    have h : s = 0 := Multiset.le_zero.mp sub
    simp [h]
  | cons a l ih =>
    by_cases zero : s = 0
    · simp [zero]
    obtain ⟨w,hw⟩ := Multiset.exists_mem_of_ne_zero zero
    obtain ⟨b,mem⟩ : ∃ b ∈ s, a ∈ s → b = a := by
      by_cases ha : a ∈ s
      · exact ⟨a,ha,fun _ => rfl⟩
      · exact ⟨w,hw,fun h => (ha h).elim⟩
    obtain ⟨t,eq⟩ := Multiset.exists_cons_of_mem mem.1
    have rest : t ≤ (l : Multiset ℕ) := by
      by_cases ha : a ∈ s
      · rw [mem.2 ha] at eq
        rw [eq] at sub
        exact (Multiset.cons_le_cons_iff _).mp sub
      · have small : s ≤ (l : Multiset ℕ) :=
          (Multiset.le_cons_of_not_mem (t := (l : Multiset ℕ)) ha).mp sub
        rw [eq] at small
        exact (Multiset.le_cons_self _ _).trans small
    have ba : b ≤ a := by
      have h := Multiset.mem_of_le sub mem.1
      rcases List.mem_cons.mp h with h|h
      · exact h.le
      · exact (List.pairwise_cons.mp sorted).1 b h
    cases k with
    | zero => simp [eq] at size
    | succ k =>
      have h := ih (List.pairwise_cons.mp sorted).2 t rest k (by simpa [eq] using size)
      simpa [eq] using Nat.add_le_add ba h

theorem capacity_bound (A : Finset V) (k : ℕ) (Ak : A.card ≤ k) :
    (∑ u ∈ A, (G.degree u + 1)) ≤ k + ((degreesDesc G).take k).sum := by
  have h := prefix_bound (degreesDesc G) (Multiset.sort_sorted _ _) (A.val.map (fun v => G.degree v))
    (by unfold degreesDesc; rw [Multiset.sort_eq]; exact Multiset.map_le_map (val_le_iff.mpr (subset_univ A)))
    k (by simpa using Ak)
  change (∑ u ∈ A, G.degree u) ≤ _ at h
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  omega

/-- If all closed neighborhoods meet T at least twice, then its two halves
give a feasible Slater prefix of length k whenever |T| ≤ 2k. -/
theorem of_double_cover [DecidableEq V] (T : Finset V) (k : ℕ) (small : T.card ≤ 2*k)
    (cover : ∀ v, 2 ≤ (T.filter (fun u => v = u ∨ G.Adj v u)).card) :
    slater G ≤ k := by
  classical
  let r (v u : V) := v = u ∨ G.Adj v u
  have swap (u : V) : (univ.bipartiteBelow r u) = insert u (G.neighborFinset u) := by
    ext v
    simp [bipartiteBelow,r,adj_comm]
  have value (u : V) : (univ.bipartiteBelow r u).card = G.degree u + 1 := by
    rw [swap,card_insert_of_not_mem,card_neighborFinset_eq_degree]
    simp
  have mass : 2 * Fintype.card V ≤ ∑ u ∈ T, (G.degree u + 1) := calc
    _ = ∑ _v : V, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ v : V, (T.bipartiteAbove r v).card := sum_le_sum (fun v _ => cover v)
    _ = ∑ u ∈ T, (univ.bipartiteBelow r u).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ = _ := sum_congr rfl (fun u _ => value u)
  obtain ⟨A,sub,sz⟩ := exists_subset_card_eq (min_le_right k T.card)
  have left := capacity_bound G A k (sz.trans_le (min_le_left _ _))
  have right := capacity_bound G (T \ A) k (by rw [card_sdiff sub]; omega)
  rw [← sum_sdiff sub] at mass
  apply Nat.sInf_le (s := {k : ℕ | Fintype.card V ≤ k + ((degreesDesc G).take k).sum})
  change Fintype.card V ≤ _
  omega

/-- Endpoints of an edge-dominating set form a double cover when δ ≥ 2.
The selected edges themselves may share endpoints. -/
theorem of_edge_dominating (deg : ∀ v, 2 ≤ G.degree v) (D : Finset G.edgeSet)
    (hD : Dominates G.lineGraph D) : slater G ≤ D.card := by
  classical
  let ends (e : G.edgeSet) := univ.filter (fun v : V => v ∈ e.val)
  let T := D.biUnion ends
  have inside {v : V} : v ∈ T ↔ ∃ e ∈ D, v ∈ e.val := by simp [T,ends]
  have size (e : G.edgeSet) : (ends e).card ≤ 2 := by
    rcases e with ⟨q,hq⟩
    induction q using Sym2.ind with
    | h a b =>
      apply le_trans (card_le_card (t:={a,b}) ?_) (card_insert_le _ _ |>.trans (by simp))
      intro v hv
      simpa [Sym2.mem_iff] using (mem_filter.mp hv).2
  have bound : T.card ≤ 2*D.card := calc
    _ ≤ ∑ e ∈ D, (ends e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, 2 := sum_le_sum (fun e _ => size e)
    _ = _ := by simp [Nat.mul_comm]
  have hit {a b : V} (ab : G.Adj a b) : a ∈ T ∨ b ∈ T := by
    obtain ⟨e,he,z,ze,zab⟩ := (dominates_iff G D).mp hD ⟨s(a,b),ab⟩
    rcases Sym2.mem_iff.mp zab with rfl|rfl
    · exact Or.inl (inside.mpr ⟨_,he,ze⟩)
    · exact Or.inr (inside.mpr ⟨_,he,ze⟩)
  apply of_double_cover G T D.card bound
  intro x
  by_cases hx : x ∈ T
  · have other : ∃ y ∈ T, G.Adj x y := by
      obtain ⟨e,he,hxe⟩ := inside.mp hx
      obtain ⟨y,rep⟩ := Sym2.mem_iff_exists.mp hxe
      exact ⟨y,inside.mpr ⟨e,he,by rw [rep]; exact Sym2.mem_iff.mpr (Or.inr rfl)⟩,
        (show s(x,y) ∈ G.edgeSet from rep ▸ e.property)⟩
    obtain ⟨y,hy,xy⟩ := other
    have sub : {x,y} ⊆ T.filter (fun u => x=u ∨ G.Adj x u) := by
      intro z hz
      rcases mem_insert.mp hz with eq|mem
      · subst z; exact mem_filter.mpr ⟨hx,Or.inl rfl⟩
      · rw [mem_singleton.mp mem]; exact mem_filter.mpr ⟨hy,Or.inr xy⟩
    simpa [xy.ne] using card_le_card sub
  · have sub : G.neighborFinset x ⊆ T.filter (fun u => x=u ∨ G.Adj x u) := by
      intro y hy
      have xy := (G.mem_neighborFinset _ _).mp hy
      exact mem_filter.mpr ⟨(hit xy).resolve_left hx,Or.inr xy⟩
    exact (deg x).trans (by simpa using card_le_card sub)

theorem slater_le_lineDomination (deg : ∀ v, 2 ≤ G.degree v) : slater G ≤ lineDomination G := by
  obtain ⟨D,sz,hD⟩ := line_attained G
  exact (of_edge_dominating G deg D hD).trans_eq sz

theorem eulerian {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : 2 ≤ Fintype.card V) (conn : G.Connected) (even : ∀ v, Even (G.degree v)) :
    slater G ≤ lineDomination G := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  apply slater_le_lineDomination
  intro v
  have pos : 0 < G.degree v := by
    apply (G.degree_pos_iff_exists_adj v).mpr
    obtain ⟨w,diff⟩ := exists_ne v
    obtain ⟨walk⟩ := conn.preconnected v w
    cases walk with
    | nil => exact (diff rfl).elim
    | cons e _ => exact ⟨_,e⟩
  obtain ⟨t,ht⟩ := even v
  omega


theorem row583 (order : 2 ≤ Fintype.card V) (_hK4 : G.CliqueFree 4)
    (conn : G.Connected) (even : ∀ v, Even (G.degree v)) :
    slater G ≤ lineDomination G ∧ slater G ≤ AutoGraphForge378.minMaximalMatching G :=
  ⟨eulerian G order conn even,(eulerian G order conn even).trans (lineDomination_le_matching G)⟩

#print axioms of_double_cover
#print axioms of_edge_dominating
#print axioms slater_le_lineDomination
#print axioms eulerian
#print axioms row583
end SlaterEdges583
