import Proof179
import Reduction185

namespace Graffiti185.Reuse
set_option maxHeartbeats 1600000
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem leaves_bridge : Short177.maxLeaves G ≤ Graffiti185.maxLeaves G := by
  classical
  unfold Short177.maxLeaves
  apply Finset.sup_le
  intro T hT
  obtain ⟨_,sub,tree⟩ := mem_filter.mp hT
  unfold Graffiti185.maxLeaves
  apply le_csSup
  · refine ⟨Fintype.card V,?_⟩
    rintro k ⟨S,_,_,rfl⟩
    exact card_le_univ _
  · exact ⟨T,sub,tree,rfl⟩

omit [Fintype V] in
private theorem color_partition (S A B : Finset V)
    (eq : A ∪ B = S) (ia : Short177.Indep G A) (ib : Short177.Indep G B) :
    ∃ d : S → Bool, ∀ a b : S, G.Adj a.val b.val → d a ≠ d b := by
  let c (v : S) := decide (v.val ∈ A)
  have memB (z : V) (hz : z ∈ S) (na : z ∉ A) : z ∈ B := by
    have hz' : z ∈ A ∪ B := eq.symm ▸ hz
    exact (mem_union.mp hz').resolve_left na
  refine ⟨c,?_⟩
  intro v w e
  by_cases a : v.val ∈ A <;> by_cases b : w.val ∈ A
  · exact (ia _ a _ b e.ne e).elim
  · simp [c,a,b]
  · simp [c,a,b]
  · exact (ib _ (memB _ v.property a) _ (memB _ w.property b) e.ne e).elim

omit [DecidableEq V] in
private theorem color_le (S : Finset V)
    (h : ∃ d : S → Bool, ∀ a b : S, G.Adj a.val b.val → d a ≠ d b) :
    S.card ≤ Graffiti185.bipartiteNumber G := by
  classical
  have hs : S ∈ univ.powerset.filter (fun s : Finset V =>
    ∃ d : s → Bool, ∀ a b : s, G.Adj a.val b.val → d a ≠ d b) :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ S),h⟩
  simpa only [Graffiti185.bipartiteNumber] using le_sup (f := Finset.card) hs

theorem bipartite_bridge : Short177.bipartiteNum G ≤ Graffiti185.bipartiteNumber G := by
  classical
  unfold Short177.bipartiteNum
  apply Finset.sup_le
  intro S hs
  obtain ⟨A,B,_,eq,ia,ib⟩ := (mem_filter.mp hs).2
  exact color_le G S (color_partition G S A B eq ia ib)

variable [Nontrivial V] [DecidableRel G.Adj]

/-- The prior metric reduction now needs no unverified order-bound hypothesis. -/
theorem order_bound (hc : G.Connected) :
    Fintype.card V + 1 ≤ Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G :=
  (Graffiti179.order_add_one G hc Fintype.one_lt_card).trans
    (Nat.add_le_add (leaves_bridge G) (bipartite_bridge G))

/-- A hypothetical failure is one of three cases, and both low-leaf-sum
cases must be claw-free (local independence at most two). -/
theorem narrowed_failure (hc : G.Connected) (fail : ¬ Claim185 G) :
    (squareMaxDegree G + 1 = Fintype.card V ∧
        ((maxLeaves G + bipartiteNumber G = Fintype.card V + 1 ∧
            1 < averageDistance (square G) ∧ Graffiti179.lambda G ≤ 2) ∨
          (maxLeaves G + bipartiteNumber G = Fintype.card V + 2 ∧
            (3 / 2 : ℚ) < averageDistance (square G)))) ∨
      (squareMaxDegree G + 2 = Fintype.card V ∧
        maxLeaves G + bipartiteNumber G = Fintype.card V + 1 ∧
        (3 / 2 : ℚ) < averageDistance (square G) ∧ Graffiti179.lambda G ≤ 2) := by
  have order := order_bound G hc
  have strict (h : 3 ≤ Graffiti179.lambda G) :
      Fintype.card V + 2 ≤ Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G :=
    (Graffiti179.order_add_two G hc h).trans (Nat.add_le_add (leaves_bridge G) (bipartite_bridge G))
  rcases (counterexample_iff_of_order_bound hc order).mp fail with h | h
  · rcases h with ⟨n, ⟨h,e⟩ | ⟨h,e⟩⟩
    · exact Or.inl ⟨n,Or.inl ⟨h,e,by by_contra! z; have := strict z; omega⟩⟩
    · exact Or.inl ⟨n,Or.inr ⟨h,e⟩⟩
  · obtain ⟨n,h,e⟩ := h
    exact Or.inr ⟨n,h,e,by by_contra! z; have := strict z; omega⟩

#print axioms narrowed_failure
end Graffiti185.Reuse
