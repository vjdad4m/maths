import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

/-- At connectivity two, the even-distance set of a root is at least as
large as its distance to any chosen vertex. -/
theorem dist_le_card_evenFrom_of_two_connected (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x y : V) : G.dist x y ≤ (EvenFrom G x).card := by
  classical
  let n := G.dist x y
  have hn : G.dist x y = n := rfl
  let k := (n - 1) / 2
  let L (i : ℕ) := Shell G x (2 * (i + 1))
  let E := (range k).biUnion L
  have pair : (range k : Set ℕ).PairwiseDisjoint L := by
    intro i _ j _ neq
    rw [Function.onFun, disjoint_left]
    intro z zi zj
    have ri := mem_shell.mp zi
    have rj := mem_shell.mp zj
    omega
  have sz : k * 2 ≤ E.card := by
    dsimp only [E]
    rw [card_biUnion pair]
    calc
      k * 2 = ∑ _i ∈ range k, 2 := by simp
      _ ≤ _ := sum_le_sum (fun i hi => by
        have h := mem_range.mp hi
        exact shell_card_of_far hc 2 conn (x:=x) (y:=y) (i:=2*(i+1)) (by omega) (by omega))
  have evenE : E ⊆ EvenFrom G x := by
    intro v hv
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
    exact mem_filter.mpr ⟨mem_univ _, by rw [mem_shell.mp hi]; exact even_two_mul _⟩
  have xE : x ∉ E := by
    intro he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    have rd := mem_shell.mp hi
    rw [dist_self] at rd
    omega
  have xe : x ∈ EvenFrom G x := by simp [EvenFrom, dist_self]
  have first := card_le_card (insert_subset xe evenE)
  rw [card_insert_of_not_mem xE] at first
  by_cases hn0 : n = 0
  · omega
  by_cases hpar : n % 2 = 0
  · have xy : x ≠ y := by
      intro h
      rw [h, dist_self] at hn
      omega
    have ye : y ∈ EvenFrom G x := mem_filter.mpr ⟨mem_univ _, by
      rw [hn]; exact ⟨n / 2, by omega⟩⟩
    have yE : y ∉ E := by
      intro he
      obtain ⟨i,hi,hy⟩ := mem_biUnion.mp he
      have ir := mem_range.mp hi
      have rd := mem_shell.mp hy
      omega
    have xi : x ∉ insert y E := fun h => (mem_insert.mp h).elim xy xE
    have second := card_le_card (insert_subset xe (insert_subset ye evenE))
    rw [card_insert_of_not_mem xi, card_insert_of_not_mem yE] at second
    omega
  · omega

/-- Degree assumptions are unnecessary for the diameter cap. -/
theorem diameter_le_even_budget_of_two_connected (hc : G.Connected) (d : ℕ)
    (cap : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∀ x y, G.dist x y ≤ d + 1 :=
  fun x y => (dist_le_card_evenFrom_of_two_connected hc conn x y).trans (cap x)

#print axioms diameter_le_even_budget_of_two_connected
end Graffiti189LongestPath
