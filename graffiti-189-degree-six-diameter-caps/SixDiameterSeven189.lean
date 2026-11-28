import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic from SmallSeparator189
set_option linter.unusedSectionVars false

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The cap pays for the separating even layers and the terminal even
point itself if the diameter reaches the next even step. -/
private theorem distance_lt_of_consumed_even_layers
    (hc : G.Connected) (d k r : ℕ) (hkr : d ≤ r*k)
    (cap : ∀ v,(EvenFrom G v).card≤d+1)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x y : V) : G.dist x y < 2*(r+1) := by
  classical
  by_contra! far
  let L (i : ℕ) := Shell G x (2*(i+1))
  let E := (range r).biUnion L
  have pair : (range r : Set ℕ).PairwiseDisjoint L := by
    intro i _ j _ ne
    rw [Function.onFun,disjoint_left]
    intro z h q
    have a := mem_shell.mp h
    have b := mem_shell.mp q
    omega
  have layer (i : ℕ) (hi : i ∈ range r) : k ≤ (L i).card := by
    have ir := mem_range.mp hi
    exact shell_card_of_far hc k conn (x:=x) (y:=y) (i:=2*(i+1)) (by omega) (by omega)
  have nE : r*k ≤ E.card := by
    dsimp only [E]
    rw [card_biUnion pair]
    calc
      r*k = ∑ _i ∈ range r,k := by simp
      _ ≤ _ := sum_le_sum layer
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  let w := p.getVert (2*(r+1))
  have dw : G.dist x w = 2*(r+1) := distance_on_geodesic hc p hp _ (by omega)
  have dxw : x ≠ w := by intro e; rw [←e,dist_self] at dw; omega
  have xE : x ∉ E := by
    intro he
    obtain ⟨i,_,im⟩ := mem_biUnion.mp he
    have di := mem_shell.mp im
    rw [dist_self] at di
    omega
  have wE : w ∉ E := by
    intro he
    obtain ⟨i,ir,im⟩ := mem_biUnion.mp he
    have di := mem_shell.mp im
    have j := mem_range.mp ir
    omega
  have xEw : x ∉ insert w E := fun h => (mem_insert.mp h).elim dxw xE
  have sub : insert x (insert w E) ⊆ EvenFrom G x := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zo
    · simp [EvenFrom,dist_self]
    rcases mem_insert.mp zo with rfl|ze
    · exact mem_filter.mpr ⟨mem_univ _,by rw [dw]; exact even_two_mul _⟩
    obtain ⟨i,_,im⟩ := mem_biUnion.mp ze
    have di := mem_shell.mp im
    exact mem_filter.mpr ⟨mem_univ _,by rw [di]; exact even_two_mul _⟩
  have count := card_le_card sub
  rw [card_insert_of_not_mem xEw,card_insert_of_not_mem wE] at count
  have h := cap x
  omega

theorem distance_le_seven_at_degree_six_two_connected
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x y : V) : G.dist x y ≤ 7 := by
  have h := distance_lt_of_consumed_even_layers hc 6 2 3 (by decide) cap conn x y
  omega

theorem distance_le_five_at_degree_six_three_connected
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x y : V) : G.dist x y ≤ 5 := by
  have h := distance_lt_of_consumed_even_layers hc 6 3 2 (by decide) cap conn x y
  omega

#print axioms distance_le_seven_at_degree_six_two_connected
#print axioms distance_le_five_at_degree_six_three_connected
end Graffiti189LongestPath
