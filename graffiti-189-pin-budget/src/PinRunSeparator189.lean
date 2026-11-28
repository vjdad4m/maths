import OneSlack189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open private Graffiti189LongestPath.OneSlack.boundary_lower
  Graffiti189LongestPath.OneSlack.smaller_boundary_after_removing_porter from OneSlack189
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti189LongestPath
namespace PinRun
open OneSlack Rigidity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma pins_count {a b : V} (p : G.Walk a b) (x : V)
    :
    (PairedPins p x = ∅ ∧ (FirstPins p x).card = (Pins p x).card) ∨
      (Pins p x).card+1 ≤ (PairedPins p x).card+(FirstPins p x).card := by
  classical
  let I := Pins p x
  let P := PairedPins p x
  let R := FirstPins p x
  have pI {i : ℕ} (hi : i ∈ P) := (mem_filter.mp hi).1
  have rp {i : ℕ} (hi : i ∈ I) (hr : i ∉ R) : i ∈ P := by
    by_contra! hn
    exact hr (mem_filter.mpr ⟨hi,fun j hj e => hn (mem_filter.mpr ⟨hi,j,hj,Or.inl e⟩)⟩)
  have cov : I ⊆ P∪R := by
    intro i hi
    by_cases h : i ∈ R
    · exact mem_union.mpr (Or.inr h)
    · exact mem_union.mpr (Or.inl (rp hi h))
  by_cases hn : P.Nonempty
  · right
    let i := P.min' hn
    have hi : i ∈ P := P.min'_mem hn
    have hr : i ∈ R := by
      refine mem_filter.mpr ⟨pI hi,?_⟩
      intro j hj e
      have hJ : j ∈ P := mem_filter.mpr ⟨hj,i,pI hi,Or.inr e⟩
      have hge : i ≤ j := P.min'_le _ hJ
      omega
    have hInter : 1 ≤ (P∩R).card := Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr ⟨hi,hr⟩⟩
    have hP := Finset.card_union_add_card_inter P R
    have hi := Finset.card_le_card cov
    change I.card+1 ≤ P.card+R.card
    omega
  · left
    have hE := Finset.not_nonempty_iff_eq_empty.mp hn
    refine ⟨hE,?_⟩
    have he : R = I := Finset.Subset.antisymm (filter_subset ..) (by
      intro i hi
      by_contra hr
      have bad := rp hi hr
      simp [hE] at bad)
    change R.card = I.card
    rw [he]

/-- At any connectivity k, a high-degree vertex outside a longest path with
a path neighbor has at most d-k minus its distance-four population contacts. -/
theorem high_omitted_pin_budget (hc : G.Connected) (d k : ℕ)
    (cap : ∀ v, (EvenFrom G v).card ≤ d+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (ex : G.Adj x y)
    (hd : d ≤ G.degree x) :
    k+(Pins p x).card+(Shell G x 4).card ≤ d := by
  classical
  have b := boundary_flank_count hc hp hx
  rw [flank_count_exact hp hx] at b
  have bLow := Graffiti189LongestPath.OneSlack.boundary_lower k hp hx conn
  have he := shell_two_four_le_of_even (cap x)
  rw [shell_two] at he
  rcases pins_count p x with ⟨_,e⟩ | h
  · omega
  · obtain ⟨z,ez,hz⟩ := omitted_has_omitted_neighbor hc hp hx hd ⟨y,ex⟩
      (distanceTwo_le_of_even d x (cap x))
    have hh := Graffiti189LongestPath.OneSlack.smaller_boundary_after_removing_porter k hp hx conn hz ez
    omega

#print axioms high_omitted_pin_budget
end PinRun
end Graffiti189LongestPath
