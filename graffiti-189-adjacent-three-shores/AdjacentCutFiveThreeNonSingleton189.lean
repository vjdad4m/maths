import AdjacentCutFiveComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_nonempty
  from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two degree_le_shore_add_one foreign_pos_even degree_le_shore
  shore_sum_budget count_sum positive_cap from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Three nonsingleton shores at an adjacent degree-five cut always
include an entirely high shore of size at most seven. -/
theorem exists_small_high_shore_of_three_no_singleton (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (noSingleton : ∀ C : (CutGraph (G := G) a b).ConnectedComponent, (Shore C).card ≠ 1) :
    ∃ C : (CutGraph (G := G) a b).ConnectedComponent,
      4 ≤ (Shore C).card ∧ (Shore C).card ≤ 7 ∧ ∀ z∈Shore C,5 ≤ G.degree z := by
  classical
  let J := CutGraph (G := G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n21 : Fintype.card V ≤ 21 := order_le_twenty_one_of_actual_adjacent_cut hc ab even conn
    (by rw [three]; decide)
  change Nat.card J.ConnectedComponent = 3 at three
  rw [Nat.card_eq_fintype_card] at three
  let U : Finset J.ConnectedComponent := univ
  have u3 : U.card = 3 := by simpa [U]
  have sum : (∑ C∈U,(Shore C).card) ≤ 19 :=
    Nat.le_of_add_le_add_right ((shore_sum_budget ab.ne U).trans
      (show Fintype.card V ≤ 19+2 from n21))
  have all4 (C : J.ConnectedComponent) : 4 ≤ (Shore C).card := by
    obtain ⟨x,xc⟩ := shore_nonempty C
    have Cpos := card_pos.mpr (shore_nonempty C)
    have n1 := noSingleton C
    have k := card_erase_add_one xc
    obtain ⟨y,ym⟩ : ((Shore C).erase x).Nonempty := card_pos.mp (by omega)
    rcases degree y x (mem_erase.mp ym).1 with dy|dx
    · have h := degree_le_shore_add_one C (mem_erase.mp ym).2
      omega
    · have h := degree_le_shore_add_one C xc
      omega
  by_cases lo : ∃ (D : J.ConnectedComponent) (z : V), z∈Shore D ∧ G.degree z < 5
  · obtain ⟨D,z,zd,lo⟩ := lo
    have du : D∈U := mem_univ _
    let T := U.erase D
    have t2 : T.card = 2 := by
      have h := card_erase_add_one du
      change T.card + 1 = U.card at h
      omega
    have ht : ∀ C∈T,∀ x∈Shore C, 5≤G.degree x := by
      intro C ct x xc
      have ne : z≠x := fun e => disjoint_left.mp
        (shore_disjoint (mem_erase.mp ct).1) xc (e.symm ▸ zd)
      exact (degree z x ne).resolve_left (by omega)
    by_cases small : ∃ C∈T, (Shore C).card ≤ 7
    · obtain ⟨C,ct,small⟩ := small
      exact ⟨C,all4 C,small,ht C ct⟩
    · push_neg at small
      have cnt : T.card * 8 ≤ ∑ C∈T,(Shore C).card := count_sum T Shore 8 (fun C ct=>small C ct)
      have eq : (∑ C∈T,(Shore C).card) + (Shore D).card = ∑ C∈U,(Shore C).card :=
        sum_erase_add U (fun C=>(Shore C).card) du
      have d := all4 D
      omega
  · push_neg at lo
    by_cases small : ∃ C∈U, (Shore C).card ≤ 7
    · obtain ⟨C,_,small⟩ := small
      exact ⟨C,all4 C,small,lo C⟩
    · push_neg at small
      have cnt : U.card * 8 ≤ ∑ C∈U,(Shore C).card := count_sum U Shore 8 (fun C cm=>small C cm)
      exact ((Nat.not_le_of_gt (show 19 < U.card * 8 by omega)) (cnt.trans sum)).elim

#print axioms exists_small_high_shore_of_three_no_singleton
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
