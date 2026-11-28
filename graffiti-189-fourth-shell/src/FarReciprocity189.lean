import SingleStar189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Normalize Graffiti189LongestPath.SingleStar
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.FarReciprocity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A fourth-shell pair at the first-slack threshold is almost reciprocal
even without a longest-path condition on its far endpoint. -/
theorem fourth_shell_reciprocity (hc : G.Connected) (k : Nat) (hk : 3≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x w : V} (four : G.dist x w=4)
    (unique : (Shell G x 4).card≤1) :
    (Shell G w 4).card≤2 ∧
    (∀ z, G.Adj w z → G.dist x z=3) ∧
    ((G.neighborFinset x).filter (fun z => G.dist w z ≠ 3)).card≤1 := by
  classical
  have diam := diameter_bound_from_inner_even_layers hc (k+2) k 1 cap conn (by omega)
  have flip : G.dist w x=4 := by rwa [dist_comm]
  have k2 := shell_card_of_far hc k conn (x:=w) (y:=x) (i:=2) (by decide) (by omega)
  have cost := shell_two_four_le_of_even (cap w)
  have one : Shell G x 4 = {w} := by
    have sub : ({w}:Finset V) ⊆ Shell G x 4 := by
      intro z h
      exact (mem_singleton.mp h).symm ▸ mem_shell.mpr four
    exact (eq_of_subset_of_card_le sub (by simpa using unique)).symm
  have close : ∀ z, G.Adj w z → G.dist x z=3 := by
    intro z e
    have high := hc.dist_triangle (u:=x) (v:=z) (w:=w)
    have step : G.dist z w=1 := dist_eq_one_iff_adj.mpr e.symm
    have top := diam x z
    have no4 : G.dist x z ≠ 4 := by
      intro hz
      have h : z∈Shell G x 4 := mem_shell.mpr hz
      rw [one] at h
      exact e.ne (mem_singleton.mp h).symm
    omega
  refine ⟨by omega,close,?_⟩
  have sub : (G.neighborFinset x).filter (fun z => G.dist w z ≠ 3) ⊆ (Shell G w 4).erase x := by
    intro z hz
    have e := (G.mem_neighborFinset x z).mp (mem_filter.mp hz).1
    have bad := (mem_filter.mp hz).2
    have step : G.dist z x=1 := dist_eq_one_iff_adj.mpr e.symm
    have tr := hc.dist_triangle (u:=w) (v:=z) (w:=x)
    exact mem_erase.mpr ⟨e.ne.symm,mem_shell.mpr (by have top := diam w z; omega)⟩
  have ct := card_le_card sub
  have h := card_erase_add_one (mem_shell.mpr flip : x∈Shell G w 4)
  omega

/-- In a normalized singleton with a fourth-shell vertex, if that vertex is
also an omitted high-degree attachment, it must itself be an exactly
reciprocal singleton, with its only fourth-shell vertex the first root. -/
theorem reciprocal_active_is_single (hc : G.Connected) (k : Nat) (hk : 3≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x w : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p)
    (far : G.dist x w=4) (wo : w∉p.support) (high : k+2≤G.degree w)
    {i : Nat} (hi : i∈Pins p w) :
    (Pins p w).card=1 ∧ Shell G w 4 = {x} ∧
      (External G (OmittedStar p w)).card=k ∧
      DistanceTwo G w \ External G (OmittedStar p w) = FlankVertices p w := by
  classical
  have flip : G.dist w x=4 := by rwa [dist_comm]
  have hw4 : x∈Shell G w 4 := mem_shell.mpr flip
  have nn := normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp wo high i hi
  have pc := card_pos.mpr ⟨i,hi⟩
  have fc := card_pos.mpr ⟨x,hw4⟩
  have size : (Pins p w).card=1 := by omega
  have fs : Shell G w 4={x} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro z h
      exact (mem_singleton.mp h).symm ▸ hw4
    · rw [card_singleton]
      omega
  have c := singleton_star_budget hc k conn hp.1.1 wo size (cap w)
  obtain ⟨h₁,h₂⟩ := c.2.2.2.2.1 ⟨x,hw4⟩
  exact ⟨size,fs,h₁,h₂⟩

#print axioms fourth_shell_reciprocity
#print axioms reciprocal_active_is_single
end Graffiti189LongestPath.FarReciprocity
