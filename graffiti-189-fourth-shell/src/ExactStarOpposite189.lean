import TruncatedHall189
import StarSize189
import UltraOrder189
import SixBorder189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.TruncatedHall
open Graffiti189LongestPath.UltraOrder Graffiti189LongestPath.StarSize Graffiti189LongestPath.SixBorder
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
namespace Graffiti189LongestPath.ExactStarOpposite
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At d≥6, any active high-degree omitted star with at most two pins
and an exact-size boundary excludes a small complementary component. -/
theorem traceable_of_small_opposite (hc : G.Connected) (k : Nat) (hk : 4≤k)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (deg : ∀ u v : V, u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (high : k+2≤G.degree x) (active : 0<(Pins p x).card) (few : (Pins p x).card≤2)
    (exactCut : (External G (OmittedStar p x)).card=k)
    (C : Finset V) (cn : C.Nonempty) (small : 2*C.card≤k+3)
    (ca : Disjoint C (OmittedStar p x)) (cb : Disjoint C (External G (OmittedStar p x)))
    (edgeC : ∀ z∈C,∀ w∉C,G.Adj z w → w∈External G (OmittedStar p x)) :
    ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ ∀ z, z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  let d := k+2
  let A := OmittedStar p x
  let B := External G A
  let R : Finset V := univ \ (A∪B∪C)
  have exactB : B.card=k := exactCut
  have xx : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have large : k≤A.card := by
    have sub : G.neighborFinset x ⊆ PinVertices p x ∪ A.erase x := by
      intro v hv
      have ed := (G.mem_neighborFinset x v).mp hv
      by_cases pV : v∈p.support
      · obtain ⟨i,hi,e⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx pV ed
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,e⟩))
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨ed.ne.symm,
          Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨pV,Or.inr ed⟩⟩))
    have co := card_le_card sub
    have cu := card_union_le (PinVertices p x) (A.erase x)
    rw [G.card_neighborFinset_eq_degree] at co
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,card_erase_of_mem xx] at cu
    omega
  have ab : Disjoint A B := disjoint_left.mpr (fun _ ha hb =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp hb).1 ha)
  have edgeA : ∀ z∈A,∀ w∉A,G.Adj z w → w∈B := fun _ hz _ hw e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hw,_,hz,e⟩
  have edgeR : ∀ z∈R,∀ w∉R,G.Adj z w → w∈B := by
    intro z hz w hw ed
    have zr := (mem_sdiff.mp hz).2
    have cov : w∈A∪B∪C := Classical.byContradiction (fun h => hw (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    rcases mem_union.mp cov with h|h
    · rcases mem_union.mp h with h|h
      · exact (zr (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
          (edgeA w h z (fun e => zr (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl e))))) ed.symm)))))).elim
      · exact h
    · exact (zr (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
        (edgeC w h z (fun e => zr (mem_union.mpr (Or.inr e))) ed.symm)))))).elim
  have pick : ∃ z∈C, k+2≤G.degree z ∨ C.card=1 := by
    by_cases singleton : C.card=1
    · obtain ⟨z,hz⟩ := cn
      exact ⟨z,hz,Or.inr singleton⟩
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp (show 1<C.card from by
      have cc := card_pos.mpr cn
      omega)
    rcases deg u v ne with h|h
    · exact ⟨u,hu,Or.inl h⟩
    · exact ⟨v,hv,Or.inl h⟩
  obtain ⟨z,hz,dz⟩ := pick
  let S := B.filter (G.Adj z)
  have za : z∉A := fun h => disjoint_left.mp ca hz h
  have zb : z∉B := fun h => disjoint_left.mp cb hz h
  have zr : z∉R := fun h => (mem_sdiff.mp h).2 (mem_union.mpr (Or.inr hz))
  have db : G.degree z≤(C.erase z).card+S.card := by
    have su : G.neighborFinset z ⊆ C.erase z ∪ S := by
      intro w hw
      have e := (G.mem_neighborFinset z w).mp hw
      by_cases h : w∈C
      · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨e.ne.symm,h⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨edgeC z hz w h e,e⟩))
    have c := card_le_card su
    rw [G.card_neighborFinset_eq_degree] at c
    exact c.trans (card_union_le _ _)
  have eras := card_erase_add_one hz
  have lowerZ : k≤G.degree z := by
    have nA : a∉A := fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 p.start_mem_support
    have cA : x≠z := fun e => za (e ▸ xx)
    rw [← G.card_neighborFinset_eq_degree]
    apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={z}) (a:=x)
    · exact mem_singleton_self _
    · exact fun h => cA (mem_singleton.mp h)
    · intro h
      have e := edgeC z hz x (fun h => (disjoint_left.mp ca h xx).elim)
        ((G.mem_neighborFinset z x).mp h)
      exact (Graffiti189LongestPath.Rigidity.mem_external.mp e).1 xx
    · exact disjoint_left.mpr (fun v h e => ((G.mem_neighborFinset z v).mp e).ne (mem_singleton.mp h).symm)
    · exact fun v h w _ e => (G.mem_neighborFinset z w).mpr ((mem_singleton.mp h) ▸ e)
  have many : d<2*S.card := by
    rcases dz with h|h <;> dsimp [d] <;> omega
  have charge := across_two_shores_budget hc d k A R B conn ab
    (disjoint_left.mpr (fun _ hr hb => (mem_sdiff.mp hr).2 (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hb))))))
    (disjoint_left.mpr (fun _ ha hr => (mem_sdiff.mp hr).2 (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl ha))))))
    exactB large za zr zb edgeA edgeR (cap z) many
  change R.card+S.card≤d at charge
  have total : Fintype.card V ≤ A.card+B.card+C.card+R.card := by
    have cov : (univ:Finset V) ⊆ A∪B∪C∪R := by
      intro v _
      by_cases h : v∈A∪B∪C
      · exact mem_union.mpr (Or.inl h)
      · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    have c := card_le_card cov
    rw [card_univ] at c
    have ab := card_union_le A B
    have ac := card_union_le (A∪B) C
    have ar := card_union_le (A∪B∪C) R
    omega
  obtain ⟨i,hi⟩ := card_pos.mp active
  have upper := (star_order_of_pin hc d (fun v => distanceTwo_le_of_even d v (cap v)) hp hx hi).1
  change A.card≤2*d at upper
  dsimp [d] at upper charge
  by_cases eq : k=4
  · have floor := order_lower_six_border hc k eq cap conn deg fail
    rcases dz with h|h <;> omega
  · have floor := order_lower_wings_sharp hc k (by omega) cap conn deg fail
    rcases dz with h|h <;> omega

#print axioms traceable_of_small_opposite
end Graffiti189LongestPath.ExactStarOpposite
