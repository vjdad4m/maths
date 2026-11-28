import HighDichotomy189
import MultiPinRotation189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Rigidity
open private Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.boundary_lower
  Graffiti189LongestPath.OneSlack.card_pinVertices Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.boundary_except_pins_two
  Graffiti189LongestPath.OneSlack.first_eq_if_no_pair from OneSlack189
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti189LongestPath.Interior

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem not_both_end_chords (hc : G.Connected) (k : Nat)
    (cap : ∀ v, (EvenFrom G v).card ≤ k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support)
    (two : (Pins p x).card≤2) (noPair : PairedPins p x = ∅)
    {i : Nat} (hi : i ∈ Pins p x) (interior : 2≤i ∧ i+2≤p.length) :
    ¬ (G.Adj a (p.getVert i) ∧ G.Adj b (p.getVert i)) := by
  classical
  intro ⟨ea,eb⟩
  let B := External G (OmittedStar p x)
  let F := PinVertices p x
  let T := FlankVertices p x
  let U := insert a (insert b T)
  have eab : a ≠ b := fun e => by
    have ev : p.getVert 0 = p.getVert p.length := by simpa only [getVert_zero,getVert_length] using e
    have h := hp.1.getVert_injOn (show 0≤p.length by omega) (show p.length≤p.length from le_rfl) ev
    omega
  have ix := (Graffiti189LongestPath.pin_data hi).2
  have na : a ∉ B := by
    intro h
    obtain ⟨_,u,hu,e⟩ := (mem_filter.mp h).2
    exact (Graffiti189LongestPath.no_endpoints hp ((mem_filter.mp hu).2.1)).1 e
  have nb : b ∉ B := by
    intro h
    obtain ⟨_,u,hu,e⟩ := (mem_filter.mp h).2
    exact (Graffiti189LongestPath.no_endpoints hp ((mem_filter.mp hu).2.1)).2 e
  have fa : a ∈ DistanceTwo G x :=
    Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc
      (fun e => hx (e.symm ▸ p.start_mem_support))
      (Graffiti189LongestPath.no_endpoints hp hx).1 ix ea.symm)
  have fb : b ∈ DistanceTwo G x :=
    Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc
      (fun e => hx (e.symm ▸ p.end_mem_support))
      (Graffiti189LongestPath.no_endpoints hp hx).2 ix eb.symm)
  have fit : U ⊆ DistanceTwo G x := by
    intro v hv
    rcases mem_insert.mp hv with rfl|ht
    · exact fa
    rcases mem_insert.mp ht with rfl|ht
    · exact fb
    exact (mem_sdiff.mp (flanks_outside_boundary hc hp hx ht)).1
  have dis : Disjoint U (B \ F) := disjoint_left.mpr (by
    intro v hv hB
    have ht := (mem_sdiff.mp hB).1
    rcases mem_insert.mp hv with rfl|hz
    · exact na ht
    rcases mem_insert.mp hz with rfl|hz
    · exact nb ht
    exact (mem_sdiff.mp (flanks_outside_boundary hc hp hx hz)).2 ht)
  have low := Graffiti189LongestPath.OneSlack.boundary_lower k hp hx conn
  have eCounts := card_sdiff_add_card_eq_card
    (Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx)
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp] at eCounts
  change (B \ F).card + (Pins p x).card = B.card at eCounts
  change k ≤ B.card at low
  have bound := distanceTwo_le_of_even (k+2) x (cap x)
  have hLe := card_le_card (union_subset fit
    (Graffiti189LongestPath.OneSlack.boundary_except_pins_two hc hp hx))
  rw [card_union_of_disjoint dis] at hLe
  have bc : U.card ≤ (Pins p x).card+2 := by omega
  have tc : T.card = 2*(Pins p x).card := by
    change (FlankVertices p x).card = _
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp,flank_count_exact hp hx,
      Graffiti189LongestPath.OneSlack.first_eq_if_no_pair noPair]
    omega
  have a_flank : a ∈ T → 1 ∈ Pins p x := by
    intro h
    obtain ⟨j,hj,e⟩ := mem_image.mp h
    rcases mem_union.mp hj with hj|hj
    · obtain ⟨u,hu,eu⟩ := mem_image.mp hj
      have ul := (Graffiti189LongestPath.pin_data hu).1
      have up := Graffiti189LongestPath.Rigidity.pin_pos hp hx hu
      have ej : p.getVert j = p.getVert 0 := e.trans p.getVert_zero.symm
      have jj := hp.1.getVert_injOn (show j≤p.length by omega) (Nat.zero_le _) ej
      have eq : u=1 := by omega
      exact eq ▸ hu
    · obtain ⟨u,hu,eu⟩ := mem_image.mp hj
      have ul := (Graffiti189LongestPath.pin_data hu).1
      have ej : p.getVert j = p.getVert 0 := e.trans p.getVert_zero.symm
      have jj := hp.1.getVert_injOn (show j≤p.length by omega) (Nat.zero_le _) ej
      omega
  have b_flank : b ∈ T → p.length-1 ∈ Pins p x := by
    intro h
    obtain ⟨j,hj,e⟩ := mem_image.mp h
    rcases mem_union.mp hj with hj|hj
    · obtain ⟨u,hu,eu⟩ := mem_image.mp hj
      have ul := (Graffiti189LongestPath.pin_data hu).1
      have ej : p.getVert j = p.getVert p.length := e.trans p.getVert_length.symm
      have jj := hp.1.getVert_injOn (show j≤p.length by omega) (show p.length≤p.length from le_rfl) ej
      omega
    · obtain ⟨u,hu,eu⟩ := mem_image.mp hj
      have ul := (Graffiti189LongestPath.pin_data hu).1
      have ej : p.getVert j = p.getVert p.length := e.trans p.getVert_length.symm
      have jj := hp.1.getVert_injOn (show j≤p.length by omega) (show p.length≤p.length from le_rfl) ej
      have eq : u = p.length-1 := by omega
      exact eq ▸ hu
  have hiPos : 0<(Pins p x).card := card_pos.mpr ⟨i,hi⟩
  by_cases h1 : (Pins p x).card = 1
  · have one := card_le_one.mp (show (Pins p x).card ≤ 1 by omega)
    have aa : a ∉ T := fun h => by
      have e := one _ hi _ (a_flank h)
      omega
    have bb : b ∉ T := fun h => by
      have e := one _ hi _ (b_flank h)
      omega
    have ax : a ∉ insert b T := fun h => (mem_insert.mp h).elim eab aa
    change (insert a (insert b T)).card ≤ _ at bc
    rw [card_insert_of_not_mem ax,card_insert_of_not_mem bb] at bc
    omega
  · have hboth : ¬ (a ∈ T ∧ b ∈ T) := by
      intro ⟨ha,hb⟩
      have sub : ({i,1,p.length-1} : Finset Nat) ⊆ Pins p x := by
        intro j hj
        simp only [mem_insert,mem_singleton] at hj
        rcases hj with rfl|rfl|rfl
        · exact hi
        · exact a_flank ha
        · exact b_flank hb
      have hcard := card_le_card sub
      have e1 : i ≠ 1 := by omega
      have e2 : i ≠ p.length-1 := by omega
      have e3 : 1 ≠ p.length-1 := by omega
      simp [e1,e2,e3] at hcard
      omega
    by_cases ha : a ∈ T
    · have hb : b ∉ T := fun h => hboth ⟨ha,h⟩
      have co : (insert b T).card ≤ U.card := card_le_card (subset_insert _ _)
      rw [card_insert_of_not_mem hb] at co
      omega
    · have co : (insert a T).card ≤ U.card := card_le_card (by
        intro x hx'
        rcases mem_insert.mp hx' with h|h
        · exact mem_insert.mpr (Or.inl h)
        · exact mem_insert.mpr (Or.inr (mem_insert_of_mem h)))
      rw [card_insert_of_not_mem ha] at co
      omega

#print axioms not_both_end_chords
end Graffiti189LongestPath.Interior
