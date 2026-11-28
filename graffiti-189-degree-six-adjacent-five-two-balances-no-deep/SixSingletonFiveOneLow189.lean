import SixSingletonFiveTwoCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 from SixSingletonFiveShallowRoute189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- With a single dark vertex whose dark degree is below four, route
the other seven first. If its only other potentially low vertex is
adjacent, make that vertex the penultimate one via weighted Ore. -/
theorem dark_route_with_one_low {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w : V} (zW : z∈D\S) (wW : w∈D\S) (zw : z≠w)
    (dw : 4≤(inside G D w).card) :
    ∃ l∈L,RouteOn G D l z := by
  classical
  let E := D.erase z
  have zd := (mem_sdiff.mp zW).1
  have wd := (mem_sdiff.mp wW).1
  have e7 : E.card=7 := by change (D.erase z).card=7; rw [card_erase_of_mem zd,d8]
  have sE : S⊆E := fun i im=>mem_erase.mpr ⟨fun h=>(mem_sdiff.mp zW).2 (h ▸ im),F.core_sub im⟩
  have wE : w∈E := mem_erase.mpr ⟨zw.symm,wd⟩
  have shape : D\S={z,w} := by
    have h : ({z,w}:Finset V)⊆D\S := insert_subset zW (singleton_subset_iff.mpr wW)
    exact (eq_of_subset_of_card_le h (by rw [F.balance,card_insert_of_not_mem (by simpa using zw),card_singleton])).symm
  have other (i : V) (im : i∈E) (iw : i≠w) : i∈S := by
    by_contra si
    have b : i∈D\S := mem_sdiff.mpr ⟨(mem_erase.mp im).2,si⟩
    rw [shape,mem_insert,mem_singleton] at b
    exact b.elim ((mem_erase.mp im).1) iw
  have four (i : V) (im : i∈E) (iw : i≠w) : 4≤(inside G E i).card := by
    have h := F.dark5 i (other i im iw)
    have p := erase_internal_deg (G:=G) D z i
    change (inside G D i).card≤(inside G E i).card+1 at p
    omega
  have wThree : 3≤(inside G E w).card := by
    have p := erase_internal_deg (G:=G) D z w
    change (inside G D w).card≤(inside G E w).card+1 at p
    omega
  have l2 : 1<L.card := by have h := F.l2; omega
  by_cases edge : G.Adj w z
  · obtain ⟨l,lm,lw⟩ := exists_ne_of_one_lt_card l2 w
    have r : RouteOn G E l w := by
      apply weighted_side_route E (sE (F.left_sub lm)) wE lw
      intro i im j jm ij _
      rw [e7]
      by_cases iw : i=w
      · subst i
        rw [if_pos (.inl rfl)]
        have hj := four j jm ij.symm
        omega
      by_cases jw : j=w
      · subst j
        rw [if_pos (.inr rfl)]
        have hi := four i im ij
        omega
      have hi := four i im iw
      have hj := four j jm jw
      omega
    have Q := r.suffix edge (by simp [E])
    change RouteOn G (insert z (D.erase z)) l z at Q
    rw [insert_erase zd] at Q
    exact ⟨l,lm,Q⟩
  have degreeW : 4≤(inside G E w).card := by
    have same : inside G E w=inside G D w := by
      ext i
      simp only [inside,E,mem_filter,mem_erase]
      exact ⟨fun h=>⟨h.1.2,h.2⟩,fun h=>⟨⟨fun e=>edge (e ▸ h.2),h.1⟩,h.2⟩⟩
    rwa [same]
  have neighbor : ∃ i∈E,G.Adj i z := by
    by_contra no
    have sub : G.neighborFinset z⊆P := by
      intro i im
      have e := (mem_neighborFinset _ _ _).mp im
      rcases mem_union.mp (F.darkBounds z zd i e) with m|m
      · exact (no ⟨i,mem_erase.mpr ⟨e.ne.symm,m⟩,e.symm⟩).elim
      exact m
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,p5] at h
    have q := F.darkHigh z zd
    omega
  obtain ⟨i,im,iz⟩ := neighbor
  obtain ⟨l,lm,li⟩ := exists_ne_of_one_lt_card l2 i
  have d (u : V) (um : u∈E) : 4≤(inside G E u).card := by
    by_cases eq : u=w
    · simpa only [eq] using degreeW
    exact four u um eq
  have r : RouteOn G E l i := terminal_route_on_of_local_ore E (sE (F.left_sub lm)) im li
    (fun u um v vm _ _=>by have k := d u um; have j := d v vm; omega)
  have Q := r.suffix iz (by simp [E])
  change RouteOn G (insert z (D.erase z)) l z at Q
  rw [insert_erase zd] at Q
  exact ⟨l,lm,Q⟩

#print axioms dark_route_with_one_low
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
