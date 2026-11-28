import DiversityElevenElevenResidual384b
import TwoEarCompletion

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem eleven_two_lows (nine : (high G).card=9) (q : (nonleaves G).card=11) :
    ∃ e f, e ≠ f ∧ nonleaves G \ high G = {e,f} := by
  have hs : high G ⊆ nonleaves G := by
    intro x hx
    have d := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hc := card_sdiff_add_card_eq_card hs
  exact card_eq_two.mp (by omega)

theorem exact_eleven_ordinary_ears (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) (q : (nonleaves G).card=11)
    (ind : ∀ x∈nonleaves G \ high G, ∀ y∈nonleaves G \ high G, ¬G.Adj x y) :
    gamma G≤bound G := by
  classical
  obtain ⟨e,f,ef,ears⟩ := eleven_two_lows G nine q
  have el : e∈nonleaves G \ high G := ears ▸ mem_insert_self _ _
  have fl : f∈nonleaves G \ high G := ears ▸ mem_insert_of_mem (mem_singleton_self _)
  have tpair : LowSample.twos G = {e,f} := ears
  have safe {x y : V} (xl : x∈nonleaves G \ high G) (xy : G.Adj x y) : y∈high G := by
    obtain ⟨z,xz,yz⟩ := sup xy
    have incl : ({x,z}:Finset V) ⊆ G.neighborFinset y := by
      intro w wm
      simp only [mem_insert,mem_singleton] at wm
      rcases wm with rfl|rfl
      · exact (G.mem_neighborFinset ..).mpr xy.symm
      · exact (G.mem_neighborFinset ..).mpr yz
    have c := card_le_card incl
    rw [card_pair xz.ne,card_neighborFinset_eq_degree] at c
    by_contra out
    exact ind x xl y (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,c⟩,out⟩) xy
  by_cases sep : Disjoint (G.neighborFinset e) (G.neighborFinset f)
  · apply TriangleFrame.two_ears_equal_quota G tpair ef sep _ (t.trans q.symm)
    intro a ha
    obtain ⟨x,xl,xa⟩ := mem_biUnion.mp ha
    exact safe xl ((G.mem_neighborFinset ..).mp xa)
  · by_contra! bad
    rcases split_profile G sup t bad with ⟨qq,_⟩|⟨_,scores,mn,dg⟩
    · omega
    · let P := G.neighborFinset e ∪ G.neighborFinset f
      have size : P.card≤3 := by
        have h := card_union_add_card_inter (G.neighborFinset e) (G.neighborFinset f)
        rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,(dg e el).1,(dg f fl).1] at h
        have pos : 0<(G.neighborFinset e ∩ G.neighborFinset f).card :=
          card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (fun h => sep (disjoint_iff_inter_eq_empty.mpr h)))
        change P.card + (G.neighborFinset e ∩ G.neighborFinset f).card=4 at h
        omega
      have low : Disjoint (nonleaves G \ high G) (high G) :=
        disjoint_left.mpr (fun _ ax bx => (mem_sdiff.mp ax).2 bx)
      have two : 2≤(nonleaves G \ high G).card := by rw [ears,card_pair ef]
      apply (not_le_of_gt bad) (exact_of_two_low_footprint_three G finite_six_selector t nine
        scores mn two low (fun x xl => (dg x xl).1.ge) ind ?_ size)
      intro z _ hz
      obtain ⟨x,xl,xz⟩ := hz
      rw [ears,mem_insert,mem_singleton] at xl
      rcases xl with rfl|rfl
      · exact mem_union_left _ ((G.mem_neighborFinset ..).mpr xz)
      · exact mem_union_right _ ((G.mem_neighborFinset ..).mpr xz)

#print axioms eleven_two_lows
#print axioms exact_eleven_ordinary_ears
end Graffiti384b.DiversityEleven
