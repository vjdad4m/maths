import SixThree21ExtremeSwap189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (LM RM left_right_disjoint)
open Graffiti189LongestPath.SixThreeNineteen (Holes missed_start_hole missed_end_hole pin_indices_not_consecutive)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos Graffiti189LongestPath.Rigidity.reverse_longest
  Graffiti189LongestPath.Rigidity.pin_reverse Graffiti189LongestPath.Rigidity.card_leftMarks
  Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def ExtraHoles {a b : V} (p : G.Walk a b) (x : V) : Finset ℕ :=
  Holes p \ ((Pins p x) ∪ (Pins p x).image (·-1))

theorem extra_holes_card_le_one_nineteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=19) {x : V} (hx : x∉p.support) :
    (ExtraHoles p x).card≤1 := by
  classical
  have long : 16≤p.length := by omega
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have da : 6≤G.degree a := (degree a x (fun h=>hx (h ▸ p.start_mem_support))).resolve_right (by omega)
  have db : 6≤G.degree b := (degree b x (fun h=>hx (h ▸ p.end_mem_support))).resolve_right (by omega)
  have no1 := no_extreme_pin_long hc conn cap degree ord hp long hx
  have noLast : p.length-1∉Pins p x := by
    intro pin
    have e := Graffiti189LongestPath.Rigidity.pin_reverse hp hx pin
    rw [show p.length-(p.length-1)=1 by omega] at e
    exact no_extreme_pin_long hc conn cap degree ord
      (Graffiti189LongestPath.Rigidity.reverse_longest hp)
      (by simpa using long) (by simpa using hx) e
  let I := Pins p x
  let J := I.image (·-1)
  have pc : I.card=3 := (saturated_flanks hc conn cap degree ord hp long hx).1
  have pos (i : ℕ) (ip : i∈I) : 0<i := Graffiti189LongestPath.Rigidity.pin_pos hp hx ip
  have jc : J.card=I.card := card_image_iff.mpr (fun i ip j jp e=>by
    change i-1=j-1 at e
    have pi := pos i ip
    have pj := pos j jp
    omega)
  have dis : Disjoint I J := by
    apply disjoint_left.mpr
    intro i im jm
    obtain ⟨j,jp,e⟩ := mem_image.mp jm
    change j-1=i at e
    have pj := pos j jp
    have h : i+1=j := by omega
    exact pin_indices_not_consecutive hp hx im (h.symm ▸ jp)
  have holeI : I⊆Holes p := by
    intro i ip
    have ib := (Graffiti189LongestPath.pin_data ip).1
    have ne : i≠p.length-1 := fun h=>noLast (h ▸ ip)
    exact missed_end_hole hp hx ip (no_chord_to_pin_end hc conn cap degree ord hp long hx ip (by omega))
  have holeJ : J⊆Holes p := by
    intro j jm
    obtain ⟨i,ip,rfl⟩ := mem_image.mp jm
    have pi := pos i ip
    have ne : i≠1 := fun h=>no1 (h ▸ ip)
    exact missed_start_hole hp hx ip (no_chord_to_pin_start hc conn cap degree ord hp long hx ip (by omega))
  obtain ⟨i,ip⟩ : I.Nonempty := card_pos.mp (by omega)
  have marks := left_right_disjoint hp hx ip
  have sub : LM p∪RM p⊆range p.length := union_subset (filter_subset ..) (filter_subset ..)
  have n := card_sdiff_add_card_eq_card sub
  change (Holes p).card+(LM p∪RM p).card=(range p.length).card at n
  rw [card_union_of_disjoint marks,card_range,Graffiti189LongestPath.Rigidity.card_leftMarks hp,
    Graffiti189LongestPath.Rigidity.card_rightMarks hp] at n
  have D : (I∪J)⊆Holes p := union_subset holeI holeJ
  unfold ExtraHoles
  change (Holes p \ (I∪J)).card≤1
  rw [card_sdiff D,card_union_of_disjoint dis,jc,pc]
  omega

theorem mem_extra_holes_of_unmarked {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V}
    (hx : x∉p.support) {k : ℕ} (kl : k<p.length) (kp : k∉Pins p x)
    (k1 : k+1∉Pins p x) (no : ¬(k∈LM p ∨ k∈RM p)) : k∈ExtraHoles p x := by
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_range.mpr kl,fun m=>no (mem_union.mp m)⟩,?_⟩
  intro m
  rcases mem_union.mp m with i|j
  · exact kp i
  obtain ⟨r,rp,e⟩ := mem_image.mp j
  change r-1=k at e
  have r0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx rp
  have eq : r=k+1 := by omega
  exact k1 (eq ▸ rp)

#print axioms extra_holes_card_le_one_nineteen
end Graffiti189LongestPath.SixThreeTwentyOne
