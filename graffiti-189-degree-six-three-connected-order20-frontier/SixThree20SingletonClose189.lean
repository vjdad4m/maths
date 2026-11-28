import SixThree20ExtremeSwap189

namespace Graffiti189LongestPath.SixThreeTwenty
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

theorem all_other_slots_marked_eighteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=18) {x : V} (hx : x∉p.support) :
    ∀ k,k<p.length → k∉Pins p x → k+1∉Pins p x → k∈LM p ∨ k∈RM p := by
  classical
  have long : 15≤p.length := by omega
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
  have eq : I∪J=Holes p := by
    apply eq_of_subset_of_card_le (union_subset holeI holeJ)
    rw [card_union_of_disjoint dis,jc,pc]
    omega
  intro k kl nk nk'
  by_contra no
  have h : k∈Holes p := mem_sdiff.mpr ⟨mem_range.mpr kl,fun u=>no (mem_union.mp u)⟩
  rcases mem_union.mp (eq.symm ▸ h) with h|h
  · exact nk h
  obtain ⟨j,jp,e⟩ := mem_image.mp h
  change j-1=k at e
  have pj := pos j jp
  have h : k+1=j := by omega
  exact nk' (h.symm ▸ jp)

theorem consecutive_pin_pair {a b : V} {p : G.Walk a b} {x : V}
    (pc : 2≤(Pins p x).card) :
    ∃ i∈Pins p x,∃ j∈Pins p x,i<j ∧ ∀ k∈Pins p x,¬(i<k ∧ k<j) := by
  classical
  let I := Pins p x
  have non : I.Nonempty := card_pos.mp (by change 2≤I.card at pc; omega)
  let i := I.min' non
  have im : i∈I := min'_mem I non
  have pos : (I.erase i).Nonempty := card_pos.mp (by
    rw [card_erase_of_mem im]
    change 2≤I.card at pc
    omega)
  let j := (I.erase i).min' pos
  have jm : j∈I.erase i := min'_mem _ pos
  obtain ⟨ji,jI⟩ := mem_erase.mp jm
  have ij : i≤j := min'_le I _ jI
  refine ⟨i,im,j,jI,by omega,?_⟩
  intro k km h
  have kI : k∈I.erase i := mem_erase.mpr ⟨by omega,km⟩
  have jk := min'_le (I.erase i) k kI
  change j≤k at jk
  omega

theorem no_nonspanning_length_eighteen_at_twenty (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=18) {x : V} (hx : x∉p.support) : False := by
  classical
  have long : 15≤p.length := by omega
  have pins := (saturated_flanks hc conn cap degree ord hp long hx).1
  have marks := all_other_slots_marked_eighteen hc conn cap degree ord hp len hx
  obtain ⟨i,ip,j,jp,ij,middle⟩ := consecutive_pin_pair (p:=p) (x:=x) (by omega)
  have jl := (Graffiti189LongestPath.pin_data jp).1
  have iGap : i+3≤j := by
    by_contra! small
    have gap : j=i+1 ∨ j=i+2 := by omega
    rcases gap with e|e
    · exact pin_indices_not_consecutive hp hx ip (e ▸ jp)
    exact no_gap_two hc conn cap degree ord hp long hx ip (e ▸ jp)
  have leftFlank : p.getVert (i+1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx
      (mem_image.mpr ⟨i+1,mem_union_right _ (mem_image.mpr ⟨i,ip,rfl⟩),rfl⟩))).1
  have rightFlank : p.getVert (j-1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx
      (mem_image.mpr ⟨j-1,mem_union_left _ (mem_image.mpr ⟨j,jp,rfl⟩),rfl⟩))).1
  have mr : i+1∈RM p := by
    rcases marks (i+1) (by omega)
      (fun m=>middle _ m ⟨by omega,by omega⟩) (fun m=>middle _ m ⟨by omega,by omega⟩) with l|r
    · exact (left_mark_not_flank_long hc conn cap degree ord hp long hx l leftFlank).elim
    exact r
  have big : i+4≤j := by
    by_contra! no
    have e : i+1+1=j-1 := by omega
    exact right_mark_not_flank_long hc conn cap degree ord hp long hx mr (e.symm ▸ rightFlank)
  have ml : j-2∈LM p := by
    rcases marks (j-2) (by omega)
      (fun m=>middle _ m ⟨by omega,by omega⟩) (fun m=>middle _ m ⟨by omega,by omega⟩) with l|r
    · exact l
    have e : j-2+1=j-1 := by omega
    exact (right_mark_not_flank_long hc conn cap degree ord hp long hx r (e.symm ▸ rightFlank)).elim
  obtain ⟨q,hq,same,index⟩ := rotate_start_indexed_prefix hp (j-2) (by omega) (mem_filter.mp ml).2
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have ql := hq.2 a b p hp.1
  let k := j-2-i
  have e : q.getVert k=p.getVert i := by
    rw [index k (by dsimp only [k]; omega)]
    congr 1
    dsimp only [k]
    omega
  have f : q.getVert (k-1)=p.getVert (i+1) := by
    rw [index (k-1) (by dsimp only [k]; omega)]
    congr 1
    dsimp only [k]
    omega
  have kp : k∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by dsimp only [k]; omega),
    by rw [e]; exact (Graffiti189LongestPath.pin_data ip).2⟩
  apply end_not_adj_pin_predecessor hq xq kp
  rw [f]
  exact (mem_filter.mp mr).2

#print axioms no_nonspanning_length_eighteen_at_twenty
end Graffiti189LongestPath.SixThreeTwenty
