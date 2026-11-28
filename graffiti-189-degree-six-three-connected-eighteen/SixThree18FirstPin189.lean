import SixThree18LowRotation189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.nonconsecutive_boundary
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nonspanning long path at the order-eighteen frontier must have the
first path neighbor as a pin of its unique omitted low vertex. -/
theorem first_pin_of_longest_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 13≤p.length) {x : V} (hx : x∉p.support) : 1∈Pins p x := by
  classical
  by_contra fail
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have da : 6≤G.degree a := (degree a x (fun e=>hx (e ▸ p.start_mem_support))).resolve_right (by omega)
  have db : 6≤G.degree b := (degree b x (fun e=>hx (e ▸ p.end_mem_support))).resolve_right (by omega)
  let P := Pins p x
  let Q := P.image (·-1)
  let T := ((P∪Q).erase 0).erase (p.length-1)
  have pc : P.card=3 := (saturated_flanks hc conn cap degree ord hp long hx).1
  have qc : Q.card=P.card := by
    apply card_image_iff.mpr
    intro i ih j jh e
    have ip := Graffiti189LongestPath.Rigidity.pin_pos hp hx ih
    have jp := Graffiti189LongestPath.Rigidity.pin_pos hp hx jh
    change i-1=j-1 at e
    omega
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro i ih iq
    obtain ⟨j,jh,e⟩ := mem_image.mp iq
    change j-1=i at e
    have jp := Graffiti189LongestPath.Rigidity.pin_pos hp hx jh
    have il := (Graffiti189LongestPath.pin_data ih).1
    have eq : i+1=j := by omega
    have bi := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx (mem_image.mpr ⟨i,ih,rfl⟩)
    have bj := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx (mem_image.mpr ⟨j,jh,rfl⟩)
    exact Graffiti189LongestPath.OneSlack.nonconsecutive_boundary hp hx il bi (eq.symm ▸ bj)
  have big : (P∪Q).card=6 := by rw [card_union_of_disjoint dis,qc,pc]
  have eras (A : Finset Nat) (i : Nat) : A.card≤(A.erase i).card+1 := by
    by_cases m : i∈A
    · rw [card_erase_add_one m]
    rw [erase_eq_of_not_mem m]
    omega
  have no0 : 0∉P∪Q := by
    intro m
    rcases mem_union.mp m with p0|q0
    · exact (Nat.lt_irrefl _) (Graffiti189LongestPath.Rigidity.pin_pos hp hx p0)
    obtain ⟨j,jp,e⟩ := mem_image.mp q0
    have jp0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx jp
    change j-1=0 at e
    have one : j=1 := by omega
    exact fail (one ▸ jp)
  have tc : 5≤T.card := by
    have f := eras (P∪Q) (p.length-1)
    have e : (P∪Q).erase 0=P∪Q := erase_eq_of_not_mem no0
    change (((P∪Q).erase 0).erase (p.length-1)).card≥5
    rw [e]
    omega
  let L := Graffiti189LongestPath.Rigidity.LeftMarks p
  let R := Graffiti189LongestPath.Rigidity.RightMarks p
  obtain ⟨k,kk⟩ : P.Nonempty := card_pos.mp (by omega)
  have lr : Disjoint L R := disjoint_left.mpr (fun i il ir=>
    not_adj_both_end_marks hp hx (p.getVert_mem_support k) (Graffiti189LongestPath.pin_data kk).2
      (mem_range.mp (mem_filter.mp il).1) (mem_filter.mp il).2 (mem_filter.mp ir).2)
  have data (i : Nat) (it : i∈T) : i<p.length ∧ i∉L ∧ i∉R := by
    obtain ⟨nl,it⟩ := mem_erase.mp it
    obtain ⟨nz,iu⟩ := mem_erase.mp it
    rcases mem_union.mp iu with ip|iq
    · have il := (Graffiti189LongestPath.pin_data ip).1
      exact ⟨il,fun h=>start_not_adj_pin_successor hp hx ip (mem_filter.mp h).2,
        fun h=>no_chord_to_pin_end hc conn cap degree ord hp long hx ip (by omega) (mem_filter.mp h).2⟩
    obtain ⟨j,jp,eq⟩ := mem_image.mp iq
    change j-1=i at eq
    have jl := (Graffiti189LongestPath.pin_data jp).1
    have sh : i+1=j := by omega
    refine ⟨by omega,?_,?_⟩
    · intro h
      have e := (mem_filter.mp h).2
      rw [sh] at e
      exact no_chord_to_pin_start hc conn cap degree ord hp long hx jp (by omega) e
    · intro h
      apply end_not_adj_pin_predecessor hp hx jp
      rw [eq]
      exact (mem_filter.mp h).2
  have dt : Disjoint (L∪R) T := disjoint_left.mpr (fun i iM iT=>
    (mem_union.mp iM).elim (data i iT).2.1 (data i iT).2.2)
  have sum : ((L∪R)∪T).card≤(range p.length).card := by
    apply card_le_card
    exact union_subset (union_subset (filter_subset ..) (filter_subset ..))
      (fun _ h=>mem_range.mpr (data _ h).1)
  rw [card_union_of_disjoint dt,card_union_of_disjoint lr,card_range] at sum
  change (Graffiti189LongestPath.Rigidity.LeftMarks p).card+
    (Graffiti189LongestPath.Rigidity.RightMarks p).card+T.card≤p.length at sum
  rw [Graffiti189LongestPath.Rigidity.card_leftMarks hp,
    Graffiti189LongestPath.Rigidity.card_rightMarks hp] at sum
  have off : x∉p.support.toFinset := fun h=>hx (List.mem_toFinset.mp h)
  have count := card_le_univ (insert x p.support.toFinset)
  rw [card_insert_of_not_mem off,List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at count
  omega


#print axioms first_pin_of_longest_long
end Graffiti189LongestPath.SixThreeEighteen
