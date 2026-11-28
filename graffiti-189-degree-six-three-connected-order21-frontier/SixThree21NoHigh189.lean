import SixThree21Saturation189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree rotate_start_first_edge)
open Graffiti189LongestPath.SixThreeEighteen (LM high_filter_card)
open Graffiti189LongestPath.SixThreeTwenty (CandL cand_left_card)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.nonconsecutive_boundary
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem first_pin_forced_high_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) (da : 6≤G.degree a) (db : 6≤G.degree b)
    {x : V} (hx : x∉p.support) (dx : 6≤G.degree x) : 1∈Pins p x := by
  classical
  by_contra fail
  have len := (high_pin_shape_long hc conn cap degree ord hp long hx dx).1
  let P := Pins p x
  let Q := P.image (·-1)
  let T := ((P∪Q).erase 0).erase (p.length-1)
  have pc : P.card=3 := (high_saturation_long hc conn cap degree ord hp long hx dx).1
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
        fun h=>high_pin_no_end_chord hc conn cap degree ord hp long hx dx ip (by omega) (mem_filter.mp h).2⟩
    obtain ⟨j,jp,eq⟩ := mem_image.mp iq
    change j-1=i at eq
    have jl := (Graffiti189LongestPath.pin_data jp).1
    have sh : i+1=j := by omega
    refine ⟨by omega,?_,?_⟩
    · intro h
      have e := (mem_filter.mp h).2
      rw [sh] at e
      exact high_pin_no_start_chord hc conn cap degree ord hp long hx dx jp (by omega) e
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
  omega

theorem all_omitted_low_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 16≤p.length)
    {x : V} (hx : x∉p.support) : G.degree x<6 := by
  classical
  by_contra! dx
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have ql := long.trans (hq.2 a b p hp.1)
  have pc := (high_pin_shape_long hc conn cap degree ord hq ql xq dx).2.2.1
  let I := (LM q).filter (fun j=>6≤G.degree (q.getVert j))
  let A := (CandL q).filter (fun y=>6≤G.degree y)
  have e : I.image q.getVert=A := by
    ext y
    constructor
    · intro m
      obtain ⟨j,jm,he⟩ := mem_image.mp m
      have d := (mem_filter.mp jm).2
      exact mem_filter.mpr ⟨mem_image.mpr ⟨j,(mem_filter.mp jm).1,he⟩,he ▸ d⟩
    intro m
    obtain ⟨jm,dy⟩ := mem_filter.mp m
    obtain ⟨j,jm,he⟩ := mem_image.mp jm
    exact mem_image.mpr ⟨j,mem_filter.mpr ⟨jm,he.symm ▸ dy⟩,he⟩
  have lower : 5≤I.card := by
    have d := high_filter_card degree (CandL q)
    change (CandL q).card≤A.card+1 at d
    rw [cand_left_card hq] at d
    have m : A.card≤I.card := e ▸ card_image_le
    omega
  let B := (Pins q x).image (·+1)
  have sub : I⊆insert 0 B := by
    intro j jm
    by_cases z : j=0
    · exact mem_insert.mpr (.inl z)
    obtain ⟨jl,dj⟩ := mem_filter.mp jm
    have jj := mem_range.mp (mem_filter.mp jl).1
    obtain ⟨r,hr,retain,hit⟩ := rotate_start_first_edge hq j (by omega) jj (mem_filter.mp jl).2
    have rl := ql.trans (hr.2 u v q hq.1)
    have xr : x∉r.support := fun h=>xq ((retain x).mpr h)
    have first := first_pin_forced_high_long hc conn cap degree ord hr rl dj dv xr dx
    have he := (Graffiti189LongestPath.pin_data first).2
    rw [hit] at he
    have pi : j-1∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),he⟩
    exact mem_insert_of_mem (mem_image.mpr ⟨j-1,pi,by omega⟩)
  have c1 := card_le_card sub
  have c2 := card_insert_le 0 B
  have c3 : B.card≤(Pins q x).card := card_image_le
  omega

#print axioms first_pin_forced_high_long
#print axioms all_omitted_low_long
end Graffiti189LongestPath.SixThreeTwentyOne
