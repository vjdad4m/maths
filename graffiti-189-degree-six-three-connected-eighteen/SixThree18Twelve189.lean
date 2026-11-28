import SixThree18Marks189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.mem_distanceTwo from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.dist_two from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem not_length_twelve_of_three_active (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=12)
    (da : 6≤G.degree a) (db : 6≤G.degree b)
    (A : Finset V) (Acard : 3≤A.card)
    (active : ∀ v∈A,v∉p.support ∧ (Pins p v).Nonempty) : False := by
  classical
  obtain ⟨x,xm⟩ : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨hx,i,ip⟩ := active x xm
  obtain ⟨lc,rc,full⟩ := full_marks hp len da db hx ip
  have lr := left_right_disjoint hp hx ip
  let L := (LM p).image p.getVert
  let R := (RM p).image (fun j=>p.getVert (j+1))
  let E := L∪R
  have leftCard : L.card=6 := by
    have e : L.card=(LM p).card := card_image_iff.mpr (fun j jm k km eq=>
      hp.1.getVert_injOn (mem_range.mp (mem_filter.mp jm).1).le (mem_range.mp (mem_filter.mp km).1).le eq)
    exact e.trans lc
  have rightCard : R.card=6 := by
    have e : R.card=(RM p).card := card_image_iff.mpr (fun j jm k km eq=>by
      have jl := mem_range.mp (mem_filter.mp jm).1
      have kl := mem_range.mp (mem_filter.mp km).1
      have t := hp.1.getVert_injOn (by omega : j+1≤p.length) (by omega : k+1≤p.length) eq
      omega)
    exact e.trans rc
  have aL : a∈L := by
    have e := p.adj_getVert_succ (i:=0) (by omega)
    have m : 0∈LM p := mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa using e⟩
    exact mem_image.mpr ⟨0,m,p.getVert_zero⟩
  have aR : a∉R := by
    intro m
    obtain ⟨j,jm,je⟩ := mem_image.mp m
    have jl := mem_range.mp (mem_filter.mp jm).1
    have t := hp.1.getVert_injOn (by omega : j+1≤p.length) (Nat.zero_le _)
      (je.trans p.getVert_zero.symm)
    omega
  have highHit {v : V} (ve : v∈E) (dv : 6≤G.degree v) : G.Adj v (p.getVert i) := by
    rcases mem_union.mp ve with l|r
    · obtain ⟨j,jm,rfl⟩ := mem_image.mp l
      exact marked_left_candidates_see_pin hp len db hx ip jm dv
    obtain ⟨j,jm,rfl⟩ := mem_image.mp r
    exact marked_right_candidates_see_pin hp len da hx ip jm dv
  have on {v : V} (ve : v∈E) : v∈p.support := by
    rcases mem_union.mp ve with l|r
    · obtain ⟨j,jm,rfl⟩ := mem_image.mp l
      exact p.getVert_mem_support j
    obtain ⟨j,jm,rfl⟩ := mem_image.mp r
    exact p.getVert_mem_support (j+1)
  have noX {v : V} (ve : v∈E) : ¬G.Adj x v := by
    intro e
    rcases mem_union.mp ve with l|r
    · obtain ⟨j,jm,rfl⟩ := mem_image.mp l
      have pin : j∈Pins p x := mem_filter.mpr ⟨(mem_filter.mp jm).1,e⟩
      exact start_not_adj_pin_successor hp hx pin (mem_filter.mp jm).2
    obtain ⟨j,jm,rfl⟩ := mem_image.mp r
    have jl := mem_range.mp (mem_filter.mp jm).1
    by_cases h : j+1=p.length
    · rw [h,getVert_length] at e
      exact (Graffiti189LongestPath.no_endpoints hp hx).2 e
    have pin : j+1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩
    apply end_not_adj_pin_predecessor hp hx pin
    rw [show j+1-1=j by omega]
    exact (mem_filter.mp jm).2
  have charged : E.filter (fun v=>6≤G.degree v)⊆DistanceTwo G x := by
    intro v vm
    obtain ⟨ve,dv⟩ := mem_filter.mp vm
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc
        (fun h=>hx (h.symm ▸ on ve)) (noX ve)
        (Graffiti189LongestPath.pin_data ip).2 (highHit ve dv).symm)
  have ecap : E.card≤7 := by
    have m := high_filter_card degree E
    have n := (card_le_card charged).trans (distanceTwo_le_of_even 6 x (cap x))
    omega
  have part : (L\R).card≤1 := by
    have sub : (L\R)∪R⊆E := union_subset (sdiff_subset.trans subset_union_left) subset_union_right
    have dis : Disjoint (L\R) R :=
      disjoint_left.mpr (fun v l r=>(mem_sdiff.mp l).2 r)
    have d := card_le_card sub
    rw [card_union_of_disjoint dis,rightCard] at d
    omega
  have other {v : V} (vl : v∈L) (va : v≠a) : v∈R := by
    by_contra vr
    exact va (card_le_one.mp part v (mem_sdiff.mpr ⟨vl,vr⟩) a (mem_sdiff.mpr ⟨aL,aR⟩))
  let C := (L.erase a).filter (fun v=>6≤G.degree v)
  have ca : 4≤C.card := by
    have d := high_filter_card degree (L.erase a)
    rw [card_erase_of_mem aL,leftCard] at d
    have eq : C.card = ((L.erase a).filter (fun v=>6≤G.degree v)).card := rfl
    exact by omega
  have chargeC : C⊆DistanceTwo G a := by
    intro v vm
    obtain ⟨ve,dv⟩ := mem_filter.mp vm
    obtain ⟨va,vl⟩ := mem_erase.mp ve
    have vr := other vl va
    obtain ⟨k,kr,ke⟩ := mem_image.mp vr
    have kb := mem_range.mp (mem_filter.mp kr).1
    have no : ¬G.Adj a v := by
      intro hit
      have lm : k∈LM p := mem_filter.mpr ⟨mem_range.mpr kb,by rwa [ke]⟩
      exact disjoint_left.mp lr lm kr
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc va.symm no
        (both_ends_see_pin hp full hx ip).1 (highHit (mem_union_left _ vl) dv).symm)
  have chargeA : A⊆DistanceTwo G a := by
    intro y ym
    obtain ⟨yo,j,jp⟩ := active y ym
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc
        (fun e=>yo (e ▸ p.start_mem_support))
        (fun e=>(Graffiti189LongestPath.no_endpoints hp yo).1 e.symm)
        (both_ends_see_pin hp full yo jp).1 (Graffiti189LongestPath.pin_data jp).2.symm)
  have sep : Disjoint C A := disjoint_left.mpr (fun v vm va=>
    (active v va).1 (on (mem_union_left _ (mem_erase.mp (mem_filter.mp vm).1).2)))
  have n := (card_le_card (union_subset chargeC chargeA)).trans (distanceTwo_le_of_even 6 a (cap a))
  rw [card_union_of_disjoint sep] at n
  omega

#print axioms not_length_twelve_of_three_active
end Graffiti189LongestPath.SixThreeEighteen
