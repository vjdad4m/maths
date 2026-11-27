import FourOffTwinRows189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private hamilton_of_labeled_chain order_sixteen_four_off_labeling length_eleven_left_block_of_small_path_d2 left_boundary_porters_at_most_two right_boundary_porters_at_most_two from FourOffGraphCore189
open private mark_holes_of_pin_and_missing_endpoint from FourOffGraphSupport189

open OffFour16Twin in
private theorem length_eleven_boundary_left_chord_16
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)


    {a b x y : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (xo : x∉p.support) (yo : y∉p.support) (xy : x≠y)
    (h1 : 1∈Pins p x) (y1 : 1∈Pins p y) (hj : 10∈Pins p x) :
    G.Adj b (p.getVert 7) ∧ G.Adj b (p.getVert 8) := by
  classical
  let D := DistanceTwo G a
  let P := D.filter (· ∈ p.support)
  let Q := D.filter (· ∉ p.support)
  have px1 := (pin_data h1).2
  have first : G.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i:=0) (by omega)
  have dist {z : V} (zo : z∉p.support) (hp1 : 1∈Pins p z) : z∈Q :=
    mem_filter.mpr ⟨mem_distanceTwo.mpr (dist_two hc (fun e => zo (e ▸ p.start_mem_support))
      (fun e => (no_endpoints hp.1 zo).1 e.symm) first (pin_data hp1).2.symm),zo⟩
  have left2 : 2≤Q.card := one_lt_card.mpr ⟨x,dist xo h1,y,dist yo y1,xy⟩
  have eq := filter_card_add_filter_neg_card_eq_card (s:=D) (· ∈ p.support)
  have cap : D.card≤4 := distanceTwo_le_of_even 4 a (even a)
  have small : P.card≤2 := by
    change P.card+Q.card=D.card at eq
    omega
  obtain ⟨t,tge,tle,back,all,na,nb⟩ := length_eleven_left_block_of_small_path_d2 hc hp.1 ah bh len xo h1 small
  have rm {k : ℕ} (ak : G.Adj a (p.getVert k)) : k∉RightMarks p := by
    intro kr
    have ab : a≠b := fun e => by
      have ee := hp.1.1.getVert_injOn (show 0≤p.length by omega) (show p.length≤p.length from le_rfl)
        (p.getVert_zero.trans (e.trans p.getVert_length.symm))
      omega
    exact nb (mem_distanceTwo.mpr (dist_two hc ab na ak ((mem_filter.mp kr).2).symm))
  have rmPred {k : ℕ} (kr : k<p.length) (ak : G.Adj a (p.getVert (k+1))) : k∉RightMarks p := by
    intro bk
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support 1) px1 kr ak (mem_filter.mp bk).2
  let S : Finset ℕ := {6,7,8,9,10}
  have Sc : S.card=5 := by decide
  have sub : RightMarks p ⊆ S := by
    intro k km
    have kr := mem_range.mp (mem_filter.mp km).1
    have beg : 6≤k := by
      by_contra! no
      have c : k=0 ∨ k=1 ∨ k=2 ∨ (3≤k ∧ k≤5) := by omega
      rcases c with rfl|rfl|rfl|c
      · exact rmPred (by omega) first km
      · exact rm first km
      · exact rmPred (by omega) (back 3 (by omega) (by omega)) km
      · exact rm (back k c.1 (c.2.trans tge)) km
    have kk : k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 := by omega
    simpa [S] using kk
  have ne : 9∉RightMarks p := fun h =>
    end_not_adj_pin_predecessor hp.1 xo hj ((mem_filter.mp h).2)
  have csub : RightMarks p ⊆ (S.erase 9) := fun k km =>
    mem_erase.mpr ⟨fun e => ne (e ▸ km),sub km⟩
  have eqR := eq_of_subset_of_card_le csub (by
    have n : (S.erase 9).card=4 := by decide
    rw [n,card_rightMarks hp.1]
    exact bh)
  have r7 : 7∈RightMarks p := by rw [eqR]; decide
  have r8 : 8∈RightMarks p := by rw [eqR]; decide
  exact ⟨(mem_filter.mp r7).2,(mem_filter.mp r8).2⟩
#print axioms length_eleven_boundary_left_chord_16

private theorem length_eleven_four_off_two_boundary_pins_span
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (_conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (xo : x∉p.support) (h1 : 1∈Pins p x) (h10 : 10∈Pins p x)
    (ports : ∀ z∉p.support,Pins p z⊆({1,10}:Finset ℕ))
    (clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  let A := O.filter (fun z => 1∈Pins p z)
  let B := O.filter (fun z => 10∈Pins p z)
  have ao (z : V) (zA : z∈A) : z∉p.support := out.mp (mem_filter.mp zA).1
  have bo (z : V) (zB : z∈B) : z∉p.support := out.mp (mem_filter.mp zB).1
  have apos := left_boundary_porters_at_most_two hc even hp.1 ah bh (by omega) xo h1 A ao
    (fun _ h => (mem_filter.mp h).2)
  have bpos := right_boundary_porters_at_most_two hc even hp.1 ah bh (by omega) xo h10 (by omega)
    B bo (fun _ h => (mem_filter.mp h).2)
  have asub : A∪B⊆O := union_subset (filter_subset _ _) (filter_subset _ _)
  have rr : (O\(A∪B)).card≤1 := by
    by_contra no
    obtain ⟨u,uo,v,vo,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge no)
    have low {z : V} (zz : z∈O\(A∪B)) : ¬4≤G.degree z := by
      obtain ⟨zO,zn⟩ := mem_sdiff.mp zz
      have zo := out.mp zO
      intro zh
      have d := degree_off_bound hp.1 zo
      rw [off] at d
      obtain ⟨k,hk⟩ := card_pos.mp (show 0<(Pins p z).card by omega)
      have ch : k=1 ∨ k=10 := by simpa using ports z zo hk
      rcases ch with rfl|rfl
      · exact zn (mem_union.mpr (.inl (mem_filter.mpr ⟨zO,hk⟩)))
      · exact zn (mem_union.mpr (.inr (mem_filter.mpr ⟨zO,hk⟩)))
    exact (degree u v ne).elim (low uo) (low vo)
  have ins := card_sdiff_add_card_eq_card asub
  have total : (A∪B).card+(A∩B).card=A.card+B.card := card_union_add_card_inter _ _
  have mid : 0<(A∩B).card := card_pos.mpr ⟨x,mem_inter.mpr
    ⟨mem_filter.mpr ⟨out.mpr xo,h1⟩,mem_filter.mpr ⟨out.mpr xo,h10⟩⟩⟩
  have o4 : O.card=4 := off
  have xA : x∈A := mem_filter.mpr ⟨out.mpr xo,h1⟩
  have nA : 0<(A.erase x).card := by rw [card_erase_of_mem xA]; omega
  obtain ⟨v,hv⟩ := card_pos.mp nA
  obtain ⟨vx,vA⟩ := mem_erase.mp hv
  obtain ⟨b7,b8⟩ := length_eleven_boundary_left_chord_16 hc even hp ah bh len
    xo (ao v vA) vx.symm h1 (mem_filter.mp vA).2 h10
  obtain ⟨φ,inj,onto,φ12,value,outP⟩ := order_sixteen_four_off_labeling hp.1 len off xo
  have endV : p.getVert 11=b := by simpa only [len] using p.getVert_length
  let path : List (Fin 16) := [0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15]
  letI : Nonempty V := ⟨a⟩
  apply hamilton_of_labeled_chain φ inj onto path (by decide) (by intro i; fin_cases i <;> decide)
  simp only [path,List.chain'_cons,List.chain'_singleton]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [value 0 (by decide),value 1 (by decide)]
    exact p.adj_getVert_succ (i:=0) (by omega)
  · rw [value 1 (by decide),value 2 (by decide)]
    exact p.adj_getVert_succ (i:=1) (by omega)
  · rw [value 2 (by decide),value 3 (by decide)]
    exact p.adj_getVert_succ (i:=2) (by omega)
  · rw [value 3 (by decide),value 4 (by decide)]
    exact p.adj_getVert_succ (i:=3) (by omega)
  · rw [value 4 (by decide),value 5 (by decide)]
    exact p.adj_getVert_succ (i:=4) (by omega)
  · rw [value 5 (by decide),value 6 (by decide)]
    exact p.adj_getVert_succ (i:=5) (by omega)
  · rw [value 6 (by decide),value 7 (by decide)]
    exact p.adj_getVert_succ (i:=6) (by omega)
  · rw [value 7 (by decide),value 11 (by decide)]
    change G.Adj (p.getVert 7) (p.getVert 11)
    rw [endV]
    exact b7.symm
  · rw [value 11 (by decide),value 8 (by decide)]
    change G.Adj (p.getVert 11) (p.getVert 8)
    rw [endV]
    exact b8
  · rw [value 8 (by decide),value 9 (by decide)]
    exact p.adj_getVert_succ (i:=8) (by omega)
  · rw [value 9 (by decide),value 10 (by decide)]
    exact p.adj_getVert_succ (i:=9) (by omega)
  · rw [value 10 (by decide),φ12]
    exact (pin_data h10).2.symm
  · exact clique _ (outP 12 (by decide)) _ (outP 13 (by decide))
      (fun e => (by decide : (12:Fin 16)≠13) (inj e))
  · exact clique _ (outP 13 (by decide)) _ (outP 14 (by decide))
      (fun e => (by decide : (13:Fin 16)≠14) (inj e))
  · exact ⟨clique _ (outP 14 (by decide)) _ (outP 15 (by decide))
      (fun e => (by decide : (14:Fin 16)≠15) (inj e)),trivial⟩

#print axioms length_eleven_four_off_two_boundary_pins_span

end Graffiti189LongestPath.TwoCut.SmallOrderFour
