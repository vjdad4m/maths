import FourOffTwinMixed189
import FourOffTwinBoundary189
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
theorem traceable_if_four_off_order_sixteen_some_two_pin_with_table
    {row : ℕ → Bool}
    (table : ∀ j : ℕ,4≤j → j≤9 → row j=true)
    (mixed : ∀ (_table : ∀ j : ℕ,4≤j → j≤9 → row j=true)
    (_hc : G.Connected) (_even : ∀ v,(EvenFrom G v).card≤5)
    (_degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (_hp : IsLongest p)
    (_ah : 4≤G.degree a) (_bh : 4≤G.degree b) (_len : p.length=11)
    (_off : ((univ : Finset V)\p.support.toFinset).card=4)
    (_xo : x∉p.support) {j : ℕ} (_h1 : 1∈Pins p x) (_hj : j∈Pins p x) (_jlo : 4≤j) (_jhi : j≤9)
    (_ports : ∀ z∉p.support,Pins p z⊆({1,j}:Finset ℕ))
    (_clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w)
    (_hole1 : 1∉LeftMarks p∪RightMarks p) (_holep : j-1∉LeftMarks p∪RightMarks p)
    (_holej : j∉LeftMarks p∪RightMarks p) ,
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ v,v∈p.support)
    (bothBoundary : ∀ (_hc : G.Connected) (_even : ∀ v,(EvenFrom G v).card≤5)
    (_conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (_degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (_hp : EdgeOptimal p) (_ah : 4≤G.degree a) (_bh : 4≤G.degree b)
    (_len : p.length=11) (_off : ((univ : Finset V)\p.support.toFinset).card=4)
    (_xo : x∉p.support) (_h1 : 1∈Pins p x) (_h10 : 10∈Pins p x)
    (_ports : ∀ z∉p.support,Pins p z⊆({1,10}:Finset ℕ))
    (_clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ,
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ v,v∈p.support)
    (shape : ∀ (_hc : G.Connected) (_even : ∀ v,(EvenFrom G v).card≤5)
    (_conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (_degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (_hp : EdgeOptimal p)
    (_ah : 4≤G.degree a) (_bh : 4≤G.degree b) (_len : p.length=11)
    (_off : ((univ : Finset V)\p.support.toFinset).card=4)
    (_xo : x∉p.support) (_x2 : 2≤(Pins p x).card) ,
    ∃ (y : V) (i j : ℕ), y∉p.support ∧ i∈Pins p y ∧ j∈Pins p y ∧ i+3≤j ∧
      (i=1 ∨ j=10) ∧ (∀ z∉p.support,Pins p z⊆({i,j}:Finset ℕ)) ∧
      (∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ∧
      i∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p ∧
      (i≠1 → i-1∉LeftMarks p∪RightMarks p) ∧ (j≠10 → j∉LeftMarks p∪RightMarks p))
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b z : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (zo : z∉p.support) (two : 2≤(Pins p z).card) :
    ∃ a b : V, ∃ q : G.Walk a b,q.IsPath ∧ ∀ v,v∈q.support := by
  obtain ⟨x,i,j,xo,hi,hj,gap,boundary,P,C,hi0,hj0,hiL,hjR⟩ :=
    shape hc even conn degree hp ah bh len off zo two
  have ip := pin_pos hp.1 xo hi
  have jp := (pin_data hj).1
  by_cases i1 : i=1
  · subst i
    by_cases j10 : j=10
    · subst j
      exact bothBoundary hc even conn degree hp ah bh len off xo hi hj P C
    · exact mixed table hc even degree hp.1 ah bh len off xo
        hi hj (by omega) (by omega) P C hi0 hj0 (hjR j10)
  have J : j=10 := boundary.resolve_left i1
  subst j
  have rev : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro u; simp)
  have rl : p.reverse.length=11 := by simpa using len
  have rx : x∉p.reverse.support := by simpa using xo
  have ro : ((univ : Finset V)\p.reverse.support.toFinset).card=4 := by simpa [support_reverse] using off
  have r1 : 1∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo hj
  have rr : 11-i∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo hi
  have rC : ∀ z∉p.reverse.support,∀ w∉p.reverse.support,z≠w → G.Adj z w := by
    simpa only [support_reverse,List.mem_reverse] using C
  have rP (y : V) (yo : y∉p.reverse.support) : Pins p.reverse y⊆({1,11-i}:Finset ℕ) := by
    intro k km
    have yz : y∉p.support := by simpa using yo
    have vp : p.reverse.getVert k∈p.support := by simpa [support_reverse] using p.reverse.getVert_mem_support k
    obtain ⟨w,wm,eq⟩ := pin_of_neighbor_mem hp.1 yz vp (pin_data km).2
    rw [getVert_reverse] at eq
    have idx := hp.1.1.getVert_injOn (pin_data wm).1.le (Nat.sub_le _ _) eq
    have ll : w=i ∨ w=10 := by simpa using P y yz wm
    have kl := (pin_data km).1
    have r : k=1 ∨ k=11-i := by omega
    simpa using r
  have bv : ¬G.Adj b (p.getVert i) := by
    intro e
    exact hi0 (mem_union.mpr (.inr (mem_filter.mpr ⟨mem_range.mpr (pin_data hi).1,e⟩)))
  have av : ¬G.Adj a (p.getVert i) := by
    intro e
    exact hiL i1 (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_range.mpr (by omega),by
      rwa [show i-1+1=i by omega]⟩)))
  have av10 : ¬G.Adj a (p.getVert 10) := by
    intro e
    exact hj0 (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩)))
  have equ : p.reverse.getVert (11-i)=p.getVert i := by
    rw [getVert_reverse,show p.length-(11-i)=i by omega]
  have eq1 : p.reverse.getVert 1=p.getVert 10 := by
    rw [getVert_reverse,show p.length-1=10 by omega]
  have h1r := (mark_holes_of_pin_and_missing_endpoint rev.1 rx r1).2
    (fun e => av10 (eq1 ▸ e))
  have hpr := (mark_holes_of_pin_and_missing_endpoint rev.1 rx rr).1
    (fun e => bv (equ ▸ e))
  have hjr := (mark_holes_of_pin_and_missing_endpoint rev.1 rx rr).2
    (fun e => av (equ ▸ e))
  exact mixed table hc even degree rev.1 bh ah rl ro rx
    r1 rr (by omega) (by omega) rP rC h1r hpr hjr

#print axioms traceable_if_four_off_order_sixteen_some_two_pin_with_table
end Graffiti189LongestPath.TwoCut.SmallOrderFour
