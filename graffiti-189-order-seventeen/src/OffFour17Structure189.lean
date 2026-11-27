import OffSix17CoreLift189
import OrderSixteenFoundation189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin reverse_long same_support_optimal mark_length
  LeftMarks RightMarks dist_two mem_distanceTwo from SmallOrderFour189
open private pin_two_contacts_end mark_holes_of_pin_and_missing_endpoint omitted_degree_component_bound
  two_pin_flanks_path_only two_pin_universal_in_omitted_component pins_gap_at_four
  off_four_component_carries_all_high from FourOffGraphSupport189
open private two_pins_choose_ordered omittedDegree_eq omittedNeighbors from FourOffGraphCore189
open private omitted_neighbors_eq_component_neighbors from OffSix17CoreLift189
open private min_two_from_cut from OrderSixteenFoundation189

/-- A nontrivial omitted component always has a path carrier different from
any prescribed member; otherwise that member disconnects the component. -/
theorem another_carrier_of_nontrivial_omitted_component
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (large : 2  ≤  H.vertices.card)
    {x : V} (xh : x∈H.vertices) : ∃ y∈H.vertices,y≠x ∧ (Pins p y).Nonempty := by
  classical
  apply Classical.byContradiction
  intro no
  have xo := H.off _ xh
  have share {y : V} (yh : y∈H.vertices) (yx : y≠x) {k : ℕ} (yk : k∈Pins p y) : False :=
    no ⟨y,yh,yx,⟨k,yk⟩⟩
  let S : Finset V := {x}
  let U := ((↑S : Set V)ᶜ)
  have cut := conn S (by simp [S])
  have ec := card_erase_of_mem xh
  obtain ⟨y,yr⟩ := card_pos.mp (show 0<(H.vertices.erase x).card by omega)
  obtain ⟨yx,yh⟩ := mem_erase.mp yr
  have ax : a≠x := fun e=>xo (e ▸ p.start_mem_support)
  let ys : U := ⟨y,by simp [U,S,yx]⟩
  let as : U := ⟨a,by simp [U,S,ax]⟩
  obtain ⟨q⟩ := cut.preconnected ys as
  have localStep {u v : U} (hu : u.val∈H.vertices) (e : (G.induce U).Adj u v) :
      v.val∈H.vertices := by
    by_cases vy : v.val∈H.vertices
    · exact vy
    exfalso
    have vs := H.closed _ hu _ vy (show G.Adj u.val v.val from e)
    obtain ⟨k,kp,_⟩ := pin_of_neighbor_mem hp (H.off _ hu) vs e
    exact share hu (by simpa [U,S] using u.property) kp
  have prop {u v : U} (q : (G.induce U).Walk u v) : u.val∈H.vertices → v.val∈H.vertices := by
    induction q with
    | nil => exact id
    | cons e q ih => exact fun h=>ih (localStep h e)
  exact H.off _ (prop q yh) p.start_mem_support



/-- A boundary member of a double-pin pair forces the carrier's omitted
component to be a singleton. -/
theorem nontrivial_dual_carrier_has_interior_pair
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (H : OmittedComponent p) (large : 2  ≤  H.vertices.card)
    {x : V} (xh : x∈H.vertices) {i j : ℕ} (xi : i∈Pins p x) (xj : j∈Pins p x) (ij : i<j) :
    2  ≤  i ∧ j+1<p.length := by
  classical
  have xo := H.off _ xh
  have ir := pin_pos hp.1 xo xi
  have jr := (pin_data xj).1
  have fail (border : i=1 ∨ j+1=p.length) : False := by
    obtain ⟨path_only,sub⟩ := two_pin_flanks_path_only hc even conn degree hp ah bh xo xi xj ij
    have share {y : V} (yh : y∈H.vertices) (yx : y≠x) {k : ℕ} (yk : k∈Pins p y) : False := by
      have yo := H.off _ yh
      have adj := two_pin_universal_in_omitted_component hc H xh path_only y yh yx
      have kp := sub y yo adj yk
      have eq : k=i ∨ k=j := by simpa using kp
      have jlen := (pin_data xj).1
      rcases border with rfl|hj
      · rcases eq with rfl|rfl
        · exact no_longest_with_shared_left_boundary_pair hp.1 yo xo adj.symm (by omega) jlen.le
            (pin_data yk).2 (pin_data xj).2
        · exact no_longest_with_shared_left_boundary_pair hp.1 xo yo adj (by omega) jlen.le
            (pin_data xi).2 (pin_data yk).2
      · have i1 := pin_pos hp.1 xo xi
        have xr : 1∈Pins p.reverse x := by
          simpa only [show p.length-j=1 by omega] using reverse_pin hp.1 xo xj
        have xf : p.length-i∈Pins p.reverse x := reverse_pin hp.1 xo xi
        have hl := (pin_data xf).1
        rw [length_reverse] at hl
        rcases eq with ki|kj
        · subst k
          have yf : p.length-i∈Pins p.reverse y := reverse_pin hp.1 yo yk
          exact no_longest_with_shared_left_boundary_pair (reverse_long hp.1)
            (by simpa using xo) (by simpa using yo) adj (by omega) (by rw [length_reverse]; exact hl.le)
            (pin_data xr).2 (pin_data yf).2
        · subst k
          have yr : 1∈Pins p.reverse y := by
            simpa only [show p.length-j=1 by omega] using reverse_pin hp.1 yo yk
          exact no_longest_with_shared_left_boundary_pair (reverse_long hp.1)
            (by simpa using yo) (by simpa using xo) adj.symm (by omega) (by rw [length_reverse]; exact hl.le)
            (pin_data yr).2 (pin_data xf).2
    obtain ⟨y,yh,yx,k,km⟩ := another_carrier_of_nontrivial_omitted_component conn hp.1 H large xh
    exact share yh yx km
  exact ⟨by by_contra n; exact fail (.inl (by omega)), by by_contra n; exact fail (.inr (by omega))⟩

/-- Four forced mark holes follow from a double-pin pair when neither site
is next to a spine endpoint. -/
theorem four_holes_of_interior_dual_pair
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (xo : x∉p.support) {i j : ℕ} (xi : i∈Pins p x) (xj : j∈Pins p x)
    (ij : i<j) (lo : 2  ≤  i) (hi : j+1<p.length) :
    (∀ k, k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j → k∉LeftMarks p∪RightMarks p) := by
  have cap := fun v=>distanceTwo_le_of_even 4 v (even v)
  have few := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp xo).1
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  obtain ⟨ll,rr⟩ := pin_two_contacts_end hp.1 hc xo few (cap x) xi xj gap
  intro k kk
  rcases kk with e|e|e|e
  · rw [e]
    exact (mark_holes_of_pin_and_missing_endpoint hp.1 xo xi).1 (fun e=>by have h:=ll i xi e; omega) 
  · rw [e]
    exact (mark_holes_of_pin_and_missing_endpoint hp.1 xo xi).2 (fun e=>by have h:=rr i xi e; omega) 
  · rw [e]
    exact (mark_holes_of_pin_and_missing_endpoint hp.1 xo xj).1 (fun e=>by have h:=ll j xj e; omega) 
  · rw [e]
    exact (mark_holes_of_pin_and_missing_endpoint hp.1 xo xj).2 (fun e=>by have h:=rr j xj e; omega)

#print axioms another_carrier_of_nontrivial_omitted_component
#print axioms nontrivial_dual_carrier_has_interior_pair
#print axioms four_holes_of_interior_dual_pair

end Graffiti189LongestPath.TwoCut
