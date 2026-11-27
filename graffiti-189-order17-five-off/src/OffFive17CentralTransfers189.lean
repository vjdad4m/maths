import OffFive17CentralStructure189
import OrderSixteenFoundation189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin reverse_long dist_two mem_distanceTwo from SmallOrderFour189
open private omitted_degree_component_bound two_pin_flanks_path_only pins_gap_at_four from FourOffGraphSupport189
open private two_pins_choose_ordered omittedDegree_eq omittedNeighbors from FourOffGraphCore189
open private omitted_neighbors_eq_component_neighbors from OffSix17CoreLift189
open private min_two_from_cut from OrderSixteenFoundation189

abbrev CoreTotalDegree17 {W : Type*} [Fintype W] (D : SimpleGraph W) [DecidableRel D.Adj]
    (m : W→Fin 3) (x : W) : ℕ :=
  D.degree x + if m x=0 then 0 else 1

/-- The isolated-vertex branch reduces to a singleton with two boundary
portals and a disjoint five-off component's two central carrier vertices. -/
theorem length_eleven_five_off_four_component_singleton
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (h4 : H.vertices.card=4)
    {y z : V} (yh : y∈H.vertices) (zh : z∈H.vertices)
    (y4 : 4∈Pins p y) (z7 : 7∈Pins p z) :
    ∃ x∉p.support, x∉H.vertices ∧ (∀ w∉p.support,¬G.Adj x w) ∧
      ∃ i j : ℕ, i∈Pins p x ∧ j∈Pins p x ∧ i+3 ≤ j ∧ (i=1 ∨ j=10) ∧
        i≠4 ∧ i≠7 ∧ j≠4 ∧ j≠7 := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  let R := O\H.vertices
  have out {x : V} : x∈O ↔ x∉p.support := by simp [O]
  have inc : H.vertices⊆O := fun x h=>out.mpr (H.off _ h)
  have r := card_sdiff_add_card_eq_card inc
  have rone : R.card=1 := by
    change R.card+H.vertices.card=O.card at r
    have off : O.card=5 := off
    omega
  obtain ⟨x,rx⟩ := card_eq_one.mp rone
  have xm : x∈R := by rw [rx]; simp
  have xo := out.mp (mem_sdiff.mp xm).1
  have xH := (mem_sdiff.mp xm).2
  have isol (w : V) (wo : w∉p.support) : ¬G.Adj x w := by
    intro adj
    by_cases wh : w∈H.vertices
    · exact xo (H.closed w wh x xH adj.symm)
    · have hm : w∈R := mem_sdiff.mpr ⟨out.mpr wo,wh⟩
      rw [rx] at hm
      exact adj.ne (mem_singleton.mp hm).symm
  have n0 : omittedNeighbors p x=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w wm
    have e := mem_filter.mp wm
    exact (isol _ e.2) ((mem_neighborFinset G _ _).mp e.1)
  have xd := omittedDegree_eq hp.1 xo
  rw [n0,card_empty,Nat.add_zero] at xd
  have n : 3 ≤ Fintype.card V := by
    have e := card_le_card (subset_univ p.support.toFinset)
    rw [List.toFinset_card_of_nodup hp.1.1.support_nodup,length_support,card_univ] at e
    omega
  have d2 := min_two_from_cut conn n x
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered (show 2 ≤ (Pins p x).card by omega)
  have hgap : i+3 ≤ j := by
    exact pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  have border := double_pins_hit_boundary_at_eleven hc even conn degree hp ah bh len xo xi xj ij
  have pathOnly := (two_pin_flanks_path_only hc even conn degree hp ah bh xo xi xj ij).1
  have exclus {w : V} (wh : w∈H.vertices) {k : ℕ} (wk : k∈Pins p w) (xk : k∈Pins p x) : False := by
    have wo := H.off _ wh
    have xw : x≠w := fun e=>xH (e ▸ wh)
    have wd : w∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc xw (isol w wo) (pin_data xk).2 (pin_data wk).2.symm)
    exact wo (pathOnly _ wd)
  exact ⟨x,xo,xH,isol,i,j,xi,xj,hgap,border,
    fun h=>exclus yh y4 (h ▸ xi),fun h=>exclus zh z7 (h ▸ xi),
    fun h=>exclus yh y4 (h ▸ xj),fun h=>exclus zh z7 (h ▸ xj)⟩

#print axioms length_eleven_five_off_four_component_singleton

/-- The connected five-vertex branch is a marked spanning-path problem
on the omitted component, with no endpoint marks in the finite model. -/
theorem no_length_eleven_with_central_five_component_of_marked_core
    (core : ∀ {W : Type u} (D : SimpleGraph W) [Fintype W] [DecidableEq W]
       [DecidableRel D.Adj] (m : W→Fin 3), Fintype.card W=5 →
       (∃ x,m x=1) → (∃ x,m x=2) →
       (∀ x,2 ≤ CoreTotalDegree17 D m x) →
       (∀ x y,x≠y → 4 ≤ CoreTotalDegree17 D m x ∨ 4 ≤ CoreTotalDegree17 D m y) →
       (∀ x y,m x≠0 → m y≠0 → m x≠m y → D.neighborFinset x≠{y}) →
       ∃ s t,∃ q : D.Walk s t, m s=1 ∧ m t=2 ∧ q.IsPath ∧ 4 ≤ q.length)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=11) (H : OmittedComponent p) (h5 : H.vertices.card=5)
    (one : ∀ z∈H.vertices,(Pins p z).card ≤ 1)
    (all : ∀ z∈H.vertices,Pins p z⊆({4,7}:Finset ℕ))
    (left : ∃ x∈H.vertices,4∈Pins p x) (right : ∃ x∈H.vertices,7∈Pins p x) : False := by
  classical
  let W : Set V := H.vertices
  let D := G.induce W
  let f : D →g G := ⟨Subtype.val, fun e=>e⟩
  let m (x : W) : Fin 3 := if 4∈Pins p x.val then 1 else if 7∈Pins p x.val then 2 else 0
  have disj (x : W) (a : 4∈Pins p x.val) (b : 7∈Pins p x.val) : False :=
    (Nat.not_lt_of_ge (one _ x.property)) (one_lt_card.mpr ⟨4,a,7,b,by decide⟩)
  have L (x : W) : m x=1 ↔ 4∈Pins p x.val := by
    by_cases a : 4∈Pins p x.val
    · simp [m,a]
    · by_cases b : 7∈Pins p x.val <;> simp [m,a,b]
  have R (x : W) : m x=2 ↔ 7∈Pins p x.val := by
    by_cases b : 7∈Pins p x.val
    · have a : 4∉Pins p x.val := fun a=>disj x a b
      simp [m,a,b]
    · by_cases a : 4∈Pins p x.val <;> simp [m,a,b]
  have count (x : W) : (Pins p x.val).card=(if m x=0 then 0 else 1) := by
    by_cases m0 : m x=0
    · have o : Pins p x.val=∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro k km
        have e : k=4 ∨ k=7 := by simpa using all _ x.property km
        rcases e with rfl|rfl
        · have a := (L x).mpr km
          rw [m0] at a
          contradiction
        · have b := (R x).mpr km
          rw [m0] at b
          contradiction
      simp [m0,o]
    · have n : (Pins p x.val).Nonempty := by
        by_cases a : 4∈Pins p x.val
        · exact ⟨4,a⟩
        by_cases b : 7∈Pins p x.val
        · exact ⟨7,b⟩
        exact (m0 (by simp [m,a,b])).elim
      simp only [if_neg m0]
      have k := card_pos.mpr n
      exact Nat.le_antisymm (one _ x.property) k
  have ed (z : W) : (D.neighborFinset z).image Subtype.val=G.neighborFinset z.val∩H.vertices := by
    ext w
    simp only [mem_image,mem_neighborFinset,mem_inter]
    constructor
    · rintro ⟨r,e,rfl⟩
      exact ⟨show G.Adj z.val r.val from e,r.property⟩
    · rintro ⟨adj,hm⟩
      exact ⟨⟨w,hm⟩,adj,rfl⟩
  have deg (x : W) : CoreTotalDegree17 D m x=G.degree x.val := by
    have e := congrArg Finset.card (ed x)
    rw [card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at e
    have b := omittedDegree_eq hp.1 (H.off _ x.property)
    rw [omitted_neighbors_eq_component_neighbors H x.property,←e,count x] at b
    unfold CoreTotalDegree17
    omega
  have mins (x : W) : 2 ≤ CoreTotalDegree17 D m x := by
    rw [deg x]
    apply min_two_from_cut conn
    have q := card_le_card (subset_univ p.support.toFinset)
    rw [card_univ,List.toFinset_card_of_nodup hp.1.1.support_nodup,length_support] at q
    omega
  have wide (x y : W) (xy : x≠y) : 4 ≤ CoreTotalDegree17 D m x ∨ 4 ≤ CoreTotalDegree17 D m y := by
    rw [deg x,deg y]
    exact degree _ _ (fun e=>xy (Subtype.ext e))
  have noleaf (x y : W) (x0 : m x≠0) (y0 : m y≠0) (xy : m x≠m y) :
      D.neighborFinset x≠{y} := by
    intro e
    have e' := ed x
    rw [e,Finset.image_singleton] at e'
    have colors (x : W) (h : m x≠0) : m x=1 ∨ m x=2 := by
      have k := (m x).isLt
      have n : (m x).val≠0 := fun e=>h (Fin.ext e)
      have a : (m x).val=1 ∨ (m x).val=2 := by omega
      exact a.imp (fun b=>Fin.ext b) (fun b=>Fin.ext b)
    rcases colors x x0 with x1|x2 <;> rcases colors y y0 with y1|y2
    · exact xy (x1.trans y1.symm)
    · exact no_foreign_pin_at_omitted_leaf_neighbor_length_eleven hc even conn degree hp ah bh len H
        x.property y.property ((L x).mp x1) ((R y).mp y2) (by decide) e'.symm
    · exact no_foreign_pin_at_omitted_leaf_neighbor_length_eleven hc even conn degree hp ah bh len H
        x.property y.property ((R x).mp x2) ((L y).mp y1) (by decide) e'.symm
    · exact xy (x2.trans y2.symm)
  obtain ⟨s,sh,s4⟩ := left
  obtain ⟨t,th,t7⟩ := right
  have cardW : Fintype.card W=5 := (Fintype.card_coe H.vertices).trans h5
  obtain ⟨x,y,q,x1,y2,qp,ln⟩ := core D m cardW ⟨⟨s,sh⟩,(L _).mpr s4⟩
    ⟨⟨t,th⟩,(R _).mpr t7⟩ mins wide noleaf
  let Q : G.Walk x.val y.val := q.map f
  have Qp : Q.IsPath := (q.map_isPath_iff_of_injective Subtype.val_injective).mpr qp
  have long : 4 ≤ Q.length := by simpa [Q] using ln
  have safe (z : V) (hz : z∈Q.support) : z∉p.support := by
    rw [show Q=q.map f from rfl,support_map] at hz
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
    exact H.off _ w.property
  exact no_longest_with_long_omitted_path_between_sites hp.1 Q Qp safe
    (i:=4) (j:=7) (by decide) (by omega) long
    (pin_data ((L _).mp x1)).2 (pin_data ((R _).mp y2)).2

#print axioms no_length_eleven_with_central_five_component_of_marked_core
end Graffiti189LongestPath.TwoCut
