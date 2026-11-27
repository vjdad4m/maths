import FourSideOrder189
namespace Graffiti189LongestPath.TwoCut.FourSideCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
set_option maxHeartbeats 2100000
set_option linter.unusedSectionVars false
noncomputable section
include C

theorem A_sub_H : C.A⊆C.H := fun _ h => (C.memA.mp h).1
theorem B_sub_H : C.B⊆C.H := fun _ h => (C.memB.mp h).1
theorem I_sub_H : C.I⊆C.H := fun _ h => (C.memI.mp h).1
theorem E_sub_H : C.E⊆C.H := fun _ h => (C.memE.mp h).1

theorem classifyH {x : V} (xh : x∈C.H) : x∈C.A ∨ x∈C.B ∨ x∈C.I := by
  by_cases ax : G.Adj a x
  · exact Or.inl (C.memA.mpr ⟨xh,ax⟩)
  by_cases bx : G.Adj b x
  · exact Or.inr (Or.inl (C.memB.mpr ⟨xh,bx⟩))
  · exact Or.inr (Or.inr (C.memI.mpr ⟨xh,ax,bx⟩))

theorem I_not_A {x : V} (xi : x∈C.I) : x∉C.A := fun h =>
  (C.memI.mp xi).2.1 (C.memA.mp h).2
theorem I_not_B {x : V} (xi : x∈C.I) : x∉C.B := fun h =>
  (C.memI.mp xi).2.2 (C.memB.mp h).2

theorem I_neighbors_H {x y : V} (xi : x∈C.I) (xy : G.Adj x y) : y∈C.H := by
  obtain ⟨xh,noa,nob⟩ := C.memI.mp xi
  rcases S.closed (!C.i) x xh y xy with rfl|rfl|yh
  · exact (noa xy.symm).elim
  · exact (nob xy.symm).elim
  · exact yh

theorem no_cross_of_E_sub_I (sub : C.E⊆C.I) {x y : V} (xa : x∈C.A) (yb : y∈C.B) :
    ¬G.Adj x y := fun xy =>
  C.I_not_B (sub (C.local_a_d2 xa (C.B_sub_H yb)
    (fun h => disjoint_left.mp C.dis_AB h yb) xy)) yb

theorem I_count_off_E (count : C.I.card=3) (cap : C.E.card≤2)
    (away : (C.I\C.E).card≤1) : C.E.card=2 ∧ C.E⊆C.I := by
  have e := card_sdiff_add_card_eq_card (inter_subset_left : C.I∩C.E⊆C.I)
  have c := card_le_card (inter_subset_right : C.I∩C.E⊆C.E)
  have eq : C.I \ (C.I∩C.E)=C.I\C.E := by ext x; simp
  rw [eq] at e
  have eq' : C.I∩C.E=C.E := eq_of_subset_of_card_le inter_subset_right (by omega)
  refine ⟨by omega,?_⟩
  rw [←eq']
  exact inter_subset_left

theorem I_in_E_of_three (three : C.A.card=3) : C.I⊆C.E := by
  have h := C.inner_away_cap (show 2≤C.A.card by omega)
  rw [three,Nat.sub_self,Nat.le_zero] at h
  have eq := card_eq_zero.mp h
  exact sdiff_eq_empty_iff_subset.mp eq

theorem high_port_has_E {x : V} (xa : x∈C.A) (high : 4≤G.degree x) :
    ∃ y∈C.E, G.Adj x y := by
  by_cases ex : ∃ y∈C.E,G.Adj x y
  · exact ex
  exfalso
  have sub : G.neighborFinset x⊆insert a (C.A.erase x) := by
    intro z hz
    have e := C.local_A_neighbor_sub xa hz
    rcases mem_insert.mp e with rfl|e
    · exact mem_insert_self _ _
    rcases mem_union.mp e with za|ze
    · exact mem_insert_of_mem za
    exact (ex ⟨z,ze,(mem_neighborFinset G x z).mp hz⟩).elim
  have deg := card_le_card sub
  rw [card_neighborFinset_eq_degree] at deg
  have c := card_insert_le a (C.A.erase x)
  rw [card_erase_of_mem xa] at c
  have cap := C.Acap
  have pos := C.Apos
  omega

theorem all_high_group :
    (∀ x∈C.A,4≤G.degree x) ∨ (∀ x∈C.B,4≤G.degree x) := by
  by_cases h : ∀ x∈C.A,4≤G.degree x
  · exact Or.inl h
  obtain ⟨x,hx⟩ := not_forall.mp h
  have xa : x∈C.A := Classical.byContradiction (fun na => hx (fun e => (na e).elim))
  have xlow : ¬4≤G.degree x := fun hi => hx (fun _ => hi)
  right
  intro y yb
  have ne : x≠y := fun e => disjoint_left.mp C.dis_AB xa (e.symm ▸ yb)
  exact (S.degree x y ne).resolve_left xlow

theorem inner_degree_bound_of_nonnear {x : V} (xi : x∈C.I)
    (xe : x∉C.E) (xf : x∉C.F) : G.degree x≤C.I.card-1 := by
  have sub : G.neighborFinset x⊆C.I.erase x := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    have yh := C.I_neighbors_H xi xy
    rcases C.classifyH yh with ya|yb|yi
    · exact (xe (C.local_a_d2 ya (C.I_sub_H xi) (C.I_not_A xi) xy.symm)).elim
    · exact (xf (C.swap.local_a_d2 yb (C.I_sub_H xi) (C.I_not_B xi) xy.symm)).elim
    · exact mem_erase.mpr ⟨xy.ne.symm,yi⟩
  have c := card_le_card sub
  rwa [card_neighborFinset_eq_degree,card_erase_of_mem xi] at c

theorem inner_low_of_no_B_no_inner {x : V} (xi : x∈C.I)
    (xf : x∉C.F) (not_inner : ∀ y∈C.I, ¬G.Adj x y) (a2 : C.A.card=2) : ¬4≤G.degree x := by
  intro high
  have sub : G.neighborFinset x⊆C.A := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases C.classifyH (C.I_neighbors_H xi xy) with ya|yb|yi
    · exact ya
    · exact (xf (C.swap.local_a_d2 yb (C.I_sub_H xi) (C.I_not_B xi) xy.symm)).elim
    · exact (not_inner y yi xy).elim
  have le := card_le_card sub
  rw [card_neighborFinset_eq_degree,a2] at le
  omega

theorem d2_of_local_nonedge {x y z : V} (xy : x≠y) (no : ¬G.Adj x y)
    (xz : G.Adj x z) (zy : G.Adj z y) : y∈DistanceTwo G x :=
  Sides.mem_d2.mpr (Sides.dist_two S.con xy no xz zy)

theorem d2_cross_group {x y z : V} (xa : x∈C.A) (yb : y∈C.B)
    (no : ¬G.Adj x y) (xz : G.Adj x z) (zy : G.Adj z y) :
    y∈DistanceTwo G x :=
  C.d2_of_local_nonedge (fun eq => disjoint_left.mp C.dis_AB xa (eq.symm ▸ yb)) no xz zy

theorem no_extra_local {x : V} (xa : x∈C.A) (u2 : C.U.card=2) {Q : Finset V}
    (q2 : Q.card=2) (qh : Q⊆C.H) (qd : Q⊆DistanceTwo G x) {y : V}
    (yh : y∈C.H) (yq : y∉Q) : y∉DistanceTwo G x := by
  intro yd
  have cap := C.local_d2_cap xa
    (show insert y Q⊆C.H from fun z hz => (mem_insert.mp hz).elim (fun e => e.symm ▸ yh) (fun q => qh q))
    (show insert y Q⊆DistanceTwo G x from fun z hz => (mem_insert.mp hz).elim (fun e => e.symm ▸ yd) (fun q => qd q))
  rw [card_insert_of_not_mem yq,q2,u2] at cap
  omega

end
end Graffiti189LongestPath.TwoCut.FourSideCtx
