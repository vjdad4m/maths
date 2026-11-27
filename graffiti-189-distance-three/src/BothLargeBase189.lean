import CrossMetric189
import DistThreeShape189
import Order189
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2700000
set_option linter.unusedSectionVars false

structure DistThreeCtx (S : CutPair G a b) where
  i : Bool
  j : Bool
  different : i≠j
  far : 3≤G.dist a b
  min2 : ∀ x, 2≤G.degree x

namespace DistThreeCtx
noncomputable section
variable {a b : V} {S : CutPair G a b} (C : DistThreeCtx S)
def K := S.H C.i
def H := S.H C.j
def U := S.A C.i
def W := S.flip.A C.i
def A := S.A C.j
def B := S.flip.A C.j
def E := S.D C.j
def F := S.flip.D C.j
def I := C.H \ (C.A ∪ C.B)
def swap : DistThreeCtx S.flip :=
  ⟨C.i,C.j,C.different,(by rw [dist_comm]; exact C.far),C.min2⟩
def other : DistThreeCtx S := ⟨C.j,C.i,C.different.symm,C.far,C.min2⟩

@[simp] theorem swap_I : C.swap.I=C.I := by
  change C.H \ (C.B∪C.A)=C.H \ (C.A∪C.B)
  rw [union_comm]

include C

theorem cut_dist : G.dist a b=3 := Nat.le_antisymm S.cut_distance C.far

theorem no_common {x : V} (ax : G.Adj a x) (bx : G.Adj b x) : False := by
  have d := G.dist_le (Walk.cons ax (Walk.cons bx.symm .nil))
  simp at d
  have h := C.far
  omega

theorem cut_not_adj : ¬ G.Adj a b := by
  intro e
  have d := dist_eq_one_iff_adj.mpr e
  have h := C.far
  omega

theorem memA {x : V} : x∈C.A ↔ x∈C.H ∧ G.Adj a x := mem_filter
theorem memB {x : V} : x∈C.B ↔ x∈C.H ∧ G.Adj b x := mem_filter
theorem memU {x : V} : x∈C.U ↔ x∈C.K ∧ G.Adj a x := mem_filter
theorem memW {x : V} : x∈C.W ↔ x∈C.K ∧ G.Adj b x := mem_filter
theorem memE {x : V} : x∈C.E ↔ x∈C.H ∧ G.dist a x=2 :=
  mem_filter.trans (and_congr_right' Sides.mem_d2)
theorem memF {x : V} : x∈C.F ↔ x∈C.H ∧ G.dist b x=2 :=
  mem_filter.trans (and_congr_right' Sides.mem_d2)
theorem memI {x : V} : x∈C.I ↔ x∈C.H ∧ ¬G.Adj a x ∧ ¬G.Adj b x := by
  by_cases h : x∈C.H <;> simp [I, C.memA,C.memB,h]

theorem dis_KH : Disjoint C.K C.H := S.disjoint_sides C.different
theorem dis_AB : Disjoint C.A C.B := disjoint_left.mpr
  (fun _ xa xb => C.no_common (C.memA.mp xa).2 (C.memB.mp xb).2)
theorem dis_UW : Disjoint C.U C.W := disjoint_left.mpr
  (fun _ xa xb => C.no_common (C.memU.mp xa).2 (C.memW.mp xb).2)

theorem count_H : C.A.card+C.B.card+C.I.card=C.H.card := by
  have su : C.A∪C.B⊆C.H := union_subset (fun _ h => (C.memA.mp h).1) (fun _ h => (C.memB.mp h).1)
  have e := card_sdiff_add_card_eq_card su
  rw [card_union_of_disjoint C.dis_AB] at e
  change C.I.card+(C.A.card+C.B.card)=C.H.card at e
  omega

theorem joined_H {x y : V} (xh : x∈C.H) (yh : y∈C.H) :
    ∃ w : G.Walk x y, ∀ z∈w.support,z∈C.H := S.joined _ _ xh _ yh

theorem no_other_edge {x y : V} (xh : x∈C.H) (yk : y∈C.K) : ¬G.Adj x y := by
  intro e
  rcases S.closed _ x xh y e with rfl|rfl|yh
  · exact (S.off C.i).1 yk
  · exact (S.off C.i).2 yk
  · exact disjoint_left.mp C.dis_KH yk yh

theorem d2_le (x : V) : (DistanceTwo G x).card≤4 := distanceTwo_le_of_even 4 x (S.even x)

theorem Upos : 1≤C.U.card := by
  obtain ⟨x,h,xadj⟩ := S.hita C.i
  exact card_pos.mpr ⟨x,C.memU.mpr ⟨h,xadj⟩⟩
theorem Apos : 1≤C.A.card := by
  obtain ⟨x,h,xadj⟩ := S.hita C.j
  exact card_pos.mpr ⟨x,C.memA.mpr ⟨h,xadj⟩⟩
theorem Ucap : C.U.card≤3 := S.at_most_three_a_ports C.far C.i
theorem Acap : C.A.card≤3 := S.at_most_three_a_ports C.far C.j

theorem cut_deg_a : G.degree a=C.U.card+C.A.card := by
  have eq : G.neighborFinset a=C.U∪C.A := by
    ext x
    constructor
    · intro xh
      have ax := (mem_neighborFinset G a x).mp xh
      rcases S.all x with rfl|rfl|⟨j,h⟩
      · exact (ax.ne rfl).elim
      · exact (C.cut_not_adj ax).elim
      by_cases eq : j=C.i
      · exact mem_union.mpr (Or.inl (C.memU.mpr ⟨show x∈S.H _ from eq ▸ h,ax⟩))
      have eq : j=C.j := by
        have ne := C.different
        cases j <;> cases hi : C.i <;> cases hj : C.j <;> simp_all
      exact mem_union.mpr (Or.inr (C.memA.mpr ⟨show x∈S.H _ from eq ▸ h,ax⟩))
    · intro e
      exact (mem_neighborFinset G a _).mpr ((mem_union.mp e).elim
        (fun h => (C.memU.mp h).2) (fun h => (C.memA.mp h).2))
  rw [←card_neighborFinset_eq_degree,eq,card_union_of_disjoint
    (C.dis_KH.mono (fun _ h => (C.memU.mp h).1) (fun _ h => (C.memA.mp h).1))]

theorem degree_A {x : V} (xa : x∈C.A) :
    G.degree x≤C.A.card+C.E.card := by
  obtain ⟨xh,ax⟩ := C.memA.mp xa
  have sub : G.neighborFinset x⊆insert a (C.A.erase x ∪ C.E) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed C.j x xh y xy with rfl|rfl|yh
    · simp
    · exact (C.no_common ax xy.symm).elim
    · refine mem_insert.mpr (Or.inr (mem_union.mpr ?_))
      by_cases ay : G.Adj a y
      · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,C.memA.mpr ⟨yh,ay⟩⟩)
      have ne : a≠y := fun e => (S.off C.j).1 (e.symm ▸ yh)
      exact Or.inr (C.memE.mpr ⟨yh,Sides.dist_two S.con ne ay ax xy⟩)
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have d := card_insert_le a (C.A.erase x∪C.E)
  have e := card_union_le (C.A.erase x) C.E
  rw [card_erase_of_mem xa] at e
  have ap := C.Apos
  omega

theorem high_of_two {Q : Finset V} (two : 2≤Q.card) : ∃ x∈Q,4≤G.degree x := by
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1<Q.card by omega)
  exact (S.degree x y ne).elim (fun d => ⟨x,hx,d⟩) (fun d => ⟨y,hy,d⟩)

theorem local_a_d2 {x y : V} (xa : x∈C.A) (yh : y∈C.H) (ya : y∉C.A) (xy : G.Adj x y) :
    y∈C.E := by
  have ne : a≠y := fun e => (S.off C.j).1 (e.symm ▸ yh)
  have ay : ¬G.Adj a y := fun e => ya (C.memA.mpr ⟨yh,e⟩)
  exact C.memE.mpr ⟨yh,Sides.dist_two S.con ne ay (C.memA.mp xa).2 xy⟩

theorem local_a_witness {y : V} (ye : y∈C.E) :
    ∃ x∈C.A,G.Adj x y := by
  obtain ⟨yh,de⟩ := C.memE.mp ye
  obtain ⟨p,pl⟩ := S.con.exists_walk_length_eq_dist a y
  rw [de] at pl
  cases p with
  | nil => simp at pl
  | @cons _ x _ ax q =>
    cases q with
    | nil => simp at pl
    | @cons _ z _ xz r =>
      have zero : r.length=0 := by simp at pl; omega
      have eq : z=y := eq_of_length_eq_zero (p:=r) zero
      subst z
      have e : G.Adj x y := xz
      rcases S.all x with rfl|rfl|⟨j,jh⟩
      · exact (ax.ne rfl).elim
      · exact (C.cut_not_adj ax).elim
      by_cases eq : j=C.i
      · exact (C.no_other_edge yh (show x∈S.H _ from eq ▸ jh) e.symm).elim
      have eq : j=C.j := by
        have ne := C.different
        cases j <;> cases hi : C.i <;> cases hj : C.j <;> simp_all
      exact ⟨x,C.memA.mpr ⟨show x∈S.H _ from eq ▸ jh,ax⟩,e⟩

theorem E_dis_A : Disjoint C.E C.A := disjoint_left.mpr (by
  intro x xe xa
  have e := (C.memE.mp xe).2
  have d := dist_eq_one_iff_adj.mpr (C.memA.mp xa).2
  omega)

theorem foreign_U_d2 {x y : V} (xa : x∈C.A) (yu : y∈C.U) : y∈DistanceTwo G x := by
  obtain ⟨xh,ax⟩ := C.memA.mp xa
  obtain ⟨yk,ay⟩ := C.memU.mp yu
  have ne : x≠y := fun e => disjoint_left.mp C.dis_KH yk (e ▸ xh)
  exact Sides.mem_d2.mpr (Sides.dist_two S.con ne (C.no_other_edge xh yk) ax.symm ay)

theorem local_d2_cap {x : V} (xa : x∈C.A) {Q : Finset V} (sub : Q⊆C.H)
    (ds : Q⊆DistanceTwo G x) : Q.card+C.U.card≤4 := by
  have dis : Disjoint Q C.U := (C.dis_KH.symm).mono sub (fun _ h => (C.memU.mp h).1)
  have le := card_le_card (union_subset ds (fun _ hy => C.foreign_U_d2 xa hy))
  rw [card_union_of_disjoint dis] at le
  exact le.trans (C.d2_le x)

theorem local_A_neighbor_sub {x : V} (xa : x∈C.A) :
    G.neighborFinset x⊆insert a (C.A.erase x∪C.E) := by
  obtain ⟨xh,ax⟩ := C.memA.mp xa
  intro y hy
  have xy := (mem_neighborFinset G x y).mp hy
  rcases S.closed C.j x xh y xy with rfl|rfl|yh
  · simp
  · exact (C.no_common ax xy.symm).elim
  refine mem_insert.mpr (Or.inr (mem_union.mpr ?_))
  by_cases ay : y∈C.A
  · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,ay⟩)
  · exact Or.inr (C.local_a_d2 xa yh ay xy)

theorem local_A_neighbor_of_tight {x : V} (xa : x∈C.A) (high : 4≤G.degree x)
    (tight : C.A.card+C.E.card=4) :
    G.neighborFinset x = insert a (C.A.erase x∪C.E) := by
  apply eq_of_subset_of_card_le (C.local_A_neighbor_sub xa)
  have c := card_insert_le a (C.A.erase x∪C.E)
  have q := card_union_le (C.A.erase x) C.E
  rw [card_erase_of_mem xa] at q
  rw [card_neighborFinset_eq_degree]
  have pos := C.Apos
  omega

theorem tight_joins_E {x y : V} (xa : x∈C.A) (ye : y∈C.E)
    (high : 4≤G.degree x) (tight : C.A.card+C.E.card=4) : G.Adj x y := by
  apply (mem_neighborFinset G x y).mp
  rw [C.local_A_neighbor_of_tight xa high tight]
  exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr ye)))

theorem tight_joins_peer {x y : V} (xa : x∈C.A) (ya : y∈C.A) (xy : x≠y)
    (high : 4≤G.degree x) (tight : C.A.card+C.E.card=4) : G.Adj x y := by
  apply (mem_neighborFinset G x y).mp
  rw [C.local_A_neighbor_of_tight xa high tight]
  exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl (mem_erase.mpr ⟨xy.symm,ya⟩))))

theorem H_abs {x : V} (xh : x∈C.H) : x≠a ∧ x≠b :=
  ⟨fun e => (S.off C.j).1 (e ▸ xh),fun e => (S.off C.j).2 (e ▸ xh)⟩

theorem split_H {x : V} (xh : x∈C.H) : x∈C.A ∨ x∈C.B ∨ x∈C.I := by
  by_cases ax : G.Adj a x
  · exact Or.inl (C.memA.mpr ⟨xh,ax⟩)
  by_cases bx : G.Adj b x
  · exact Or.inr (Or.inl (C.memB.mpr ⟨xh,bx⟩))
  · exact Or.inr (Or.inr (C.memI.mpr ⟨xh,ax,bx⟩))

theorem eq_A_neighbor_if_one {x : V} (xa : x∈C.A) (one : C.A.card=1) {y : V} :
    y∈C.E ↔ y∈C.H ∧ G.Adj x y := by
  constructor
  · intro ye
    obtain ⟨u,ua,uy⟩ := C.local_a_witness ye
    have eq := card_le_one.mp (show C.A.card≤1 by omega) u ua x xa
    exact ⟨(C.memE.mp ye).1,eq ▸ uy⟩
  · rintro ⟨yh,xy⟩
    have yn : y∉C.A := fun e => xy.ne (card_le_one.mp (show C.A.card≤1 by omega) _ xa _ e)
    exact C.local_a_d2 xa yh yn xy

private theorem E_pos_aux : C.E.Nonempty := by
  by_cases e : C.E.Nonempty
  · exact e
  exfalso
  obtain ⟨x,xa⟩ := card_pos.mp C.Apos
  obtain ⟨y,yb⟩ := card_pos.mp C.swap.Apos
  obtain ⟨q,qs⟩ := C.joined_H (C.memA.mp xa).1 (C.memB.mp yb).1
  have go {u v : V} (w : G.Walk u v) (ws : ∀ z∈w.support,z∈C.H)
      (ua : u∈C.A) : v∈C.A := by
    induction w with
    | nil => exact ua
    | @cons u z v uz w ih =>
      apply ih (fun w hw => ws w (by simp [hw]))
      by_cases za : z∈C.A
      · exact za
      exact (e ⟨z,C.local_a_d2 ua (ws z (by simp)) za uz⟩).elim
  exact disjoint_left.mp C.dis_AB (go q qs xa) yb

theorem E_pos : 1≤C.E.card := card_pos.mpr C.E_pos_aux

theorem shell_sum : C.E.card+C.other.E.card≤4 := by
  have d : Disjoint C.E C.other.E :=
    C.dis_KH.symm.mono (fun _ h => (C.memE.mp h).1) (fun _ h => (C.other.memE.mp h).1)
  have sub : C.E∪C.other.E⊆DistanceTwo G a := union_subset
    (fun _ h => Sides.mem_d2.mpr (C.memE.mp h).2)
    (fun _ h => Sides.mem_d2.mpr (C.other.memE.mp h).2)
  have k := card_le_card sub
  rw [card_union_of_disjoint d] at k
  exact k.trans (C.d2_le a)

theorem cut_high : 4≤G.degree a := by
  by_contra! lo
  have h1 {D : DistThreeCtx S} : 4≤D.A.card+D.E.card := by
    obtain ⟨x,xa⟩ := card_pos.mp D.Apos
    have ne : a≠x := (D.H_abs (D.memA.mp xa).1).1.symm
    exact ((S.degree a x ne).resolve_left (by omega)).trans (D.degree_A xa)
  have p := h1 (D:=C)
  have q := h1 (D:=C.other)
  have r := C.shell_sum
  have eq := C.cut_deg_a
  change 4≤C.U.card+C.other.E.card at q
  omega

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

theorem port_extra {x : V} (xa : x∈C.A) :
    ∃ y, y∈DistanceTwo G x ∧ (y=b ∨ y∈C.H) :=
  S.extra_d2 C.far (C.memA.mp xa).1 (C.memA.mp xa).2

theorem saturated_of_foreign_three {x : V} (xa : x∈C.A) (u3 : C.U.card=3) :
    (DistanceTwo G x).card=4 ∧ ∀ y, G.dist x y≤3 := by
  obtain ⟨z,zd,zown⟩ := C.port_extra xa
  have zn : z∉C.U := by
    intro zU
    have zK := (C.memU.mp zU).1
    rcases zown with e|e
    · exact (S.off C.i).2 (e ▸ zK)
    · exact disjoint_left.mp C.dis_KH zK e
  have sub : insert z C.U⊆DistanceTwo G x := by
    intro t ht
    exact (mem_insert.mp ht).elim (fun e => e.symm ▸ zd) (fun tU => C.foreign_U_d2 xa tU)
  have card := card_le_card sub
  rw [card_insert_of_not_mem zn,u3] at card
  have upper := C.d2_le x
  refine ⟨by omega,?_⟩
  intro y
  by_contra! far
  have k := distanceTwo_add_two_le_even_of_far S.con (show 4≤G.dist x y by omega)
  have ce := S.even x
  omega

theorem bridge_universal {x y : V} (xa : x∈C.A) (yb : y∈C.B) (xy : G.Adj x y)
    (u3 : C.U.card=3) : ∀ z∈C.H, x=z ∨ G.Adj x z := by
  have xd : b∈DistanceTwo G x := Sides.mem_d2.mpr (Sides.dist_two S.con
    (C.H_abs (C.memA.mp xa).1).2 (fun e => C.no_common (C.memA.mp xa).2 e.symm)
    xy (C.memB.mp yb).2.symm)
  have bno : b∉C.U := fun e => (S.off C.i).2 (C.memU.mp e).1
  have sub : insert b C.U⊆DistanceTwo G x := by
    intro z hz
    exact (mem_insert.mp hz).elim (fun e => e.symm ▸ xd) (fun h => C.foreign_U_d2 xa h)
  have eq : insert b C.U=DistanceTwo G x := eq_of_subset_of_card_le sub (by
    rw [card_insert_of_not_mem bno,u3]; exact C.d2_le x)
  have forbid {z : V} (zh : z∈C.H) : z∉DistanceTwo G x := by
    rw [←eq]
    intro zin
    rcases mem_insert.mp zin with e|e
    · exact (C.H_abs zh).2 e
    · exact disjoint_left.mp C.dis_KH (C.memU.mp e).1 zh
  intro z zh
  obtain ⟨w,ws⟩ := C.joined_H (C.memA.mp xa).1 zh
  have prop {u v : V} (q : G.Walk u v) (qs : ∀ z∈q.support,z∈C.H)
      (xu : x=u ∨ G.Adj x u) : x=v ∨ G.Adj x v := by
    induction q with
    | nil => exact xu
    | @cons u z v uz w ih =>
      apply ih (fun y hy => qs y (by simp [hy]))
      rcases xu with e|xu
      · exact Or.inr (e.symm ▸ uz)
      by_cases e : x=z
      · exact Or.inl e
      by_cases xz : G.Adj x z
      · exact Or.inr xz
      exact (forbid (qs z (by simp)) (Sides.mem_d2.mpr (Sides.dist_two S.con e xz xu uz))).elim
  exact prop w ws (Or.inl rfl)

theorem bridge_propagates {x y : V} (xa : x∈C.A) (yb : y∈C.B) (xy : G.Adj x y)
    (u3 : C.U.card=3) (b2 : 2≤C.B.card) :
    ∀ z∈C.A, ∀ w∈C.H,z=w ∨ G.Adj z w := by
  have first := C.bridge_universal xa yb xy u3
  intro z za
  by_cases e : z=x
  · subst z
    exact first
  have zx := (first z (C.memA.mp za).1).resolve_left (Ne.symm e) |>.symm
  let Bmiss := C.B.filter (fun w => ¬G.Adj z w)
  have bs : Bmiss⊆DistanceTwo G z := by
    intro w hw
    obtain ⟨wb,nw⟩ := mem_filter.mp hw
    have zw : z≠w := fun e => disjoint_left.mp C.dis_AB za (e.symm ▸ wb)
    have xw : x≠w := fun e => disjoint_left.mp C.dis_AB xa (e.symm ▸ wb)
    exact Sides.mem_d2.mpr (Sides.dist_two S.con zw nw zx
      ((first w (C.memB.mp wb).1).resolve_left xw))
  have c : Bmiss.card+C.U.card≤4 := C.local_d2_cap za (fun _ h => (C.memB.mp (mem_filter.mp h).1).1) bs
  have nonempty : ∃ w∈C.B,G.Adj z w := by
    by_cases ex : ∃ w∈C.B,G.Adj z w
    · exact ex
    exfalso
    have s : C.B⊆Bmiss := fun w wb => mem_filter.mpr ⟨wb,fun zw => ex ⟨w,wb,zw⟩⟩
    have card := card_le_card s
    omega
  obtain ⟨w,wb,zw⟩ := nonempty
  exact C.bridge_universal za wb zw u3

#print axioms cut_high
#print axioms bridge_propagates

def Bridge : Prop := ∃ x∈C.A,∃ y∈C.B,G.Adj x y
theorem bridge_swap : C.swap.Bridge ↔ C.Bridge := by
  constructor <;> rintro ⟨x,xa,y,yb,e⟩ <;> exact ⟨y,yb,x,xa,e.symm⟩

theorem shell_eq_of_universal {x : V} (xa : x∈C.A)
    (all : ∀ y∈C.H,x=y ∨ G.Adj x y) : C.E=C.H\C.A := by
  ext y
  constructor
  · intro ye
    exact mem_sdiff.mpr ⟨(C.memE.mp ye).1,fun ya => disjoint_left.mp C.E_dis_A ye ya⟩
  · intro yd
    obtain ⟨yh,yn⟩ := mem_sdiff.mp yd
    have xy := (all y yh).resolve_left (fun e => yn (e ▸ xa))
    exact C.local_a_d2 xa yh yn xy

theorem shell_sub_inner_no_bridge (no : ¬C.Bridge) : C.E⊆C.I := by
  intro y ye
  rcases C.split_H (C.memE.mp ye).1 with ya|yb|yi
  · exact (disjoint_left.mp C.E_dis_A ye ya).elim
  · obtain ⟨x,xa,xy⟩ := C.local_a_witness ye
    exact (no ⟨x,xa,y,yb,xy⟩).elim
  · exact yi

theorem I_sub_H : C.I⊆C.H := fun _ h => (C.memI.mp h).1
theorem A_sub_H : C.A⊆C.H := fun _ h => (C.memA.mp h).1
theorem B_sub_H : C.B⊆C.H := fun _ h => (C.memB.mp h).1

theorem port_b_dist_ge_three {x : V} (xa : x∈C.A) (no : ∀ y∈C.B,¬G.Adj x y) :
    3≤G.dist x b := by
  have xh := C.A_sub_H xa
  have nxb : ¬G.Adj x b := fun e => C.no_common (C.memA.mp xa).2 e.symm
  have gd := S.con.one_lt_dist_of_ne_of_not_adj (C.H_abs xh).2 nxb
  by_contra! d
  have be : x∈C.F := C.memF.mpr ⟨xh,by rw [dist_comm]; omega⟩
  obtain ⟨y,yb,yx⟩ := C.swap.local_a_witness be
  exact no y yb yx.symm

theorem foreign_opp_near {x : V} (xa : x∈C.A) (u3 : C.U.card=3)
    (no : ∀ y∈C.B,¬G.Adj x y) : C.W⊆C.other.E := by
  have xb := C.port_b_dist_ge_three xa no
  obtain ⟨_,ecc⟩ := C.saturated_of_foreign_three xa u3
  intro z zw
  have ⟨zk,bz⟩ := C.memW.mp zw
  have zx := ecc z
  have eq := S.cross_distance_eq C.different.symm (C.A_sub_H xa) zk
  have xa1 : G.dist x a=1 := dist_eq_one_iff_adj.mpr (C.memA.mp xa).2.symm
  have bz1 : G.dist b z=1 := dist_eq_one_iff_adj.mpr bz
  have az : 1<G.dist a z := S.con.one_lt_dist_of_ne_of_not_adj
    (fun e => (S.off C.i).1 (e.symm ▸ zk)) (fun e => C.no_common e bz)
  exact C.other.memE.mpr ⟨zk,by omega⟩

theorem foreign_inner_near {x y : V} (xa : x∈C.A) (yb : y∈C.B) (xy : G.Adj x y)
    (u3 : C.U.card=3) : C.other.I⊆C.other.E := by
  obtain ⟨_,ecc⟩ := C.saturated_of_foreign_three xa u3
  have xb2 : G.dist x b=2 := Sides.dist_two S.con (C.H_abs (C.A_sub_H xa)).2
    (fun e => C.no_common (C.memA.mp xa).2 e.symm) xy (C.memB.mp yb).2.symm
  have xa1 : G.dist x a=1 := dist_eq_one_iff_adj.mpr (C.memA.mp xa).2.symm
  intro z zi
  obtain ⟨zk,az,bz⟩ := C.other.memI.mp zi
  have a_lt := S.con.one_lt_dist_of_ne_of_not_adj
    (C.other.H_abs zk).1.symm az
  have b_lt := S.con.one_lt_dist_of_ne_of_not_adj
    (C.other.H_abs zk).2.symm bz
  have dx := ecc z
  have eq := S.cross_distance_eq C.different.symm (C.A_sub_H xa) zk
  exact C.other.memE.mpr ⟨zk,by omega⟩

theorem B_inter_E_of_saturated_no_bridge (u3 : C.U.card=3)
    (no : ¬C.Bridge) {x : V} (xa : x∈C.A) :
    ∃ r∈C.E,r∈C.F ∧ G.Adj x r := by
  have d := C.port_b_dist_ge_three xa (fun y yb e => no ⟨x,xa,y,yb,e⟩)
  obtain ⟨_,ecc⟩ := C.saturated_of_foreign_three xa u3
  obtain ⟨w,wl⟩ := S.con.exists_walk_length_eq_dist x b
  have d3 : G.dist x b=3 := by have h := ecc b; omega
  rw [d3] at wl
  cases w with
  | nil => simp at wl
  | @cons _ r _ xr w =>
    cases w with
    | nil => simp at wl
    | @cons _ y _ ry w =>
      cases w with
      | nil => simp at wl
      | @cons _ z _ yz w =>
        have wz : w.length=0 := by simp at wl; omega
        have eq : z=b := eq_of_length_eq_zero (p:=w) wz
        subst z
        have rh : r∈C.H := by
          rcases S.closed C.j x (C.A_sub_H xa) r xr with er|er|er
          · have r_b : G.dist r b≤2 := by
              have h := G.dist_le (Walk.cons ry (Walk.cons yz Walk.nil))
              simp at h
              exact h
            have dc := C.cut_dist
            rw [er] at r_b
            omega
          · exact (C.no_common (C.memA.mp xa).2 (er ▸ xr).symm).elim
          · exact er
        have yh : y∈C.H := by
          rcases S.closed C.j r rh y ry with ey|ey|ey
          · exact (C.cut_not_adj (ey ▸ yz)).elim
          · exact (yz.ne ey).elim
          · exact ey
        have yb : y∈C.B := C.memB.mpr ⟨yh,yz.symm⟩
        have ra : r∉C.A := fun ra => no ⟨r,ra,y,yb,ry⟩
        have rb : r∉C.B := fun rb => no ⟨x,xa,r,rb,xr⟩
        exact ⟨r,C.local_a_d2 xa rh ra xr,C.swap.local_a_d2 yb rh rb ry.symm,xr⟩

private theorem singleton_no_bridge (A1 : C.A.card=1) (U3 : C.U.card=3)
    (large : 5≤C.H.card) : ¬C.Bridge := by
  rintro ⟨x,xa,y,yb,xy⟩
  have un := C.bridge_universal xa yb xy U3
  have eq := C.shell_eq_of_universal xa un
  have ct := card_sdiff_add_card_eq_card C.A_sub_H
  rw [←eq] at ct
  have as := C.shell_sum
  have pos := C.other.E_pos
  omega

theorem no_single_large (first : 5≤C.H.card) (second : 5≤C.K.card) : 2≤C.A.card := by
  have pos := C.Apos
  by_cases A1 : C.A.card=1
  · exfalso
    have d := C.cut_deg_a
    have hi := C.cut_high
    have cap := C.Ucap
    have U3 : C.U.card=3 := by omega
    have no := C.singleton_no_bridge A1 U3 first
    obtain ⟨x,xa⟩ := card_pos.mp pos
    have zstop (y : V) (yb : y∈C.B) : ¬G.Adj x y := fun e => no ⟨x,xa,y,yb,e⟩
    have all := C.foreign_opp_near xa U3 zstop
    have cb := card_le_card all
    have small : 3≤C.E.card := by
      by_cases xhigh : 4≤G.degree x
      · have g := C.degree_A xa
        omega
      have op : ∃ y∈C.E,G.Adj x y := by
        by_cases ex : ∃ y∈C.E,G.Adj x y
        · exact ex
        exfalso
        have sub : G.neighborFinset x⊆{a} := by
          intro u hu
          rcases mem_insert.mp (C.local_A_neighbor_sub xa hu) with eu|eu
          · exact mem_singleton.mpr eu
          rcases mem_union.mp eu with uA|uE
          · obtain ⟨ne,ua⟩ := mem_erase.mp uA
            exact (ne (card_le_one.mp (by omega : C.A.card≤1) u ua x xa)).elim
          · exact (ex ⟨u,uE,(mem_neighborFinset G x u).mp hu⟩).elim
        have cd := card_le_card sub
        rw [card_neighborFinset_eq_degree,card_singleton] at cd
        have nd := C.min2 x
        omega
      obtain ⟨y,ye,xy⟩ := op
      have yhi := (S.degree x y xy.ne).resolve_left xhigh
      have yi := C.shell_sub_inner_no_bridge no ye
      let B := insert x (C.E.erase y)
      let Q := G.neighborFinset y \ B
      have cover : Q⊆C.H := by
        intro z zq
        have yz := (mem_neighborFinset G y z).mp (mem_sdiff.mp zq).1
        have yi' := C.memI.mp yi
        rcases S.closed C.j y yi'.1 z yz with rfl|rfl|zh
        · exact (yi'.2.1 yz.symm).elim
        · exact (yi'.2.2 yz.symm).elim
        · exact zh
      have dset : Q⊆DistanceTwo G x := by
        intro z zq
        have yz := (mem_neighborFinset G y z).mp (mem_sdiff.mp zq).1
        have qno := (mem_sdiff.mp zq).2
        have ne : x≠z := fun e => qno (mem_insert.mpr (Or.inl e.symm))
        have nedge : ¬G.Adj x z := fun e => qno (mem_insert_of_mem
          (mem_erase.mpr ⟨yz.ne.symm,(C.eq_A_neighbor_if_one xa A1).mpr ⟨cover zq,e⟩⟩))
        exact Sides.mem_d2.mpr (Sides.dist_two S.con ne nedge xy yz)
      have cc := C.local_d2_cap xa cover dset
      have cB := card_insert_le x (C.E.erase y)
      rw [card_erase_of_mem ye] at cB
      have covers : G.neighborFinset y⊆Q∪B := by
        intro z hz
        by_cases hb : z∈B
        · exact mem_union.mpr (Or.inr hb)
        · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hz,hb⟩))
      have cp := card_le_card covers
      rw [card_neighborFinset_eq_degree] at cp
      have cn := card_union_le Q B
      have ep := C.E_pos
      change B.card≤C.E.card-1+1 at cB
      omega
    have sm := C.shell_sum
    have Wpos := C.swap.Upos
    change 1≤C.W.card at Wpos
    have w1 : C.W.card=1 := by omega
    have highb := C.swap.cut_high
    have db := C.swap.cut_deg_a
    change G.degree b=C.W.card+C.B.card at db
    have bcap := C.swap.Acap
    change C.B.card≤3 at bcap
    have B3 : C.B.card=3 := by omega
    have nob := C.other.swap.singleton_no_bridge w1 B3 second
    obtain ⟨z,zw⟩ := card_pos.mp Wpos
    obtain ⟨q,qa,qz⟩ := C.other.local_a_witness (all zw)
    exact nob ⟨z,zw,q,qa,qz.symm⟩
  · omega

#print axioms no_single_large
end
end DistThreeCtx
end Graffiti189LongestPath.TwoCut
