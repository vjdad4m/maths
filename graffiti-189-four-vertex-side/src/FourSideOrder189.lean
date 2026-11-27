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

structure FourSideCtx (S : CutPair G a b) where
  i : Bool
  size : (S.H i).card=4
  far : 3≤G.dist a b
  conn : ∀ B : Finset V, B.card<2 → (G.induce ((↑B : Set V)ᶜ)).Connected
  min2 : ∀ x, 2≤G.degree x

namespace FourSideCtx
noncomputable section
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
def K := S.H C.i
def H := S.H (!C.i)
def U := S.A C.i
def W := S.flip.A C.i
def A := S.A (!C.i)
def B := S.flip.A (!C.i)
def E := S.D (!C.i)
def F := S.flip.D (!C.i)
def I := C.H \ (C.A ∪ C.B)
def swap : FourSideCtx S.flip := ⟨C.i,C.size,(by rw [dist_comm]; exact C.far),C.conn,C.min2⟩

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

theorem dis_KH : Disjoint C.K C.H := S.disjoint_sides (by cases C.i <;> decide)
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
  obtain ⟨x,h,xadj⟩ := S.hita (!C.i)
  exact card_pos.mpr ⟨x,C.memA.mpr ⟨h,xadj⟩⟩
theorem Ucap : C.U.card≤3 := S.at_most_three_a_ports C.far C.i
theorem Acap : C.A.card≤3 := S.at_most_three_a_ports C.far (!C.i)

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
      have eq : j= !C.i := by cases j <;> cases hc : C.i <;> simp_all
      exact mem_union.mpr (Or.inr (C.memA.mpr ⟨show x∈S.H _ from eq ▸ h,ax⟩))
    · intro e
      exact (mem_neighborFinset G a _).mpr ((mem_union.mp e).elim
        (fun h => (C.memU.mp h).2) (fun h => (C.memA.mp h).2))
  rw [←card_neighborFinset_eq_degree,eq,card_union_of_disjoint
    (C.dis_KH.mono (fun _ h => (C.memU.mp h).1) (fun _ h => (C.memA.mp h).1))]

theorem e_cap : C.E.card≤C.U.card := by
  have hsub : C.K \ C.U ⊆ DistanceTwo G a := by
    intro z zz
    obtain ⟨zk,zu⟩ := mem_sdiff.mp zz
    obtain ⟨x,xu⟩ := card_pos.mp C.Upos
    obtain ⟨xk,ax⟩ := C.memU.mp xu
    have xz : x≠z := fun e => zu (e ▸ xu)
    have az : a≠z := fun e => (S.off C.i).1 (e.symm ▸ zk)
    have az' : ¬G.Adj a z := fun e => zu (C.memU.mpr ⟨zk,e⟩)
    exact Sides.mem_d2.mpr (Sides.dist_two S.con az az' ax (S.side_four_clique C.far C.size xk zk xz))
  have esub : C.E⊆DistanceTwo G a := fun _ h => Sides.mem_d2.mpr (C.memE.mp h).2
  have ds : Disjoint (C.K \ C.U) C.E :=
    C.dis_KH.mono sdiff_subset (fun _ h => (C.memE.mp h).1)
  have card := card_le_card (union_subset hsub esub)
  rw [card_union_of_disjoint ds] at card
  have e := card_sdiff_add_card_eq_card (show C.U⊆C.K from fun _ h => (C.memU.mp h).1)
  have cap := C.d2_le a
  have c := C.size
  change C.K.card=4 at c
  omega

theorem degree_A {x : V} (xa : x∈C.A) :
    G.degree x≤C.A.card+C.E.card := by
  obtain ⟨xh,ax⟩ := C.memA.mp xa
  have sub : G.neighborFinset x⊆insert a (C.A.erase x ∪ C.E) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed (!C.i) x xh y xy with rfl|rfl|yh
    · simp
    · exact (C.no_common ax xy.symm).elim
    · refine mem_insert.mpr (Or.inr (mem_union.mpr ?_))
      by_cases ay : G.Adj a y
      · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,C.memA.mpr ⟨yh,ay⟩⟩)
      have ne : a≠y := fun e => (S.off (!C.i)).1 (e.symm ▸ yh)
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

theorem U_eq_three_of_A_one (h : C.A.card=1) : C.U.card=3 := by
  obtain ⟨x,hx⟩ := card_pos.mp C.Apos
  have ax : a≠x := fun e => (S.off (!C.i)).1 (e.symm ▸ (C.memA.mp hx).1)
  have d := C.degree_A hx
  have d' := C.cut_deg_a
  have cap := C.e_cap
  have U := C.Ucap
  rcases S.degree a x ax with h|h <;> omega

theorem port_K_sum : 3≤C.U.card+C.W.card ∧ C.U.card+C.W.card≤4 := by
  have c : C.K.card=4 := C.size
  have Usub : C.U∪C.W⊆C.K :=
    union_subset (fun _ h => (C.memU.mp h).1) (fun _ h => (C.memW.mp h).1)
  have count := card_sdiff_add_card_eq_card Usub
  have upper := card_le_card Usub
  rw [card_union_of_disjoint C.dis_UW] at count upper
  have low (x : V) (hx : x∈C.K \ (C.U∪C.W)) : ¬4≤G.degree x := by
    intro ge
    obtain ⟨xk,xn⟩ := mem_sdiff.mp hx
    have sub : G.neighborFinset x ⊆ C.K.erase x := by
      intro y hy
      have e := (mem_neighborFinset G x y).mp hy
      rcases S.closed C.i x xk y e with rfl|rfl|yk
      · exact (xn (mem_union.mpr (Or.inl (C.memU.mpr ⟨xk,e.symm⟩)))).elim
      · exact (xn (mem_union.mpr (Or.inr (C.memW.mpr ⟨xk,e.symm⟩)))).elim
      · exact mem_erase.mpr ⟨e.ne.symm,yk⟩
    have k := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem xk,c] at k
    omega
  have one : (C.K\(C.U∪C.W)).card≤1 := card_le_one.mpr (by
    intro x hx y hy
    exact Classical.byContradiction (fun ne => (S.degree x y ne).elim (low x hx) (low y hy)))
  omega

theorem two_foreign_and_other_cut {x : V} (xu : x∈C.U) :
    insert b C.A⊆DistanceTwo G x := by
  intro y hy
  obtain ⟨xk,ax⟩ := C.memU.mp xu
  rcases mem_insert.mp hy with yb|ya
  · subst y
    obtain ⟨z,zw⟩ := card_pos.mp C.swap.Upos
    obtain ⟨zk,bz⟩ := C.memW.mp zw
    have xz : x≠z := fun e => C.no_common ax (e.symm ▸ bz)
    have xb : x≠b := fun e => (S.off C.i).2 (e ▸ xk)
    have no : ¬G.Adj x b := fun e => C.no_common ax e.symm
    exact Sides.mem_d2.mpr (Sides.dist_two S.con xb no (S.side_four_clique C.far C.size xk zk xz) bz.symm)
  obtain ⟨yh,ay⟩ := C.memA.mp ya
  have ne : x≠y := fun e => disjoint_left.mp C.dis_KH xk (e.symm ▸ yh)
  exact Sides.mem_d2.mpr (Sides.dist_two S.con ne (fun e => C.no_other_edge yh xk e.symm) ax.symm ay)

theorem inner_away_cap (two : 2≤C.A.card) :
    (C.I \ C.E).card≤3-C.A.card := by
  obtain ⟨x,xu⟩ := card_pos.mp C.Upos
  obtain ⟨xk,ax⟩ := C.memU.mp xu
  have two_b := C.two_foreign_and_other_cut xu
  have bno : b∉C.A := fun h => (S.off (!C.i)).2 (C.memA.mp h).1
  have ge := card_le_card two_b
  rw [card_insert_of_not_mem bno] at ge
  have ecc (y : V) : G.dist x y≤4 := by
    by_contra! far
    have D4 := shell_card_of_far S.con 2 C.conn (x:=x) (y:=y) (by decide) (by omega : 4<G.dist x y)
    have bg := shell_two_four_le_of_even (x:=x) (d:=4) (S.even x)
    have de : Shell G x 2=DistanceTwo G x := by ext z; simp [Shell,DistanceTwo]
    rw [de] at bg
    omega
  have sub : C.I \ C.E⊆Shell G x 4 := by
    intro y hy
    obtain ⟨yin,bad⟩ := mem_sdiff.mp hy
    obtain ⟨yh,ay,by'⟩ := C.memI.mp yin
    have xb : G.dist x b=2 := Sides.mem_d2.mp (two_b (mem_insert_self _ _))
    have xa : G.dist x a=1 := dist_eq_one_iff_adj.mpr ax.symm
    have a_ne : a≠y := fun e => (S.off (!C.i)).1 (e.symm ▸ yh)
    have b_ne : b≠y := fun e => (S.off (!C.i)).2 (e.symm ▸ yh)
    have ay2 := S.con.one_lt_dist_of_ne_of_not_adj a_ne ay
    have by2 := S.con.one_lt_dist_of_ne_of_not_adj b_ne by'
    have no2 : G.dist a y≠2 := fun e => bad (C.memE.mpr ⟨yh,e⟩)
    have eq := S.cross_distance_eq (by cases C.i <;> decide) xk yh
    have u := ecc y
    apply mem_shell.mpr
    omega
  have cf := card_le_card sub
  have bg := shell_two_four_le_of_even (x:=x) (d:=4) (S.even x)
  have de : Shell G x 2=DistanceTwo G x := by ext z; simp [Shell,DistanceTwo]
  rw [de] at bg
  omega

theorem inner_cap (two : 2≤C.A.card) : C.I.card≤C.U.card+3-C.A.card := by
  have e := C.inner_away_cap two
  have s := card_sdiff_add_card_eq_card (inter_subset_left : C.I∩C.E⊆C.I)
  have c := card_le_card (inter_subset_right : C.I∩C.E⊆C.E)
  have eq : C.I \ (C.I ∩ C.E)=C.I \ C.E := by ext x; simp
  rw [eq] at s
  have ec := C.e_cap
  have ap := C.Acap
  omega

#print axioms inner_cap

theorem local_a_d2 {x y : V} (xa : x∈C.A) (yh : y∈C.H) (ya : y∉C.A) (xy : G.Adj x y) :
    y∈C.E := by
  have ne : a≠y := fun e => (S.off (!C.i)).1 (e.symm ▸ yh)
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
      have eq : j= !C.i := by cases j <;> cases hc : C.i <;> simp_all
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
  rcases S.closed (!C.i) x xh y xy with rfl|rfl|yh
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

theorem large_no_single (large : 7≤C.H.card) : 2≤C.A.card := by
  have Ap := C.Apos
  by_cases one : C.A.card=1
  · exfalso
    have U3 := C.U_eq_three_of_A_one one
    have bd := C.port_K_sum
    have wp := C.swap.Upos
    change 1≤C.W.card at wp
    have wone : C.W.card=1 := by omega
    have bp := C.swap.Apos
    have bc := C.swap.Acap
    change 1≤C.B.card at bp
    change C.B.card≤3 at bc
    have be := C.swap.e_cap
    change C.F.card≤C.W.card at be
    have not1 : C.B.card≠1 := fun e => by
      have h := C.swap.U_eq_three_of_A_one e
      change C.W.card=3 at h
      omega
    have not2 : C.B.card≠2 := fun e => by
      obtain ⟨x,hx,high⟩ := C.high_of_two (show 2≤C.B.card by omega)
      have deg := C.swap.degree_A hx
      change G.degree x≤C.B.card+C.F.card at deg
      omega
    have ge : 2≤C.B.card := by omega
    have cap := C.swap.inner_cap ge
    rw [C.swap_I] at cap
    change C.I.card≤C.W.card+3-C.B.card at cap
    have eq := C.count_H
    omega
  · omega

theorem high_port_implies_foreign_ge_two (atwo : C.A.card=2) : 2≤C.U.card := by
  obtain ⟨x,xa,high⟩ := C.high_of_two (show 2≤C.A.card by omega)
  have e := C.e_cap
  have d := C.degree_A xa
  omega

#print axioms local_a_witness
#print axioms large_no_single
end
end FourSideCtx
end Graffiti189LongestPath.TwoCut
