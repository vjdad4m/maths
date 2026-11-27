import SaturatedTwo189
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

structure CutPair (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) where
  con : G.Connected
  ab : a≠b
  even : ∀ x, (EvenFrom G x).card≤5
  degree : ∀ x y : V, x≠y → 4≤G.degree x ∨ 4≤G.degree y
  H : Bool → Finset V
  dis : Disjoint (H false) (H true)
  off : ∀ i, a∉H i ∧ b∉H i
  all : ∀ x, x=a ∨ x=b ∨ ∃ i,x∈H i
  closed : ∀ i, ∀ x∈H i, ∀ y, G.Adj x y → y=a ∨ y=b ∨ y∈H i
  joined : ∀ i, ∀ x∈H i, ∀ y∈H i, ∃ q : G.Walk x y, ∀ z∈q.support, z∈H i
  hita : ∀ i, ∃ x∈H i,G.Adj a x
  hitb : ∀ i, ∃ x∈H i,G.Adj b x

namespace CutPair
noncomputable section
variable {a b : V} (S : CutPair G a b)
def A (i : Bool) := (S.H i).filter (G.Adj a)
def D (i : Bool) := (S.H i).filter (fun x => x∈DistanceTwo G a)
def flip : CutPair G b a :=
  ⟨S.con,S.ab.symm,S.even,S.degree,S.H,S.dis,fun i => (S.off i).symm,
    fun x => (S.all x).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))),
    fun i x hx y xy => (S.closed i x hx y xy).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))),
    S.joined,S.hitb,S.hita⟩

theorem disjoint_sides {i j : Bool} (ne : i≠j) : Disjoint (S.H i) (S.H j) := by
  cases i <;> cases j
  · exact (ne rfl).elim
  · exact S.dis
  · exact S.dis.symm
  · exact (ne rfl).elim

theorem cross_far (far : 4≤G.dist a b) {i j : Bool} (ij : i≠j)
    {x y : V} (xi : x∈S.H i) (yj : y∈S.H j) (ax : G.Adj a x) (by' : G.Adj b y) :
    4≤G.dist x y := by
  have dis := S.disjoint_sides ij
  have crossing {u v : V} (w : G.Walk u v) (ui : u∈S.H i) (vi : v∉S.H i) :
      a∈w.support ∨ b∈w.support := by
    induction w with
    | nil => exact (vi ui).elim
    | @cons u z v uz w ih =>
      rcases S.closed i u ui z uz with rfl|rfl|zi
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih zi vi).imp (fun h => by simp [h]) (fun h => by simp [h])
  apply Nat.le_of_not_gt
  intro short
  obtain ⟨w,wl⟩ := S.con.exists_walk_length_eq_dist x y
  rcases crossing w xi (fun yi => disjoint_left.mp dis yi yj) with ha|hb
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp ha
    have lp : 1≤p.length := by
      have ne : x≠a := fun e => (S.off i).1 (e ▸ xi)
      have dp := G.dist_le p
      have pos : G.dist x a ≠ 0 := fun e => ne (S.con.dist_eq_zero_iff.mp e)
      omega
    have lq := G.dist_le (q.append (.cons by'.symm .nil))
    have lengths : w.length = p.length+q.length := by rw [eq,length_append]
    simp at lq
    omega
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp hb
    have lq : 1≤q.length := by
      have ne : b≠y := fun e => (S.off j).2 (e.symm ▸ yj)
      have dq := G.dist_le q
      have pos : G.dist b y ≠ 0 := fun e => ne (S.con.dist_eq_zero_iff.mp e)
      omega
    have lp := G.dist_le (.cons ax p)
    have lengths : w.length = p.length+q.length := by rw [eq,length_append]
    simp at lp
    omega

private theorem internal_d2 (far : 4≤G.dist a b) {i : Bool} {x : V}
    (xi : x∈S.H i) (ax : G.Adj a x) : ∃ y∈S.H i,y∈DistanceTwo G x := by
  obtain ⟨z,zi,bz⟩ := S.hitb i
  have no : ¬(x=z ∨ G.Adj x z) := by
    intro h
    rcases h with rfl|xz
    · have d := G.dist_le (Walk.cons ax (.cons bz.symm .nil))
      simp at d
      omega
    · have d := G.dist_le (Walk.cons ax (.cons xz (.cons bz.symm .nil)))
      simp at d
      omega
  by_cases ex : ∃ y∈S.H i,y∈DistanceTwo G x
  · exact ex
  exfalso
  obtain ⟨q,qs⟩ := S.joined i x xi z zi
  have prop {u v : V} (w : G.Walk u v) (ws : ∀ y∈w.support,y∈S.H i)
      (xu : x=u ∨ G.Adj x u) : x=v ∨ G.Adj x v := by
    induction w with
    | nil => exact xu
    | @cons u y v uy w ih =>
      apply ih (fun y hy => ws y (by simp [hy]))
      rcases xu with eq|xu
      · exact Or.inr (eq.symm ▸ uy)
      by_cases xy : x=y
      · exact Or.inl xy
      by_cases ad : G.Adj x y
      · exact Or.inr ad
      exact (ex ⟨y,ws y (by simp),Sides.mem_d2.mpr (Sides.dist_two S.con xy ad xu uy)⟩).elim
  exact no (prop q qs (Or.inl rfl))

private theorem a_port_cap (far : 4≤G.dist a b) (i : Bool) :
    (S.A i).card≤2 := by
  obtain ⟨x,xi,ax⟩ := S.hita (!i)
  obtain ⟨y,yi,by'⟩ := S.hitb i
  have ne : (!i)≠i := by cases i <;> decide
  have dis := S.disjoint_sides ne
  have xy := S.cross_far far ne xi yi ax by'
  have budget := distanceTwo_add_two_le_even_of_far S.con xy
  have cap := S.even x
  obtain ⟨z,zi,z2⟩ := S.internal_d2 far xi ax
  have zno : z∉S.A i := fun h => disjoint_left.mp dis zi (mem_filter.mp h).1
  have sub : insert z (S.A i) ⊆ DistanceTwo G x := by
    intro t ht
    rcases mem_insert.mp ht with rfl|th
    · exact z2
    obtain ⟨ti,at'⟩ := mem_filter.mp th
    have tout : t∉S.H (!i) := fun h => disjoint_left.mp dis h ti
    have xt : x≠t := fun e => tout (e ▸ xi)
    have no : ¬G.Adj x t := fun e => (S.closed (!i) x xi t e).elim
      (fun e => (S.off i).1 (e ▸ ti)) (fun h => h.elim (fun e => (S.off i).2 (e ▸ ti)) tout)
    exact Sides.mem_d2.mpr (Sides.dist_two S.con xt no ax.symm at')
  have s := card_le_card sub
  rw [card_insert_of_not_mem zno] at s
  omega

private theorem local_degree (_no : ¬G.Adj a b) {i : Bool} {x : V} (xi : x∈S.A i)
    (xb : ¬G.Adj x b) : G.degree x≤(S.A i).card+(S.D i).card := by
  obtain ⟨xh,ax⟩ := mem_filter.mp xi
  have sub : G.neighborFinset x ⊆ insert a ((S.A i).erase x ∪ S.D i) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xh y xy with rfl|rfl|yh
    · simp
    · exact (xb xy).elim
    · refine mem_insert.mpr (Or.inr (mem_union.mpr ?_))
      by_cases ay : G.Adj a y
      · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yh,ay⟩⟩)
      · right
        have ne : a≠y := fun e => (S.off i).1 (e.symm ▸ yh)
        exact mem_filter.mpr ⟨yh,Sides.mem_d2.mpr (Sides.dist_two S.con ne ay ax xy)⟩
  have c := card_le_card sub
  have c1 := card_insert_le a ((S.A i).erase x ∪ S.D i)
  have c2 := card_union_le ((S.A i).erase x) (S.D i)
  rw [card_neighborFinset_eq_degree] at c
  rw [card_erase_of_mem xi] at c2
  obtain ⟨x',xh,xedge⟩ := S.hita i
  have p := card_pos.mpr (show (S.A i).Nonempty from ⟨x',mem_filter.mpr ⟨xh,xedge⟩⟩)
  omega

include S

private theorem cut_close_of_a_high (high : 4≤G.degree a) : G.dist a b≤3 := by
  by_contra! far
  have no : ¬G.Adj a b := fun e => by have d := dist_eq_one_iff_adj.mpr e; omega
  have cover : G.neighborFinset a ⊆ S.A false ∪ S.A true := by
    intro x hx
    have ax := (mem_neighborFinset G a x).mp hx
    rcases S.all x with rfl|rfl|⟨i,ih⟩
    · exact (ax.ne rfl).elim
    · exact (no ax).elim
    cases i
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨ih,ax⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨ih,ax⟩))
  have cq := card_le_card cover
  rw [card_neighborFinset_eq_degree] at cq
  have ca := card_union_le (S.A false) (S.A true)
  have c0 := S.a_port_cap (by omega : 4≤G.dist a b) false
  have c1 := S.a_port_cap (by omega : 4≤G.dist a b) true
  have many (i : Bool) : 1<(S.A i).card := by cases i <;> omega
  have D (i : Bool) : 2≤(S.D i).card := by
    obtain ⟨x,xi,y,yi,xy⟩ := one_lt_card.mp (many i)
    have lo {v : V} (vi : v∈S.A i) (vh : 4≤G.degree v) : 2≤(S.D i).card := by
      have vb : ¬G.Adj v b := fun e => by
        have d := G.dist_le (Walk.cons (mem_filter.mp vi).2 (Walk.cons e .nil))
        simp at d
        omega
      have cb := S.local_degree no vi vb
      have ac := S.a_port_cap (by omega : 4≤G.dist a b) i
      omega
    exact (S.degree x y xy).elim (lo xi) (lo yi)
  have ds : Disjoint (S.D false) (S.D true) := S.dis.mono (filter_subset _ _) (filter_subset _ _)
  have sub : S.D false ∪ S.D true ⊆ DistanceTwo G a :=
    union_subset (fun _ h => (mem_filter.mp h).2) (fun _ h => (mem_filter.mp h).2)
  have sum := card_le_card sub
  rw [card_union_of_disjoint ds] at sum
  have lo0 := D false
  have lo1 := D true
  have d2 := distanceTwo_add_two_le_even_of_far S.con (show 4≤G.dist a b by omega)
  have cap := S.even a
  omega

/-- In the degree-four case, distinct vertices forming a two-cut are at
distance at most three. -/
theorem cut_distance : G.dist a b≤3 := by
  rcases S.degree a b S.ab with ah|bh
  · exact S.cut_close_of_a_high ah
  · rw [dist_comm]
    exact S.flip.cut_close_of_a_high bh

#print axioms cut_distance
end
end CutPair
end Graffiti189LongestPath.TwoCut
