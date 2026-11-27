import Mathlib.SetTheory.Cardinal.Finite
import SmallSeparator189
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
namespace Graffiti189LongestPath.FourCut
open SimpleGraph Finset
open Graffiti189LongestPath
variable {V : Type*} [Finite V] {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

/-- No two-vertex cut has four components meeting the neighborhood of the
first discarded vertex, under the order-four Graffiti.pc #189 bounds. -/
theorem no_four_sides (hc : G.Connected) (a b : V)
    (d2 : ∀ x, (DistanceTwo G x).card≤4)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (H : Fin 4 → Finset V)
    (hdis : ∀ i j, i≠j → Disjoint (H i) (H j))
    (hoff : ∀ i, a∉H i ∧ b∉H i)
    (hclosed : ∀ i, ∀ x∈H i, ∀ y, G.Adj x y → y=a ∨ y=b ∨ y∈H i)
    (hit : ∀ i, ∃ x∈H i, G.Adj a x) : False := by
  classical
  let A (i : Fin 4) := (H i).filter (G.Adj a)
  let D (i : Fin 4) := (H i).filter (fun x => x∈DistanceTwo G a)
  have apos (i : Fin 4) : 1≤(A i).card := by
    obtain ⟨x,xh,ax⟩ := hit i
    exact card_pos.mpr ⟨x,mem_filter.mpr ⟨xh,ax⟩⟩
  have Adis (i j) (ij : i≠j) : Disjoint (A i) (A j) :=
    (hdis i j ij).mono (filter_subset _ _) (filter_subset _ _)
  have Ddis (i j) (ij : i≠j) : Disjoint (D i) (D j) :=
    (hdis i j ij).mono (filter_subset _ _) (filter_subset _ _)
  have add (i j k l : Fin 4) (ij : i≠j) (ik : i≠k) (il : i≠l)
      (jk : j≠k) (jl : j≠l) (kl : k≠l) :
      (A j).card+(A k).card+(A l).card≤4 := by
    obtain ⟨x,xi,ax⟩ := hit i
    have belong (t : Fin 4) (it : i≠t) : A t ⊆ DistanceTwo G x := by
      intro y hy
      obtain ⟨yt,ay⟩ := mem_filter.mp hy
      have ny : y∉H i := fun e => disjoint_left.mp (hdis i t it) e yt
      have xy : x≠y := fun e => ny (e ▸ xi)
      have na : ¬G.Adj x y := fun adj =>
        (hclosed i x xi y adj).elim (fun e => (hoff t).1 (e ▸ yt))
          (fun rest => rest.elim (fun e => (hoff t).2 (e ▸ yt)) ny)
      have ge := hc.one_lt_dist_of_ne_of_not_adj xy na
      have le := G.dist_le (Walk.cons ax.symm (Walk.cons ay .nil))
      simp at le
      simp [DistanceTwo, show G.dist x y=2 by omega]
    have sub : A j ∪ A k ∪ A l ⊆ DistanceTwo G x :=
      union_subset (union_subset (belong j ij) (belong k ik)) (belong l il)
    have dis : Disjoint (A j ∪ A k) (A l) := disjoint_union_left.mpr ⟨Adis j l jl,Adis k l kl⟩
    have ca := card_le_card sub
    rw [card_union_of_disjoint dis,card_union_of_disjoint (Adis j k jk)] at ca
    have cap := d2 x
    omega
  have b0 := add 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b1 := add 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b2 := add 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b3 := add 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have high_lower (i : Fin 4) (x : V) (hx : x∈A i) (dx : 4≤G.degree x) :
      3≤(A i).card+(D i).card := by
    obtain ⟨xi,ax⟩ := mem_filter.mp hx
    have sub : G.neighborFinset x ⊆ insert a (insert b ((A i).erase x ∪ D i)) := by
      intro y hy
      have xy := (mem_neighborFinset G x y).mp hy
      rcases hclosed i x xi y xy with rfl|rfl|yi
      · simp
      · simp
      · refine mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr (mem_union.mpr ?_))))
        by_cases ay : G.Adj a y
        · exact Or.inl (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yi,ay⟩⟩)
        · right
          have az : a≠y := fun e => (hoff i).1 (e.symm ▸ yi)
          have ge := hc.one_lt_dist_of_ne_of_not_adj az ay
          have le := G.dist_le (Walk.cons ax (Walk.cons xy .nil))
          simp at le
          exact mem_filter.mpr ⟨yi, by simp [DistanceTwo,show G.dist a y=2 by omega]⟩
    have c := card_le_card sub
    have c1 := card_insert_le a (insert b ((A i).erase x ∪ D i))
    have c2 := card_insert_le b ((A i).erase x ∪ D i)
    have c3 := card_union_le ((A i).erase x) (D i)
    rw [card_erase_of_mem hx] at c3
    rw [card_neighborFinset_eq_degree] at c
    have n := apos i
    omega
  have pair (i j : Fin 4) (ij : i≠j) :
      3≤(A i).card+(D i).card ∨ 3≤(A j).card+(D j).card := by
    obtain ⟨x,xh,ax⟩ := hit i
    obtain ⟨y,yh,ay⟩ := hit j
    have ne : x≠y := fun e => disjoint_left.mp (hdis i j ij) xh (e.symm ▸ yh)
    exact (degree x y ne).imp (high_lower i x (mem_filter.mpr ⟨xh,ax⟩))
      (high_lower j y (mem_filter.mpr ⟨yh,ay⟩))
  have c01 := pair 0 1 (by decide)
  have c02 := pair 0 2 (by decide)
  have c03 := pair 0 3 (by decide)
  have c12 := pair 1 2 (by decide)
  have c13 := pair 1 3 (by decide)
  have c23 := pair 2 3 (by decide)
  have sumD : (D 0).card+(D 1).card+(D 2).card+(D 3).card≤4 := by
    have sub (i : Fin 4) : D i ⊆ DistanceTwo G a := fun _ hx => (mem_filter.mp hx).2
    have de := card_le_card (union_subset (union_subset (union_subset (sub 0) (sub 1)) (sub 2)) (sub 3))
    rw [card_union_of_disjoint (disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨Ddis 0 3 (by decide),Ddis 1 3 (by decide)⟩,Ddis 2 3 (by decide)⟩),
        card_union_of_disjoint (disjoint_union_left.mpr ⟨Ddis 0 2 (by decide),Ddis 1 2 (by decide)⟩),
        card_union_of_disjoint (Ddis 0 1 (by decide))] at de
    exact de.trans (d2 a)
  have p0 := apos 0
  have p1 := apos 1
  have p2 := apos 2
  have p3 := apos 3
  omega

#print axioms no_four_sides

/-- At most three connected components remain after deleting any two vertices. -/
theorem component_card_le_three (hc : G.Connected) (a b : V) (ab : a≠b)
    (d2 : ∀ x, (DistanceTwo G x).card≤4)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del_b : (G.induce {x : V | x≠b}).Connected) :
    Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent ≤ 3 := by
  classical
  let J := G.induce {x : V | x≠a ∧ x≠b}
  by_contra excess
  have card := Nat.not_le.mp excess
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card (Fin 4) ≤ Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card]
    exact card
  obtain ⟨C⟩ := Function.Embedding.nonempty_of_card_le n
  let H (i : Fin 4) : Finset V := Finset.univ.filter (fun x =>
    ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i)
  have mem {i : Fin 4} {x : V} : x∈H i ↔
      ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i := by simp [H]
  have ds (i j : Fin 4) (ij : i≠j) : Disjoint (H i) (H j) := by
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨hx,hi⟩ := mem.mp xi
    obtain ⟨_,hj⟩ := mem.mp xj
    exact ij (C.injective (hi.symm.trans hj))
  have off (i : Fin 4) : a∉H i ∧ b∉H i :=
    ⟨fun ha => (mem.mp ha).choose.1 rfl,fun hb => (mem.mp hb).choose.2 rfl⟩
  have closed (i : Fin 4) (x : V) (hx : x∈H i) (y : V) (xy : G.Adj x y) :
      y=a ∨ y=b ∨ y∈H i := by
    by_cases ya : y=a
    · exact Or.inl ya
    by_cases yb : y=b
    · exact Or.inr (Or.inl yb)
    obtain ⟨hx',hx''⟩ := mem.mp hx
    have edge : J.Adj ⟨x,hx'⟩ ⟨y,⟨ya,yb⟩⟩ := xy
    exact Or.inr (Or.inr (mem.mpr ⟨⟨ya,yb⟩,(ConnectedComponent.sound ⟨Walk.cons edge Walk.nil⟩).symm.trans hx''⟩))
  apply no_four_sides hc a b d2 degree H ds off closed
  intro i
  obtain ⟨x,hx⟩ := (C i).exists_rep
  have xi : (x : V)∈H i := mem.mpr ⟨x.property,hx⟩
  by_cases nhit : ∃ x∈H i,G.Adj a x
  · exact nhit
  exfalso
  let K := G.induce {x : V | x≠b}
  let x' : {x : V // x∈{x : V | x≠b}} := ⟨x.val,x.property.2⟩
  let a' : {x : V // x∈{x : V | x≠b}} := ⟨a,ab⟩
  have r : K.Reachable x' a' := del_b x' a'
  obtain ⟨w⟩ := r
  have stay {u v : {x : V // x∈{x : V | x≠b}}} (q : K.Walk u v)
      (hu : (u : V) ∈ H i) : (v : V) ∈ H i := by
    induction q with
    | nil => exact hu
    | @cons u v w uv q ih =>
      apply ih
      have uv' : G.Adj u.val v.val := uv
      rcases closed i u.val hu v.val uv' with va|vb|vv
      · exact (nhit ⟨u.val,hu,by simpa only [va] using uv'.symm⟩).elim
      · exact (v.property vb).elim
      · exact vv
  exact (off i).1 (stay w xi)

#print axioms component_card_le_three
end Graffiti189LongestPath.FourCut
