import ForcedParents180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every designated source of a parent edge into the unmarked set
provides one unit in addition to the full branching at a. -/
theorem forced_credit (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a t : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (F : Finset V) (sources : ∀ x∈F,x≠r ∧ ¬G.Adj a x ∧ x≠a ∧ G.Adj x t)
    (levels : ∀ x∈F,G.dist t r≤G.dist x r ∨
      (G.Adj a t ∧ G.dist t r=G.dist a r ∧ G.dist t r≤G.dist x r+1))
    (free : ∀ x∈F,x∉A∩parity G r p) (outside : t∉A∪parity G r p) :
    F.card+(G.degree a-2)≤allowance G r p A := by
  classical
  obtain ⟨T,q,k,sub,tree,down,take,deg,pres,pay⟩ :=
    star_parents G gc r a t ar p A ai am F sources levels (fun _ _ _ => outside)
  have cost := parent_gain G T gc hn sub tree r p A ai q k down take pay F (fun x m =>
    ⟨(sources x m).1,free x m,pres x m ▸ outside⟩)
  have aa : a∈(A∪parity G r p).erase r := mem_erase.mpr ⟨ar,mem_union_left _ am⟩
  have br := single_le_sum (f:=fun x => T.degree x-2) (fun x _ => Nat.zero_le _) aa
  change T.degree a-2≤∑ v ∈ (A ∪ parity G r p).erase r, (T.degree v-2) at br
  rw [← deg];exact le_trans (Nat.add_le_add_left br _) cost

/-- Outside the star of a saturated vertex every same-parity predecessor
test forbids a non-double child with an unmarked parent. -/
theorem no_extra_parent (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a x y : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (sat : G.degree a=allowance G r p A+2) (xr : x≠r) (na : ¬G.Adj a x) (xa : x≠a)
    (ed : G.Adj x y) (le : G.dist y r≤G.dist x r) (free : x∉A∩parity G r p) : y∈A∪parity G r p := by
  by_contra no
  have cost := forced_credit G gc hn r a y ar p A ai am {x}
    (fun z m => (mem_singleton.mp m) ▸ ⟨xr,na,xa,ed⟩)
    (fun z m => (mem_singleton.mp m) ▸ Or.inl le)
    (fun z m => (mem_singleton.mp m) ▸ free) no
  rw [card_singleton] at cost;omega

omit [DecidableEq V] in
theorem eq_dist (G : SimpleGraph V) (gc : G.Connected) (r x y : V) (p : Bool) (ed : G.Adj x y)
    (same : x∈parity G r p ↔ y∈parity G r p) : G.dist x r=G.dist y r := by
  have u := gc.dist_triangle (u:=x) (v:=y) (w:=r)
  have v := gc.dist_triangle (u:=y) (v:=x) (w:=r)
  rw [dist_eq_one_iff_adj.mpr ed] at u
  rw [dist_eq_one_iff_adj.mpr ed.symm] at v
  simp only [mem_parity] at same
  cases p <;> simp only [Bool.toNat_false,Bool.toNat_true] at same <;> omega

/-- Under saturation all edges within the opposite parity have both
endpoints in the neighborhood of a. The independent mark need not lie
in a single parity. -/
theorem opposite_edges_confined (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) {x y : V} (ed : G.Adj x y)
    (xp : x∉parity G r p) (yp : y∉parity G r p) : G.Adj a x ∧ G.Adj a y := by
  classical
  have d := eq_dist G gc r x y p ed (iff_of_false xp yp)
  have force {u v : V} (uv : G.Adj u v) (up : u∉parity G r p) (vp : v∉parity G r p)
      (eq : G.dist u r=G.dist v r) (va : v∉A) : G.Adj a u := by
    by_contra no
    have ur : u≠r := by
      intro same;subst u
      have pos := gc.pos_dist_of_ne uv.ne.symm
      rw [dist_self] at eq;omega
    have ua : u≠a := fun same => up (same ▸ ap)
    have yes := no_extra_parent G gc hn r a u v ar p A ai am sat ur no ua uv eq.ge
      (fun m => up (mem_inter.mp m).2)
    exact (mem_union.mp yes).elim va vp
  have ax : x∉A := by
    intro xm
    have ay : y∉A := fun ym => ai x xm y ym ed.ne ed
    have adj := force ed xp yp d ay
    exact ai a am x xm adj.ne adj
  have ay : y∉A := by
    intro ym
    have adj := force ed.symm yp xp d.symm ax
    exact ai a am y ym adj.ne adj
  exact ⟨force ed xp yp d ay,force ed.symm yp xp d.symm ax⟩

/-- Each shortest-path predecessor of a nonroot, unmarked vertex in the
selected parity outside the full star is in the independent marking. -/
theorem outside_predecessors_marked (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (sat : G.degree a=allowance G r p A+2) {x y : V} (xr : x≠r) (na : ¬G.Adj a x)
    (xp : x∈parity G r p) (out : x∉A) (ed : G.Adj x y) (d : G.dist x r=G.dist y r+1) : y∈A := by
  have marked := no_extra_parent G gc hn r a x y ar p A ai am sat xr na (fun eq => out (eq ▸ am)) ed
    (by omega) (fun m => out (mem_inter.mp m).1)
  exact (mem_union.mp marked).resolve_right (fun yp => by
    have eq := eq_dist G gc r x y p ed (iff_of_true xp yp);omega)

/-- When A lies in the selected parity, its only unmarked vertices
there are the root and actual neighbors of the saturated center. -/
theorem parity_covered (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (sat : G.degree a=allowance G r p A+2) (sub : A⊆parity G r p) {x : V}
    (xp : x∈parity G r p) (xr : x≠r) (out : x∉A) : G.Adj a x := by
  by_contra no
  obtain ⟨y,ed,d⟩ := Graffiti169.exists_predecessor G gc r x xr
  have yp := sub (outside_predecessors_marked G gc hn r a ar p A ai am sat xr no xp out ed d)
  have eq := eq_dist G gc r x y p ed (iff_of_true xp yp);omega

#print axioms forced_credit
#print axioms no_extra_parent
#print axioms opposite_edges_confined
#print axioms outside_predecessors_marked
#print axioms parity_covered
end Minimal180.OppositeGain
