import PathMaximum180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [DecidableEq V]

def ProperOn (J : SimpleGraph V) (S : Finset V) (c : V→Bool) : Prop :=
  ∀ x∈S, ∀ y∈S, J.Adj x y → c x≠c y

theorem color_function (J : SimpleGraph V) (S : Finset V) : TwoColor J S ↔ ∃ c, ProperOn J S c := by
  classical
  constructor
  · rintro ⟨C,D,dis,rfl,ci,di⟩
    refine ⟨fun x => decide (x∈C),?_⟩
    intro x hx y hy e eq
    by_cases a : x∈C
    · have b : y∈C := by simpa [a] using eq
      exact ci x a y b e.ne e
    · have b : y∉C := by simpa [a] using eq
      exact di x ((mem_union.mp hx).resolve_left a) y ((mem_union.mp hy).resolve_left b) e.ne e
  · rintro ⟨c,good⟩
    let C := S.filter (fun x => c x=true)
    let D := S.filter (fun x => c x=false)
    refine ⟨C,D,disjoint_left.mpr (fun _ h k => Bool.noConfusion ((mem_filter.mp h).2.symm.trans (mem_filter.mp k).2)),?_,?_,?_⟩
    · ext x; cases h : c x <;> simp [C,D,h]
    all_goals
      intro x hx y hy _ e
      exact good x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 e ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)

noncomputable def within (J : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := J.Adj x y ∧ x∈S ∧ y∈S
  symm _ _ h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless _ h := h.1.ne rfl

omit [DecidableEq V] in
private theorem add_proper (J : SimpleGraph V) (S : Finset V) (c : V→Bool) (hc : ProperOn J S c)
    (u v : V) (ok : u∈S → v∈S → c u≠c v) : ProperOn (J⊔SimpleGraph.edge u v) S c := by
  intro x hx y hy edge
  rcases edge with e|e
  · exact hc x hx y hy e
  rcases (edge_adj ..).mp e with ⟨(⟨rfl,rfl⟩|⟨rfl,rfl⟩),_⟩
  · exact ok hx hy
  · exact (ok hy hx).symm

/-- On any old witness whose specified ends have equal color, preserving both
ends after adding their edge is equivalent to disconnecting them in the retained set. -/
theorem anchored_iff_cut (J : SimpleGraph V) (X : Finset V) (u v : V) (uv : u≠v)
    (ux : u∈X) (vx : v∈X) (c : V→Bool) (hc : ProperOn J X c) (same : c u=c v) :
    TwoColor (J⊔SimpleGraph.edge u v) X ↔ ¬(within J X).Reachable u v := by
  classical
  constructor
  · rintro col ⟨path⟩
    obtain ⟨d,hd⟩ := (color_function _ _).mp col
    have diff := hd u ux v vx (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩))
    have parity {a b : V} (p : (within J X).Walk a b) : (c a=d a ↔ c b=d b) := by
      induction p with
      | nil => rfl
      | @cons i j k ij _ ih =>
        have x := hc i ij.2.1 j ij.2.2 ij.1
        have y := hd i ij.2.1 j ij.2.2 (Or.inl ij.1)
        apply Iff.trans _ ih
        revert x y
        cases c i <;> cases d i <;> cases c j <;> cases d j <;> decide
    have equ := parity path
    rw [same] at equ
    revert equ diff
    cases c v <;> cases d u <;> cases d v <;> decide
  · intro sep
    let f (x : V) := if (within J X).Reachable u x then !(c x) else c x
    have good : ProperOn J X f := by
      intro x hx y hy e
      have h : (within J X).Adj x y := ⟨e,hx,hy⟩
      have equiv : (within J X).Reachable u x ↔ (within J X).Reachable u y :=
        ⟨fun p => p.trans h.reachable,fun p => p.trans h.symm.reachable⟩
      have ne := hc x hx y hy e
      by_cases reached : (within J X).Reachable u y <;> simp [f,equiv,reached,ne]
    apply (color_function _ _).mpr
    refine ⟨f,add_proper J X f good u v (fun _ _ => ?_)⟩
    simp [f,Reachable.refl,sep,same]

variable [Fintype V]

/-- A strict rank drop pins both ends in every maximum lower coloring.
They have the same color and are connected inside that witness. -/
theorem rank_forces_route (J : SimpleGraph V) (u v : V) (uv : u≠v)
    (drop : bipartiteNum (J⊔SimpleGraph.edge u v)<bipartiteNum J)
    (S : Finset V) (top : MaxSet J S) (c : V→Bool) (hc : ProperOn J S c) :
    u∈S ∧ v∈S ∧ c u=c v ∧ (within J S).Reachable u v := by
  classical
  have no : ¬TwoColor (J⊔SimpleGraph.edge u v) S := fun old => by
    have := size_bip _ old; have := top.2; omega
  have cannot : ¬(u∈S → v∈S → c u≠c v) :=
    fun ok => no ((color_function _ _).mpr ⟨c,add_proper J S c hc u v ok⟩)
  push_neg at cannot
  obtain ⟨us,vs,eq⟩ := cannot
  exact ⟨us,vs,eq,Classical.byContradiction (fun cut => no ((anchored_iff_cut J S u v uv us vs c hc eq).mpr cut))⟩

/-- The universal monochromatic endpoint condition characterizes the strict drop. -/
theorem rank_lock_iff (J : SimpleGraph V) (u v : V) (uv : u≠v) :
    bipartiteNum (J⊔SimpleGraph.edge u v)<bipartiteNum J ↔
    ∀ S, MaxSet J S → ∀ c, ProperOn J S c → u∈S ∧ v∈S ∧ c u=c v := by
  constructor
  · intro drop S h c good
    obtain ⟨a,b,d,_⟩ := rank_forces_route J u v uv drop S h c good
    exact ⟨a,b,d⟩
  · intro locked
    by_contra! no
    let G := J⊔SimpleGraph.edge u v
    obtain ⟨S,col,eq⟩ := optB G
    obtain ⟨c,good⟩ := (color_function G S).mp col
    have old : ProperOn J S c := fun x hx y hy e => good x hx y hy (Or.inl e)
    have oldCol := (color_function J S).mpr ⟨c,old⟩
    have maxS : MaxSet J S := ⟨oldCol,le_antisymm (size_bip J oldCol) (no.trans_eq eq.symm)⟩
    obtain ⟨us,vs,same⟩ := locked S maxS c old
    exact good u us v vs (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩)) same

/-- Restrict any maximum lower witness to a set still containing the ends.
The chord can be added on the restriction precisely when that restriction separates them. -/
theorem maximum_restriction_iff_cut (J : SimpleGraph V) (u v : V) (uv : u≠v)
    (drop : bipartiteNum (J⊔SimpleGraph.edge u v)<bipartiteNum J)
    (S : Finset V) (top : MaxSet J S) (X : Finset V) (xs : X⊆S) (ux : u∈X) (vx : v∈X) :
    TwoColor (J⊔SimpleGraph.edge u v) X ↔ ¬(within J X).Reachable u v := by
  obtain ⟨c,good⟩ := (color_function J S).mp top.1
  have same := (rank_forces_route J u v uv drop S top c good).2.2.1
  exact anchored_iff_cut J X u v uv ux vx c (fun x hx y hy => good x (xs hx) y (xs hy)) same

#print axioms rank_lock_iff
#print axioms maximum_restriction_iff_cut
#print axioms anchored_iff_cut
#print axioms rank_forces_route
end Minimal180
