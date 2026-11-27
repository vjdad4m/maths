import PortBudget180
import ComponentBalance180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [DecidableEq V]

/-- A path in the part joins opposite-colored neighbors of a. -/
def MixedAt (G : SimpleGraph V) (a : V) (C : Finset V) (c : V→Bool) : Prop :=
  ∃ x y,G.Adj a x ∧ G.Adj a y ∧ c x=true ∧ c y=false ∧ Joined G C x y

/-- A single retained tip closes an odd cycle inside this part exactly
when its two color classes of contacts are joined there. -/
theorem mixed_iff (G : SimpleGraph V) (a : V) (C : Finset V) (c : V→Bool)
    (out : a∉C) (cp : ProperOn G C c) : MixedAt G a C c ↔ ¬TwoColor G (insert a C) := by
  classical
  have dis : Disjoint C {a} := by simpa using out
  have shape : C∪{a}=insert a C := by ext x;simp [or_comm]
  have ext := extension_iff G C {a} c (fun _ => true) dis cp
    (fun i im j jm ed => (ed.ne ((mem_singleton.mp im).trans (mem_singleton.mp jm).symm)).elim)
  rw [one_compatible] at ext
  constructor
  · rintro ⟨x,y,ax,ay,cx,cy,join⟩ bi
    obtain ⟨e,ok⟩ := (color_function ..).mp bi
    have paint : ∃ d,ProperOn G (C∪{a}) d ∧ ∀ t∈({a}:Finset V),d t=true := by
      refine ⟨fun v => e v == e a,?_,?_⟩
      · rw [shape];intro v vm w wm ed
        have ne := ok v vm w wm ed
        cases j : e v <;> cases k : e w <;> cases h : e a <;> simp_all
      · intro t tm;rw [mem_singleton.mp tm];simp
    exact ext.mp paint x y ax ay cx cy join
  · intro non
    by_contra! none
    apply non
    apply (color_function ..).mpr
    obtain ⟨e,ok,_⟩ := ext.mpr (fun x y ax ay cx cy path => none ⟨x,y,ax,ay,cx,cy,path⟩)
    exact ⟨e,shape ▸ ok⟩

/-- Normalized colors at the two terminals. -/
def TerminalColor (G : SimpleGraph V) (a b : V) (C : Finset V) (t : Bool) : Prop :=
  ∃ e,ProperOn G (({a,b}:Finset V)∪C) e ∧ e a=true ∧ e b=t

theorem terminal_restrict (G : SimpleGraph V) {a b : V} {C D : Finset V} {t : Bool}
    (sub : C⊆D) (h : TerminalColor G a b D t) : TerminalColor G a b C t := by
  obtain ⟨e,ok,aa,bb⟩ := h
  exact ⟨e,fun x xm y ym => ok x (union_subset_union (Subset.rfl) sub xm) y (union_subset_union (Subset.rfl) sub ym),aa,bb⟩

/-- Each side may choose its coloring independently once the relative
color of the two terminals is fixed. -/
theorem terminal_union (G : SimpleGraph V) (a b : V) (C D : Finset V) (t : Bool)
    (dis : Disjoint C D) (cross : ∀ x∈C,∀ y∈D,¬G.Adj x y) :
    TerminalColor G a b (C∪D) t ↔ TerminalColor G a b C t ∧ TerminalColor G a b D t := by
  classical
  constructor
  · intro ok
    exact ⟨terminal_restrict G subset_union_left ok,terminal_restrict G subset_union_right ok⟩
  · rintro ⟨⟨e,ep,ea,eb⟩,⟨f,fp,fa,fb⟩⟩
    let X : Finset V := {a,b}
    let h (x : V) := if x∈C then e x else f x
    have agree (x : V) (xm : x∈X) : e x=f x := by
      rcases mem_insert.mp xm with eq|mem
      · exact eq ▸ ea.trans fa.symm
      · exact (mem_singleton.mp mem) ▸ eb.trans fb.symm
    have left (x : V) (xm : x∈X∪C) : h x=e x := by
      by_cases xc : x∈C
      · simp [h,xc]
      · simp [h,xc,agree x ((mem_union.mp xm).resolve_right xc)]
    have right (x : V) (xm : x∈X∪D) : h x=f x := by
      by_cases xc : x∈C
      · have xx := (mem_union.mp xm).resolve_right (disjoint_left.mp dis xc)
        simp [h,xc,agree x xx]
      · simp [h,xc]
    refine ⟨h,?_,(left a (mem_union_left _ (mem_insert_self ..))).trans ea,
      (left b (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))).trans eb⟩
    intro x xm y ym ed
    have classify (z : V) (zm : z∈X∪(C∪D)) : z∈X ∨ z∈C ∨ z∈D := by simpa only [mem_union] using zm
    rcases classify x xm with xh|xh|xh <;> rcases classify y ym with yh|yh|yh
    all_goals first
      | exact (cross x xh y yh ed).elim
      | exact (cross y yh x xh ed.symm).elim
      | (have hx : x∈X∪C := by first | exact mem_union_left _ xh | exact mem_union_right _ xh
         have hy : y∈X∪C := by first | exact mem_union_left _ yh | exact mem_union_right _ yh
         rw [left x hx,left y hy];exact ep x hx y hy ed)
      | (have hx : x∈X∪D := by first | exact mem_union_left _ xh | exact mem_union_right _ xh
         have hy : y∈X∪D := by first | exact mem_union_left _ yh | exact mem_union_right _ yh
         rw [right x hx,right y hy];exact fp x hx y hy ed)

#print axioms mixed_iff
#print axioms terminal_union
end Minimal180.PairRepair
