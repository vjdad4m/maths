import PairSeparator180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [DecidableEq V]

/-- Fix all retained neighbors of the center to false. Every surviving
component outside the closed neighborhood may choose its own flip. -/
def PortsFit (G : SimpleGraph V) (S H : Finset V) (c : V→Bool) : Prop :=
  Indep G H ∧ Compatible G S H c (fun _ => false)

private theorem true_normalize {x y z : Bool} (h : x≠y) : (x==z)≠(y==z) := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Once the center is kept, all its surviving neighbors have a common
color. The remaining constraints are exactly component flip constraints. -/
theorem ports_iff (G : SimpleGraph V) (a : V) (S H : Finset V) (c : V→Bool)
    (outside : ∀ x∈S,¬G.Adj a x) (ports : ∀ x∈H,G.Adj a x) (cp : ProperOn G S c) :
    TwoColor G (insert a (S∪H)) ↔ PortsFit G S H c := by
  classical
  have dis : Disjoint S H := disjoint_left.mpr (fun x xs xh => outside x xs (ports x xh))
  constructor
  · intro bi
    obtain ⟨e,proper⟩ := (color_function ..).mp bi
    let d (x : V) := e x == e a
    have norm : ProperOn G (insert a (S∪H)) d := fun x xm y ym ed => true_normalize (proper x xm y ym ed)
    have dn (x : V) (xh : x∈H) : d x=false := by
      have unlike := proper a (mem_insert_self ..) x (mem_insert_of_mem (mem_union_right _ xh)) (ports x xh)
      cases ea : e a <;> cases ex : e x <;> simp_all [d]
    have ind : Indep G H := by
      intro x xh y yh _ ed
      exact norm x (mem_insert_of_mem (mem_union_right _ xh)) y (mem_insert_of_mem (mem_union_right _ yh))
        ed ((dn x xh).trans (dn y yh).symm)
    refine ⟨ind,(extension_iff G S H c (fun _ => false) dis cp
      (fun x xm y ym ed => (ind x xm y ym ed.ne ed).elim)).mp ?_⟩
    exact ⟨d,fun x xm y ym => norm x (mem_insert_of_mem xm) y (mem_insert_of_mem ym),dn⟩
  · rintro ⟨ind,fit⟩
    obtain ⟨e,ok,agree⟩ := (extension_iff G S H c (fun _ => false) dis cp
      (fun x xm y ym ed => (ind x xm y ym ed.ne ed).elim)).mpr fit
    let d (x : V) := if x=a then true else e x
    have away (x : V) (xm : x∈S∪H) (ed : G.Adj a x) : d x=false := by
      have h := (mem_union.mp xm).resolve_left (fun xs => outside x xs ed)
      simp [d,ed.ne.symm,agree x h]
    apply (color_function ..).mpr
    refine ⟨d,fun x xm y ym ed => ?_⟩
    by_cases xa : x=a
    · subst x
      have ys := (mem_insert.mp ym).resolve_left ed.ne.symm
      simp [d,show e y=false by simpa [d,ed.ne.symm] using away y ys ed,ed.ne.symm]
    by_cases ya : y=a
    · subst y
      have xs := (mem_insert.mp xm).resolve_left xa
      simp [d,show e x=false by simpa [d,xa] using away x xs ed.symm,xa]
    exact (show d x=e x by simp [d,xa]).symm ▸ (show d y=e y by simp [d,ya]).symm ▸
      ok x ((mem_insert.mp xm).resolve_left xa) y ((mem_insert.mp ym).resolve_left ya) ed

/-- All component and adjacency obstructions have one or two ports as
witnesses. The diagonal tests are required even for a single port. -/
theorem ports_pairwise (G : SimpleGraph V) (S H : Finset V) (c : V→Bool) :
    PortsFit G S H c ↔ ∀ u∈H,∀ v∈H,PortsFit G S {u,v} c := by
  classical
  constructor
  · rintro ⟨ind,fit⟩ u uh v vh
    have sub : ({u,v}:Finset V)⊆H := insert_subset uh (singleton_subset_iff.mpr vh)
    exact ⟨fun x xm y ym => ind x (sub xm) y (sub ym),
      fun x y ⟨i,im,ix,on⟩ ⟨j,jm,jy,off⟩ => fit x y ⟨i,sub im,ix,on⟩ ⟨j,sub jm,jy,off⟩⟩
  · intro all
    constructor
    · intro x xh y yh
      exact (all x xh y yh).1 x (mem_insert_self ..) y (mem_insert_of_mem (mem_singleton_self _))
    · rintro x y ⟨i,im,ix,on⟩ ⟨j,jm,jy,off⟩
      exact (all i im j jm).2 x y ⟨i,mem_insert_self ..,ix,on⟩
        ⟨j,mem_insert_of_mem (mem_singleton_self _),jy,off⟩

#print axioms ports_iff
#print axioms ports_pairwise
end Minimal180.PairRepair
