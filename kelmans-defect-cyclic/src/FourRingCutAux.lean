import FourRingCutChoices

open Finset SimpleGraph
namespace KelmansCactus.FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def boundary (G : SimpleGraph V) (c : V→Bool) : Finset (V×V) := by
  classical
  exact univ.filter (fun e=>c e.1=true ∧ c e.2=false ∧ G.Adj e.1 e.2)

omit [DecidableEq V] in
theorem mem_boundary {G : SimpleGraph V} {c : V→Bool} {e : V×V} :
    e∈boundary G c ↔ c e.1=true ∧ c e.2=false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

def orientation (c : V→Bool) (x y : V) : V×V := if c x then (x,y) else (y,x)

omit [Fintype V] [DecidableEq V] in
theorem orientation_cases {c : V→Bool} {x y : V} :
    orientation c x y = (x,y) ∨ orientation c x y = (y,x) := by
  unfold orientation
  split <;> simp

omit [DecidableEq V] in
theorem active_edge {G : SimpleGraph V} {c : V→Bool} {x y : V}
    (m : c x≠c y) (adj : G.Adj x y) : orientation c x y∈boundary G c := by
  cases xC : c x <;> cases yC : c y
  · exact (m (xC.trans yC.symm)).elim
  · exact mem_boundary.mpr (by simp [orientation,xC,yC,adj.symm])
  · exact mem_boundary.mpr (by simp [orientation,xC,yC,adj])
  · exact (m (xC.trans yC.symm)).elim

def SmallTrivial (G : SimpleGraph V) : Prop :=
  ∀ c : V→Bool, (boundary G c).card≤3 →
    (∀ x y,c x=true → c y=true→x=y) ∨ (∀ x y,c x=false → c y=false→x=y)

theorem boundary_flip_card (G : SimpleGraph V) (c : V→Bool) :
    (boundary G (fun x=> !(c x))).card=(boundary G c).card := by
  classical
  have e : boundary G (fun x=> !(c x))=(boundary G c).image Prod.swap := by
    ext x
    constructor
    · intro h
      obtain ⟨a,b,d⟩ := mem_boundary.mp h
      have a' : c x.1=false := by
        change (!(c x.1))=true at a
        cases hx : c x.1 <;> simp_all
      have b' : c x.2=true := by
        change (!(c x.2))=false at b
        cases hx : c x.2 <;> simp_all
      exact mem_image.mpr ⟨x.swap,mem_boundary.mpr ⟨b',a',d.symm⟩,Prod.swap_swap _⟩
    · rintro h
      obtain ⟨y,ym,rfl⟩ := mem_image.mp h
      obtain ⟨a,b,d⟩ := mem_boundary.mp ym
      exact mem_boundary.mpr ⟨by simp [b],by simp [a],d.symm⟩
  rw [e,card_image_of_injective _ Prod.swap_injective]

theorem singleton_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→Bool) (x : V) (hx : c x=true)
    (uniq : ∀y,c y=true→y=x) :
    (boundary G c).card=G.degree x := by
  classical
  let e : V→V×V := fun v=>(x,v)
  have a : boundary G c=(G.neighborFinset x).image e := by
    ext z
    constructor
    · intro h
      obtain ⟨u,v⟩ := z
      obtain ⟨b0,_,e0⟩ := mem_boundary.mp h
      have ex : u=x := uniq u b0
      refine mem_image.mpr ⟨v,(mem_neighborFinset G x v).mpr (ex ▸ e0),?_⟩
      exact Prod.ext ex.symm rfl
    · intro h
      obtain ⟨v,vm,rfl⟩ := mem_image.mp h
      have ed := (mem_neighborFinset G x v).mp vm
      have other : c v=false := by
        by_cases vt : c v=true
        · exact (ed.ne (uniq _ vt).symm).elim
        · simpa using vt
      exact mem_boundary.mpr ⟨hx,other,ed⟩
  rw [a,card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e),card_neighborFinset_eq_degree]

theorem singleton_colour_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→Bool) (x : V) (uniq : ∀y,c y=c x→y=x) :
    (boundary G c).card=G.degree x := by
  cases hc : c x
  · have a : (!(c x))=true := by simp [hc]
    rw [←boundary_flip_card G c]
    exact singleton_boundary G _ x a (fun _ e=>uniq _ (by simpa [hc] using e))
  · exact singleton_boundary G c x hc (fun _ h=>uniq _ (h.trans hc.symm))

omit [Fintype V] [DecidableEq V] in
theorem bool_not_eq_of_distinct {a b : Bool} (h : a≠b) : a = !b := by
  cases a <;> cases b <;> simp_all

#print axioms singleton_colour_boundary
end
end KelmansCactus.FourRingCutAux
