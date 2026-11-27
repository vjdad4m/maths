import RemoteT2FourCutMatching
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteFourCutAttachment
open SquareCap (Port boundary attach SmallTrivial)
open RemoteT2FourCutMatching (ColorThree no_repeated_endpoint_of_four_cut)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Side (c : V→Bool) (b : Bool) := {v : V // c v=b}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
abbrev sideGraph (c : V→Bool) (b : Bool) : SimpleGraph (Side c b) :=
  G.induce {v : V | c v=b}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
noncomputable def splitMap (c : V→Bool) (b : Bool) : Side c b ⊕ Side c (!b) ≃ V := by
  classical
  apply Equiv.ofBijective (Sum.elim Subtype.val Subtype.val)
  constructor
  · rintro (u|u) (v|v) e
    · exact congrArg Sum.inl (Subtype.ext e)
    · have uv : u.val=v.val := e
      have h := u.property.symm.trans ((congrArg c uv).trans v.property)
      cases b <;> contradiction
    · have uv : u.val=v.val := e
      have h := v.property.symm.trans ((congrArg c uv.symm).trans u.property)
      cases b <;> contradiction
    · exact congrArg Sum.inr (Subtype.ext e)
  · intro v
    cases h : c v <;> cases b
    · exact ⟨Sum.inl ⟨v,h⟩,rfl⟩
    · exact ⟨Sum.inr ⟨v,h⟩,rfl⟩
    · exact ⟨Sum.inr ⟨v,h⟩,rfl⟩
    · exact ⟨Sum.inl ⟨v,h⟩,rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem boundary_mem {c : V→Bool} {a b : V} :
    (a,b)∈boundary G c ↔ c a=true∧c b=false∧G.Adj a b := by
  classical
  simp [boundary]

/-- An actual width-four cut between two non-tiny shores of a cubic
cyclic-four graph has the exact four-port attachment representation.
The ports are chosen from the cut's four distinct edges; every
crossing edge is represented by a port. -/
theorem true_shore_attachment (c : V→Bool) (small : SmallTrivial G)
    (cub : ∀ v,G.degree v=3) (pos : ColorThree c true) (neg : ColorThree c false)
    (w : (boundary G c).card=4) :
    ∃ p : Port↪Side c true, ∃ r : Port→Side c false,
      (∀ a : Side c true,∀ b : Side c false,G.Adj a.val b.val → ∃ i : Port,p i=a ∧ r i=b) ∧
      ∃ e : (attach (sideGraph G c true) (sideGraph G c false) p r) ≃g G,
        (∀ a : Side c true,e (Sum.inl a)=a.val) ∧
        (∀ b : Side c false,e (Sum.inr b)=b.val) := by
  classical
  let P := {e : V×V // e∈boundary G c}
  have pcard : Fintype.card P=4 := by
    let e0 := Fintype.subtype_card (boundary G c) (fun _=>Iff.rfl)
    have e : Fintype.card P=(boundary G c).card := by
      letI : Fintype P := inferInstance
      have fq := Subsingleton.elim (Fintype.subtype (boundary G c) (fun _=>Iff.rfl))
        (inferInstance : Fintype P)
      rw [fq] at e0
      exact e0
    exact e.trans w
  have portcard : Fintype.card Port=4 := by simp [SquareCap.Port]
  let en : Port ≃ P := Fintype.equivOfCardEq (portcard.trans pcard.symm)
  have m (a : P) : c a.val.1=true∧c a.val.2=false∧G.Adj a.val.1 a.val.2 := by
    exact (boundary_mem G).mp a.property
  let f : Port→Side c true := fun i=>⟨(en i).val.1,(m (en i)).1⟩
  have inj : Function.Injective f := by
    intro i j h
    have eq : (en i).val.1=(en j).val.1 := congrArg Subtype.val h
    have e2 := no_repeated_endpoint_of_four_cut G small cub c pos neg w.le
      (m (en i)).2.2 (eq.symm ▸ (m (en j)).2.2)
      (fun h=>(by decide : true≠false) ((m (en i)).1.symm.trans (h.trans (m (en i)).2.1)))
      (fun h=>(by decide : true≠false) ((m (en i)).1.symm.trans (h.trans (m (en j)).2.1)))
    exact en.injective (Subtype.ext (Prod.ext eq e2))
  let p : Port↪Side c true := ⟨f,inj⟩
  let r : Port→Side c false := fun i=>⟨(en i).val.2,(m (en i)).2.1⟩
  have forward (a : Side c true) (b : Side c false) (ed : G.Adj a.val b.val) :
      ∃ i : Port,p i=a ∧ r i=b := by
    let k : P := ⟨(a.val,b.val),(boundary_mem G).mpr ⟨a.property,b.property,ed⟩⟩
    let i := en.symm k
    have eq : en i=k := en.apply_symm_apply k
    refine ⟨i,Subtype.ext ?_,Subtype.ext ?_⟩
    · exact congrArg (fun q : P=>q.val.1) eq
    · exact congrArg (fun q : P=>q.val.2) eq
  have reverse (a : Side c true) (b : Side c false) :
      (∃ i : Port,p i=a ∧ r i=b)→G.Adj a.val b.val := by
    rintro ⟨i,ha,hb⟩
    have one := congrArg Subtype.val ha
    have two := congrArg Subtype.val hb
    exact one ▸ two ▸ (m (en i)).2.2
  let e : (attach (sideGraph G c true) (sideGraph G c false) p r) ≃g G :=
    {toEquiv:=splitMap c true,map_rel_iff':=by
      rintro (a|a) (b|b)
      · rfl
      · exact ⟨forward a b,reverse a b⟩
      · exact ⟨fun h=>forward b a h.symm,fun h=>(reverse b a h).symm⟩
      · rfl}
  exact ⟨p,r,forward,e,fun _=>rfl,fun _=>rfl⟩

#print axioms true_shore_attachment
end KelmansCactus.AtomicBridge.RemoteFourCutAttachment
