import RemoteAvoid3SixTester
import RemoteAvoid3OneWire
import RemoteT2CompletionTransfer
import RemoteT2AvoidThree

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3ZeroFromTester
open SquareCap (HasFactor Port cap attach SmallTrivial)
open RemoteAvoid3SixTester (Stage wireIndex wireIndex_eq out oldPole contact tester tester_card
  tester_cubic tester_small tester_old_iff tester_contact_iff no_old_pole_contact)
open RemoteT2CompletionTransfer (eraseEdge marked SmallerIsolatedAvoid3)
open RemoteAvoid3OneWire (outside_factors_of_one_wire)
open RemoteT2AvoidThree (factor_image_injOn)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private def innerSix : Finset (Stage V) :=
  {oldPole false,oldPole true,contact false false,contact false true,contact true false,contact true true}

omit [Fintype V] in
private theorem innerSix_card : (innerSix (V:=V)).card=6 := by
  simp [innerSix,contact]

omit [Fintype V] in
private theorem inGadget (v : Stage V) : v∈innerSix ↔
    (∃ s : Bool,v=oldPole s) ∨ ∃ a s : Bool,v=contact a s := by
  constructor
  · intro h
    simp only [innerSix,mem_insert,mem_singleton] at h
    rcases h with e|e|e|e|e|e
    · exact Or.inl ⟨false,e⟩
    · exact Or.inl ⟨true,e⟩
    · exact Or.inr ⟨false,false,e⟩
    · exact Or.inr ⟨false,true,e⟩
    · exact Or.inr ⟨true,false,e⟩
    · exact Or.inr ⟨true,true,e⟩
  · rintro (⟨s,rfl⟩|⟨a,s,rfl⟩)
    · cases s <;> simp [innerSix]
    · cases a <;> cases s <;> simp [innerSix]

omit [Fintype V] in
private theorem outsideSix (v : Stage V) : v∉innerSix ↔ ∃ u : V,v=out u := by
  constructor
  · intro h
    rcases v with (((u|s)|a)|b)
    · exact ⟨u,rfl⟩
    · exact (h ((inGadget _).mpr (Or.inl ⟨s,rfl⟩))).elim
    · exact (h ((inGadget _).mpr (Or.inr ⟨false,a,rfl⟩))).elim
    · exact (h ((inGadget _).mpr (Or.inr ⟨true,b,rfl⟩))).elim
  · rintro ⟨u,rfl⟩ q
    rcases (inGadget _).mp q with ⟨s,e⟩|⟨a,s,e⟩
    · exact Sum.noConfusion (Sum.inl.inj (Sum.inl.inj e))
    · cases a
      · exact Sum.noConfusion (Sum.inl.inj e)
      · exact Sum.noConfusion e

omit [Fintype V] [DecidableEq V] in
private theorem out_contact_ne (v : V) (a s : Bool) : out v≠contact a s := by
  cases a <;> simp [contact]

omit [Fintype V] [DecidableEq V] in
private theorem contact_eq {a s b t : Bool} :
    (contact a s : Stage V)=contact b t ↔ a=b∧s=t := by
  cases a <;> cases b <;> simp [contact]

omit [Fintype V] [DecidableEq V] in
private theorem ports_eq (p : Port↪V) (k a s b t : Bool) :
    p (wireIndex k a s)=p (wireIndex k b t) ↔ a=b∧s=t :=
  ⟨fun q=>(wireIndex_eq k a b s t).mp (p.injective q),
    fun q=>congrArg p ((wireIndex_eq k a b s t).mpr q)⟩

/-- Zero-residue shore factorization from the same smaller Avoid3 promise.
Instead of a T2 cap promise, inflate the valid two-pole cap by two
disjoint-handle operations. A six-vertex gadget remains beyond four
disjoint port wires. Omit three of those wires: arithmetic forces the
factor to stay internal on both sides. -/
theorem zero_factor_of_smaller_avoid3 (G : SimpleGraph V) (p : Port↪V) (k : Bool)
    [DecidableRel (cap G p k).Adj]
    (small : SmallTrivial (cap G p k)) (cub : ∀ a,(cap G p k).degree a=3)
    (rem : Fintype.card V%6=0) (n : ℕ) (budget : Fintype.card V+6<n)
    (avo : SmallerIsolatedAvoid3.{u} n) : HasFactor G := by
  classical
  let H := tester G p k
  let a0 := p (wireIndex k false false)
  let a1 := p (wireIndex k false true)
  let a2 := p (wireIndex k true false)
  let a3 := p (wireIndex k true true)
  let b0 : Stage V := contact false false
  let b1 : Stage V := contact false true
  let b2 : Stage V := contact true false
  let b3 : Stage V := contact true true
  have cH := tester_cubic G p k cub
  have sH := tester_small G p k cub small
  have card := tester_card (V:=V)
  have vH := SquareCap.three_connected_of_small_trivial H cH (by omega) sH
  have smaller : Fintype.card (Stage V)<n := by omega
  have modu : Fintype.card (Stage V)%6=0 := by omega
  have e0 : H.Adj (out a0) b0 := (tester_contact_iff G p k false false a0).mpr rfl
  have e1 : H.Adj (out a1) b1 := (tester_contact_iff G p k false true a1).mpr rfl
  have e2 : H.Adj (out a2) b2 := (tester_contact_iff G p k true false a2).mpr rfl
  have o01 : (out a0 : Stage V)≠out a1 := by
    intro e
    have q : a0=a1 := Sum.inl.inj (Sum.inl.inj (Sum.inl.inj e))
    exact Bool.false_ne_true ((ports_eq p k false false false true).mp q).2
  have o02 : (out a0 : Stage V)≠out a2 := by
    intro e
    have q : a0=a2 := Sum.inl.inj (Sum.inl.inj (Sum.inl.inj e))
    exact Bool.false_ne_true ((ports_eq p k false false true false).mp q).1
  have o12 : (out a1 : Stage V)≠out a2 := by
    intro e
    have q : a1=a2 := Sum.inl.inj (Sum.inl.inj (Sum.inl.inj e))
    exact Bool.false_ne_true ((ports_eq p k false true true false).mp q).1
  have b01 : b0≠b1 := fun e=>Bool.false_ne_true ((contact_eq (V:=V)).mp e).2
  have b02 : b0≠b2 := fun e=>Bool.false_ne_true ((contact_eq (V:=V)).mp e).1
  let D := eraseEdge (eraseEdge (eraseEdge H (out a0) b0) (out a1) b1) (out a2) b2
  have df : HasFactor D :=
    avo (Stage V) H smaller cH vH sH modu (out a0) b0 (out a1) b1 (out a2) b2
      e0 e1 e2 o01 (out_contact_ne a0 false true) (out_contact_ne a1 false false).symm b01
      o02 (out_contact_ne a0 true false) (out_contact_ne a2 false false).symm b02
      (fun h=>h.elim (fun q=>o12 q.1.symm) (fun q=>out_contact_ne a2 false true q.1))
  let B : Finset (Stage V) := innerSix
  have three : 3∣B.card := by
    change 3∣(innerSix (V:=V)).card
    rw [innerSix_card]
    decide
  have seam : ∀ a : Stage V,a∉B → ∀ b∈B,D.Adj a b → a=out a3∧b=b3 := by
    intro a outB b bIn ed
    obtain ⟨v,rfl⟩ := (outsideSix a).mp outB
    rcases (inGadget b).mp bIn with ⟨s,rfl⟩|⟨t,s,rfl⟩
    · exact (no_old_pole_contact G p k s v ed.1.1.1).elim
    · have h := (tester_contact_iff G p k t s v).mp ed.1.1.1
      subst v
      cases t <;> cases s
      · exact (ed.1.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
      · exact (ed.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
      · exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim
      · exact ⟨rfl,rfl⟩
  have rest := outside_factors_of_one_wire D B three seam df
  let S := (univ : Finset (Stage V)) \ B
  let f : Stage V→V := Sum.elim (Sum.elim (Sum.elim id (fun _=>a0)) (fun _=>a0)) (fun _=>a0)
  have find (z : Stage V) (h : z∈S) : ∃ v : V,z=out v := (outsideSix z).mp (mem_sdiff.mp h).2
  have inj : Set.InjOn f (↑S : Set (Stage V)) := by
    intro a ha b hb eq
    obtain ⟨u,rfl⟩ := find a ha
    obtain ⟨v,rfl⟩ := find b hb
    exact congrArg out eq
  have keep (a : Stage V) (ha : a∈S) (b : Stage V) (hb : b∈S) (ed : D.Adj a b) :
      G.Adj (f a) (f b) := by
    obtain ⟨u,rfl⟩ := find a ha
    obtain ⟨v,rfl⟩ := find b hb
    exact (tester_old_iff G p k u v).mp ed.1.1.1
  have cover : S.image f=univ := by
    apply eq_univ_of_forall
    intro v
    exact mem_image.mpr ⟨out v,mem_sdiff.mpr ⟨mem_univ _,(outsideSix _).mpr ⟨v,rfl⟩⟩,rfl⟩
  have fact := factor_image_injOn f inj keep rest
  rwa [cover] at fact

/-- Automatically choose a good two-pole cap from the original
cubic cyclic-four four-port attachment. No packing hypothesis beyond
the strictly smaller Avoid3 promise is used. -/
theorem zero_factor_from_attachment {O : Type u} [Fintype O] [DecidableEq O]
    {G : SimpleGraph V} {P : SimpleGraph O} [DecidableRel G.Adj]
    (p : Port↪V) (r : Port→O) [DecidableRel (attach G P p r).Adj]
    (small : SmallTrivial (attach G P p r)) (cub : ∀ z,(attach G P p r).degree z=3)
    (large : 4<Fintype.card V) (other : 1<Fintype.card O)
    (rem : Fintype.card V%6=0) (n : ℕ) (size : Fintype.card V+6<n)
    (avo : SmallerIsolatedAvoid3.{u} n) : HasFactor G := by
  classical
  obtain ⟨k,ks,_⟩ := SquareCap.cubic_good_cap other large cub small
  exact zero_factor_of_smaller_avoid3 G p k ks (SquareCap.cap_cubic (fun v=>cub (Sum.inl v)) k)
    rem n size avo

#print axioms zero_factor_of_smaller_avoid3
#print axioms zero_factor_from_attachment
end KelmansCactus.AtomicBridge.RemoteAvoid3ZeroFromTester
