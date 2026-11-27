import ThetaDeadLeafOriginal
import ThetaAdjacentEarMirror

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaDeadLeafSymmetry
open SquareCap (SmallTrivial FactorOn boundary factor_map omitEdge)
open PentagonCap (SmallFourTrivial)
open PentagonProfile (Port)
open EarRelease (Released)
noncomputable section
universe u

private def turn : Equiv.Perm (Fin 7) := ((Equiv.swap 0 3).trans (Equiv.swap 1 4)).trans (Equiv.swap 2 5)
private def turnIndex : Equiv.Perm Port := (Equiv.swap 0 2).trans (Equiv.swap 1 4)

def turnedPorts {V : Type*} (p : Port↪V) : Port↪V := turnIndex.toEmbedding.trans p

private theorem turn_arm : ∀ i : Port,turn (ThetaCase.arm i)=ThetaCase.arm (turnIndex i) := by decide
private theorem turn_adj : ∀ a b : Fin 7,ThetaCase.theta.Adj (turn a) (turn b) ↔
    ThetaCase.theta.Adj a b := by decide

private theorem turn_wires {V : Type*} (p : Port↪V) (x : V) (a : Fin 7) :
    (∃ i : Port,p i=x ∧ ThetaCase.arm i=turn a) ↔
    ∃ i : Port,turnedPorts p i=x ∧ ThetaCase.arm i=a := by
  constructor
  · rintro ⟨i,ix,ia⟩
    let j := turnIndex.symm i
    have ji : turnIndex j=i := turnIndex.apply_symm_apply i
    have jj : turnedPorts p j=x := (congrArg p ji).trans ix
    refine ⟨j,jj,turn.injective ?_⟩
    rw [turn_arm,ji,ia]
  · rintro ⟨i,ix,rfl⟩
    exact ⟨turnIndex i,ix,(turn_arm i).symm⟩

def turnedIso {V : Type*} (G : SimpleGraph V) (p : Port↪V) :
    ThetaCase.ambient G (turnedPorts p) ≃g ThetaCase.ambient G p where
  toEquiv := Equiv.sumCongr (Equiv.refl V) turn
  map_rel_iff' := by
    intro a b
    cases a <;> cases b
    · rfl
    · apply turn_wires
    · apply turn_wires
    · apply turn_adj

private theorem turn_root : turn 6=6 := by decide

private theorem degree_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (e : H ≃g K) (v : A) : H.degree v = K.degree (e v) := by
  rw [←card_neighborSet_eq_degree,←card_neighborSet_eq_degree]
  let u : H.neighborSet v ≃ K.neighborSet (e v) := {
    toFun := fun x => ⟨e x.val,e.map_adj_iff.mpr x.property⟩
    invFun := fun y => ⟨e.symm y.val,by
      have h : H.Adj (e.symm (e v)) (e.symm y.val) := e.symm.map_adj_iff.mpr y.property
      simpa using h⟩
    left_inv := fun _ => Subtype.ext (e.toEquiv.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.toEquiv.apply_symm_apply _) }
  exact Fintype.card_congr u

private theorem boundary_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (c : A → Bool) :
    (boundary H c).card = (boundary K (c ∘ e.symm)).card := by
  classical
  have memA (z : A×A) : z∈boundary H c ↔ c z.1=true ∧ c z.2=false ∧ H.Adj z.1 z.2 := by
    simp [boundary]
  have memB (z : B×B) : z∈boundary K (c ∘ e.symm) ↔
      c (e.symm z.1)=true ∧ c (e.symm z.2)=false ∧ K.Adj z.1 z.2 := by simp [boundary]
  apply card_bij (fun z _ => (e z.1,e z.2))
  · intro z h
    obtain ⟨f,t,u⟩ := (memA z).mp h
    exact (memB _).mpr ⟨by simpa using f,by simpa using t,e.map_adj_iff.mpr u⟩
  · intro a _ b _ h
    exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h)) (e.toEquiv.injective (congrArg Prod.snd h))
  · intro z h
    obtain ⟨f,t,u⟩ := (memB z).mp h
    exact ⟨(e.symm z.1,e.symm z.2),(memA _).mpr ⟨f,t,e.symm.map_adj_iff.mpr u⟩,
      Prod.ext (e.toEquiv.apply_symm_apply _) (e.toEquiv.apply_symm_apply _)⟩

private theorem small_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallTrivial K) :
    SmallTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  rcases h (c ∘ e.symm) near with ts|fs
  · left
    intro x y hx hy
    apply e.toEquiv.injective
    exact ts (e x) (e y) (by simpa using hx) (by simpa using hy)
  · right
    intro x y hx hy
    apply e.toEquiv.injective
    exact fs (e x) (e y) (by simpa using hx) (by simpa using hy)


private theorem small4_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallFourTrivial K) :
    SmallFourTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  obtain ⟨b,cut⟩ := h (c ∘ e.symm) near
  refine ⟨b,?_⟩
  intro x y z hx hy hz
  rcases cut (e x) (e y) (e z) (by simpa using hx) (by simpa using hy) (by simpa using hz) with xy|xz|yz
  · exact Or.inl (e.toEquiv.injective xy)
  · exact Or.inr (Or.inl (e.toEquiv.injective xz))
  · exact Or.inr (Or.inr (e.toEquiv.injective yz))



open ThetaAdjacentEarOriginal (release_of)
open ThetaAdjacentEarMirror (reflectedPorts reflectedIso released_mirror)

private theorem turn0 {V : Type*} (p : Port↪V) : turnedPorts p 0=p 2 := rfl
private theorem turn1 {V : Type*} (p : Port↪V) : turnedPorts p 1=p 4 := rfl
private theorem turn2 {V : Type*} (p : Port↪V) : turnedPorts p 2=p 0 := rfl
private theorem turn4 {V : Type*} (p : Port↪V) : turnedPorts p 4=p 1 := rfl

private def rotateReleased {V : Type*} {G : SimpleGraph V} {p : Port↪V}
    (L : Released G p) : Released G (turnedPorts p) where
  next1 := ⟨L.next4.val,by simpa [turn1] using L.next4.property.2,
    by simpa [turn4] using L.next4.property.1⟩
  next4 := ⟨L.next1.val,by simpa [turn1] using L.next1.property.2,
    by simpa [turn4] using L.next1.property.1⟩
  end1 v := by
    change G.Adj (p 4) v.val ↔ _
    exact (L.end4 ⟨v.val,by simpa [turn4] using v.property.2,
      by simpa [turn1] using v.property.1⟩).trans
        (Iff.intro (fun h=>Subtype.ext (congrArg (fun w : EarRelease.Rest p=>w.val) h))
          (fun h=>Subtype.ext (congrArg (fun w : EarRelease.Rest (turnedPorts p)=>w.val) h)))
  end4 v := by
    change G.Adj (p 1) v.val ↔ _
    exact (L.end1 ⟨v.val,by simpa [turn4] using v.property.2,
      by simpa [turn1] using v.property.1⟩).trans
        (Iff.intro (fun h=>Subtype.ext (congrArg (fun w : EarRelease.Rest p=>w.val) h))
          (fun h=>Subtype.ext (congrArg (fun w : EarRelease.Rest (turnedPorts p)=>w.val) h)))

private theorem transport {V : Type*} [Fintype V] [DecidableEq V]
    {A B : SimpleGraph (V⊕Fin 7)} (I : A ≃g B)
    (ext : ∀ v : V,I (.inl v)=.inl v) (root : I (.inr 6)=.inr 6)
    (x y : V)
    (f : FactorOn (omitEdge A (Sum.inl x) (Sum.inl y)) (univ.erase (Sum.inr 6))) :
    FactorOn (omitEdge B (Sum.inl x) (Sum.inl y)) (univ.erase (Sum.inr 6)) := by
  have mapp (a b : V⊕Fin 7) (e : (omitEdge A (Sum.inl x) (Sum.inl y)).Adj a b) :
      (omitEdge B (Sum.inl x) (Sum.inl y)).Adj (I a) (I b) := by
    refine ⟨I.map_adj_iff.mpr e.1,?_⟩
    change ¬((_=_∧_ = _)∨(_=_∧_ = _))
    rw [←ext x,←ext y]
    rintro (⟨p,q⟩|⟨p,q⟩)
    · exact e.2 (Or.inl ⟨I.injective p,I.injective q⟩)
    · exact e.2 (Or.inr ⟨I.injective p,I.injective q⟩)
  have result := factor_map I.toEquiv.toEmbedding mapp f
  rw [Finset.map_erase,map_univ_equiv] at result
  change FactorOn (omitEdge B (Sum.inl x) (Sum.inl y)) (univ.erase (I (.inr 6))) at result
  rwa [root] at result

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Either one of the nominal replacement-pair edges may be present.
The choice is transferred by the half-turn of the actual theta. -/
theorem only_one
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 1) (p 4)) (L : Released G p)
    (one : (G.Adj (p 0) L.next4.val ∧ ¬G.Adj (p 2) L.next1.val) ∨
      (¬G.Adj (p 0) L.next4.val ∧ G.Adj (p 2) L.next1.val))
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  rcases one with ⟨a,b⟩|⟨a,b⟩
  · exact ThetaDeadLeafOriginal.original_reduction smaller cub small small4 order L ear a b edge other
  · classical
    let I := turnedIso G p
    have cb (v) : (ThetaCase.ambient G (turnedPorts p)).degree v=3 :=
      (degree_iso I v).trans (cub _)
    let N := rotateReleased L
    have ed : G.Adj (turnedPorts p 1) (turnedPorts p 4) := by rw [turn1,turn4]; exact ear.symm
    have present : G.Adj (turnedPorts p 0) N.next4.val := by rw [turn0]; exact b
    have absent : ¬G.Adj (turnedPorts p 2) N.next1.val := by rw [turn2]; exact a
    have ban : ¬((x=turnedPorts p 1 ∧ y=turnedPorts p 4)∨
        (x=turnedPorts p 4 ∧ y=turnedPorts p 1)) := by rw [turn1,turn4]; tauto
    have f := ThetaDeadLeafOriginal.original_reduction smaller cb (small_iso I small)
      (small4_iso I small4) order N ed present absent edge ban
    exact transport I (fun _=>rfl) (congrArg Sum.inr turn_root) x y f

private theorem ref1 {V : Type*} (p : Port↪V) : reflectedPorts p 1=p 2 := rfl
private theorem ref4 {V : Type*} (p : Port↪V) : reflectedPorts p 4=p 0 := rfl

/-- The same exactly-one-replacement-edge branch when the absorbed
opposite pair is at sites 1 and 4 instead of sites 2 and 5. -/
theorem reflected_only_one
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 0) (p 2))
    (one : (G.Adj (reflectedPorts p 0) (released_mirror cub ear).next4.val ∧
        ¬G.Adj (reflectedPorts p 2) (released_mirror cub ear).next1.val) ∨
      (¬G.Adj (reflectedPorts p 0) (released_mirror cub ear).next4.val ∧
        G.Adj (reflectedPorts p 2) (released_mirror cub ear).next1.val))
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 0 ∧ y=p 2) ∨ (x=p 2 ∧ y=p 0))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  classical
  let I := reflectedIso G p
  have cb (v) : (ThetaCase.ambient G (reflectedPorts p)).degree v=3 :=
    (degree_iso I v).trans (cub _)
  have ed : G.Adj (reflectedPorts p 1) (reflectedPorts p 4) := by rw [ref1,ref4]; exact ear.symm
  have ban : ¬((x=reflectedPorts p 1 ∧ y=reflectedPorts p 4)∨
        (x=reflectedPorts p 4 ∧ y=reflectedPorts p 1)) := by rw [ref1,ref4]; tauto
  have f := only_one smaller cb (small_iso I small) (small4_iso I small4)
    order ed (released_mirror cub ear) one edge ban
  exact transport I (fun _=>rfl) rfl x y f

#print axioms only_one
#print axioms reflected_only_one
end
end KelmansCactus.AtomicBridge.ThetaDeadLeafSymmetry
