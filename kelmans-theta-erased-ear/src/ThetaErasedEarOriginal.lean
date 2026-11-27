import ThetaErasedEarCap
import ThetaDeadLeafCrossOriginal
import ThetaCrossEarGeometry
import ThetaCrossEarSquareFree
import ThetaAdjacentEarOriginal
import ThetaCase
import EarRelease
import EarPorts
import ThetaDeadLeafCrossCover
import ThetaAdjacentEarMirror

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaErasedEarOriginal
open SquareCap (FactorOn SmallTrivial omitEdge boundary factor_map)
open PentagonCap (attach attach_degree_outside SmallFourTrivial)
open PentagonProfile (Port)
open EarRelease (Released Rest contacts armEmbedding releasedIso releasedOfAdjacent gadget)
open EarPorts (exterior_contacts_injective)
open ThetaAdjacentEarCap (released place)
open ThetaErasedEarCap (erased erased_shape)
open ThetaDeadLeafCrossOriginal (released_contacts_injective)
open ThetaAdjacentEarOriginal (release_of)
open ThetaAdjacentEarMirror (reflectedPorts reflectedIso released_mirror)
open ThetaAdjacentEarRefill (Shape In Out)
noncomputable section
universe u

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

private def castThree : Fin 3 ↪ Fin 9 :=
  ⟨fun i=>⟨i.val,by have l:=i.isLt; omega⟩,
    fun i j e=>Fin.ext (congrArg (fun x : Fin 9=>x.val) e)⟩

private def swapAttach {W X : Type*} (A : SimpleGraph W) (B : SimpleGraph X)
    (a : Port ↪ W) (b : Port ↪ X) :
    attach A B a b ≃g attach B A b a := by
  refine {toEquiv := Equiv.sumComm W X, map_rel_iff' := ?_}
  intro x y
  cases x <;> cases y
  · rfl
  · simp [PentagonCap.attach,PentagonCap.attachAdj,and_comm]
  · simp [PentagonCap.attach,PentagonCap.attachAdj,and_comm]
  · rfl

private theorem port_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)}
    {p : Port↪V} {r : Port ↪ Fin 7} [DecidableRel (attach G P p r).Adj]
    (cub : ∀ v,(attach G P p r).degree v=3) (i : Port) : G.degree (p i)=2 := by
  have fi : (univ : Finset Port).filter (fun j=>p j=p i) = {i} := by
    ext j
    simp [p.injective.eq_iff]
  have count := cub (Sum.inl (p i))
  rw [attach_degree_outside,fi,card_singleton] at count
  omega



private def arms : Port↪Fin 7 := ⟨ThetaCase.arm,by decide⟩
private theorem exactPlace : (armEmbedding arms : Port→Fin 9)=place := by
  funext i
  have d : ∀ i : Port,armEmbedding arms i=place i := by decide
  exact d i

private theorem map_omitted_factor {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {G : SimpleGraph A} {H : SimpleGraph B}
    (iso : G ≃g H) {r a b : A} {x y : B}
    (matchE : (iso a=x ∧ iso b=y) ∨ (iso a=y ∧ iso b=x))
    (f : FactorOn (omitEdge G a b) (univ.erase r)) :
    FactorOn (omitEdge H x y) (univ.erase (iso r)) := by
  have preserve (s t : A) (ed : (omitEdge G a b).Adj s t) :
      (omitEdge H x y).Adj (iso s) (iso t) := by
    refine ⟨iso.map_adj_iff.mpr ed.1,?_⟩
    rcases matchE with ⟨ax,byy⟩|⟨ay,bx⟩
    · rintro (⟨e,g⟩|⟨e,g⟩)
      · exact ed.2 (Or.inl ⟨iso.injective (e.trans ax.symm),iso.injective (g.trans byy.symm)⟩)
      · exact ed.2 (Or.inr ⟨iso.injective (e.trans byy.symm),iso.injective (g.trans ax.symm)⟩)
    · rintro (⟨e,g⟩|⟨e,g⟩)
      · exact ed.2 (Or.inr ⟨iso.injective (e.trans bx.symm),iso.injective (g.trans ay.symm)⟩)
      · exact ed.2 (Or.inl ⟨iso.injective (e.trans ay.symm),iso.injective (g.trans bx.symm)⟩)
  have m := factor_map iso.toEquiv.toEmbedding preserve f
  rwa [Finset.map_erase,map_univ_equiv] at m

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Canonical orientation: the original p1–p4 edge itself is
the omitted edge, not a retained edge available to the refill. -/
theorem original_reduction
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (L : Released G p) (ear : G.Adj (p 1) (p 4)) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p 1)) (Sum.inl (p 4)))
      (univ.erase (Sum.inr 6)) := by
  classical
  let A := ThetaCase.ambient G p
  let X := Rest p
  let B : SimpleGraph X := G.comap Subtype.val
  let K := A.comap (gadget p)
  let R := armEmbedding arms
  let reverse := attach K B R (contacts L)
  let firstIso : reverse ≃g A := releasedIso arms L
  let q : Port↪X := ⟨contacts L,released_contacts_injective cub small4 order L⟩
  let new := released B K q
  have rEq : (R : Port→Fin 9)=place := exactPlace
  have eqNew : attach B K q R=new := by rw [rEq]; rfl
  let comb : attach B K q R ≃g A := (swapAttach B K q R).trans firstIso
  let iso : new ≃g A := {
    toEquiv := comb.toEquiv
    map_rel_iff' := by
      intro a b
      rw [←eqNew]
      exact comb.map_adj_iff }
  have in7 : iso (Sum.inr 7)=Sum.inl (p 1) := rfl
  have in8 : iso (Sum.inr 8)=Sum.inl (p 4) := rfl
  have in6 : iso (Sum.inr 6)=Sum.inr 6 := rfl
  have c1 : q 1=L.next1 := by change contacts L 1=L.next1; simp [contacts]
  have c4 : q 4=L.next4 := by change contacts L 4=L.next4; simp [contacts]
  have saf : ¬G.Adj L.next1.val L.next4.val :=
    ThetaCrossEarGeometry.replacements_nonadjacent L
      (ThetaCrossEarSquareFree.no_exterior_square cub small4) ear
  have s41 : ¬B.Adj (q 4) (q 1) := by
    change ¬G.Adj (q 4).val (q 1).val
    rw [c4,c1]
    exact fun e=>saf e.symm
  have shape : Shape (erased B K q) := erased_shape B K q
    (show ThetaCase.theta.Adj 0 1 ∧ ThetaCase.theta.Adj 1 2 ∧ ThetaCase.theta.Adj 2 3 ∧
          ThetaCase.theta.Adj 3 4 ∧ ThetaCase.theta.Adj 4 5 ∧ ThetaCase.theta.Adj 5 0 from by decide)
      (show A.Adj (Sum.inr 2) (Sum.inl (p 1)) from ⟨1,rfl,rfl⟩)
      (show A.Adj (Sum.inr 5) (Sum.inl (p 4)) from ⟨4,rfl,rfl⟩)
  have nc : Fintype.card (X⊕Fin 9)=Fintype.card (V⊕Fin 7) :=
    Fintype.card_congr iso.toEquiv
  have sm : EarCase.CyclicF2Below.{u} (Fintype.card (X⊕Fin 9)) := nc.symm ▸ smaller
  have cb (v) : new.degree v=3 := (degree_iso iso v).trans (cub _)
  have s3 : SmallTrivial new := small_iso iso small
  have s4 : SmallFourTrivial new := small4_iso iso small4
  have ord : Fintype.card (X⊕Fin 9)%6=4 := nc.symm ▸ order
  have f : FactorOn (erased B K q) (univ.erase (Sum.inr 6)) := by
    by_cases b : B.Adj (q 2) (q 1)
    · exact ThetaErasedEarCap.second_extra sm cb s3 s4 ord b s41 shape
    · by_cases a : B.Adj (q 0) (q 4)
      · exact ThetaErasedEarCap.first_extra sm cb s3 s4 ord a b shape
      · exact ThetaErasedEarCap.zero_extra sm cb s3 s4 ord a b shape
  rw [←in6]
  exact map_omitted_factor iso (Or.inl ⟨in7,in8⟩) f

/-- The omitted edge may be the adjacent original opposite pair,
without any smaller order-zero avoidance assumption. -/
theorem erase_14
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4) (ear : G.Adj (p 1) (p 4)) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p 1)) (Sum.inl (p 4)))
      (univ.erase (Sum.inr 6)) :=
  original_reduction smaller cub small small4 order (release_of cub ear) ear

/-- Symmetric case: the opposite original pair 0–2 is omitted. -/
theorem erase_02
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4) (ear : G.Adj (p 0) (p 2)) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p 0)) (Sum.inl (p 2)))
      (univ.erase (Sum.inr 6)) := by
  classical
  let iso := reflectedIso G p
  have cb (v) : (ThetaCase.ambient G (reflectedPorts p)).degree v=3 :=
    (degree_iso iso v).trans (cub _)
  have er : G.Adj (reflectedPorts p 1) (reflectedPorts p 4) := ear.symm
  have f := original_reduction smaller cb (small_iso iso small) (small4_iso iso small4)
    order (released_mirror cub ear) er
  exact map_omitted_factor iso (Or.inr ⟨rfl,rfl⟩) f

private theorem reversed_omit {W : Type*} (H : SimpleGraph W) (a b : W) :
    omitEdge H a b=omitEdge H b a := by
  ext x y
  show (H.Adj x y ∧ ¬((x=a∧y=b)∨(x=b∧y=a))) ↔
    (H.Adj x y ∧ ¬((x=b∧y=a)∨(x=a∧y=b)))
  tauto

/-- If either original opposite contact pair is an edge, every
genuine exterior omission is a smaller cyclic-four F2 reduction:
use a retained ear if available, or erase the only adjacent ear. -/
theorem any_exterior_with_one_ear
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 1) (p 4) ∨ G.Adj (p 0) (p 2))
    {x y : V} (edge : G.Adj x y) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  rcases ear with h|h
  · by_cases e : (x=p 1 ∧ y=p 4)∨(x=p 4∧y=p 1)
    · rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact erase_14 smaller cub small small4 order h
      · rw [reversed_omit _ (Sum.inl (p 4)) (Sum.inl (p 1))]
        exact erase_14 smaller cub small small4 order h
    · exact ThetaDeadLeafCrossCover.released_exterior_if_one_retained_ear smaller cub
        small small4 order edge (Or.inl ⟨h,e⟩)
  · by_cases e : (x=p 0 ∧ y=p 2)∨(x=p 2∧y=p 0)
    · rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact erase_02 smaller cub small small4 order h
      · rw [reversed_omit _ (Sum.inl (p 2)) (Sum.inl (p 0))]
        exact erase_02 smaller cub small small4 order h
    · exact ThetaDeadLeafCrossCover.released_exterior_if_one_retained_ear smaller cub
        small small4 order edge (Or.inr ⟨h,e⟩)

#print axioms original_reduction
#print axioms erase_14
#print axioms erase_02
#print axioms any_exterior_with_one_ear
end
end KelmansCactus.AtomicBridge.ThetaErasedEarOriginal
