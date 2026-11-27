import ThetaDeadLeafCap
import ThetaAdjacentEarOriginal
import ThetaCase
import EarRelease
import EarPorts

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaDeadLeafOriginal
open SquareCap (FactorOn SmallTrivial omitEdge boundary factor_map)
open PentagonCap (attach attach_degree_outside SmallFourTrivial)
open PentagonProfile (Port)
open EarRelease (Released Rest contacts armEmbedding releasedIso releasedOfAdjacent gadget)
open EarPorts (exterior_contacts_injective)
open ThetaAdjacentEarCap (Omission released place kept_shape target)
open ThetaDeadLeafCap (released_choice)
open ThetaAdjacentEarOriginal (release_of)
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

/-- Exact transfer for an adjacent opposite ear when just one of
the two default replacement pairs is adjacent. The omitted exterior
edge may even be that known edge: it chooses the cap geometry, but
is not needed as a guaranteed edge of the refill. -/
theorem original_reduction
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (L : Released G p)
    (ear : G.Adj (p 1) (p 4))
    (cross0 : G.Adj (p 0) L.next4.val) (safe2 : ¬G.Adj (p 2) L.next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  classical
  let A := ThetaCase.ambient G p
  let X := Rest p
  let B : SimpleGraph X := G.comap Subtype.val
  let K := A.comap (gadget p)
  let R := armEmbedding arms
  let reverse := attach K B R (contacts L)
  let firstIso : reverse ≃g A := releasedIso arms L
  have rCard : Fintype.card (Fin 9⊕X)=Fintype.card (V⊕Fin 7) :=
    Fintype.card_congr firstIso.toEquiv
  have n7 : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have n9 : Fintype.card (Fin 9⊕X)=9+Fintype.card X := by simp
  have ports : 5≤Fintype.card V := by simpa using (Fintype.card_le_of_injective p p.injective)
  have largeA : 16≤Fintype.card (V⊕Fin 7) := by omega
  have largeX : 4≤Fintype.card X := by omega
  have rb (v : X) : reverse.degree (Sum.inr v)=3 :=
    (degree_iso firstIso (Sum.inr v)).trans (cub _)
  have injective := exterior_contacts_injective (Q:=K) (G:=B) (left:=R)
    (right:=contacts L) castThree largeX rb (small4_iso firstIso small4)
  let q : Port↪X := ⟨contacts L,injective⟩
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
  have extPt (v : X) : iso (Sum.inl v)=Sum.inl v.val := rfl
  have in7 : iso (Sum.inr 7)=Sum.inl (p 1) := rfl
  have in8 : iso (Sum.inr 8)=Sum.inl (p 4) := rfl
  have in6 : iso (Sum.inr 6)=Sum.inr 6 := rfl
  have c00 : (q 0).val=p 0 := by change (contacts L 0).val=p 0; simp [contacts]
  have c22 : (q 2).val=p 2 := by change (contacts L 2).val=p 2; simp [contacts]
  have c1 : q 1=L.next1 := by change contacts L 1=L.next1; simp [contacts]
  have c4 : q 4=L.next4 := by change contacts L 4=L.next4; simp [contacts]
  have s04 : B.Adj (q 0) (q 4) := by
    change G.Adj (q 0).val (q 4).val
    rwa [c00,c4]
  have s21 : ¬B.Adj (q 2) (q 1) := by
    change ¬G.Adj (q 2).val (q 1).val
    rwa [c22,c1]
  have choice (a b : V) (ab : G.Adj a b)
      (ne : ¬((a=p 1∧b=p 4)∨(a=p 4∧b=p 1)))
      (ha : a=p 1∨a=p 4) :
      ∃ e : Omission X, iso (e.originalEnds q).1=Sum.inl a ∧
        iso (e.originalEnds q).2=Sum.inl b := by
    rcases ha with rfl|rfl
    · have d1 : b≠p 1 := ab.ne.symm
      have d4 : b≠p 4 := fun h=>ne (Or.inl ⟨rfl,h⟩)
      let v : X := ⟨b,d1,d4⟩
      have eq : q 1=v := c1.trans ((L.end1 v).mp ab).symm
      exact ⟨.first,in7, (extPt _).trans (congrArg Sum.inl (congrArg Subtype.val eq))⟩
    · have d1 : b≠p 1 := fun h=>ne (Or.inr ⟨rfl,h⟩)
      have d4 : b≠p 4 := ab.ne.symm
      let v : X := ⟨b,d1,d4⟩
      have eq : q 4=v := c4.trans ((L.end4 v).mp ab).symm
      exact ⟨.fourth,in8,(extPt _).trans (congrArg Sum.inl (congrArg Subtype.val eq))⟩
  have use : ∃ e : Omission X,
      (iso (e.originalEnds q).1=Sum.inl x ∧ iso (e.originalEnds q).2=Sum.inl y) ∨
      (iso (e.originalEnds q).1=Sum.inl y ∧ iso (e.originalEnds q).2=Sum.inl x) := by
    by_cases xx : x=p 1∨x=p 4
    · obtain ⟨e,h⟩ := choice x y edge other xx
      exact ⟨e,Or.inl h⟩
    by_cases yy : y=p 1∨y=p 4
    · have no : ¬((y=p 1∧x=p 4)∨(y=p 4∧x=p 1)) := by tauto
      obtain ⟨e,h⟩ := choice y x edge.symm no yy
      exact ⟨e,Or.inr h⟩
    · let vx : X := ⟨x,fun e=>xx (Or.inl e),fun e=>xx (Or.inr e)⟩
      let vy : X := ⟨y,fun e=>yy (Or.inl e),fun e=>yy (Or.inr e)⟩
      exact ⟨.old vx vy,Or.inl ⟨extPt vx,extPt vy⟩⟩
  obtain ⟨e,matchE⟩ := use
  have real : new.Adj (e.originalEnds q).1 (e.originalEnds q).2 := by
    apply iso.map_adj_iff.mp
    rcases matchE with ⟨a,b⟩|⟨a,b⟩
    · rw [a,b]
      exact edge
    · rw [a,b]
      exact edge.symm
  have shape : Shape (target B K q e) := by
    exact kept_shape B K q e
      (show ThetaCase.theta.Adj 0 1 ∧ ThetaCase.theta.Adj 1 2 ∧ ThetaCase.theta.Adj 2 3 ∧
          ThetaCase.theta.Adj 3 4 ∧ ThetaCase.theta.Adj 4 5 ∧ ThetaCase.theta.Adj 5 0 from by decide)
      (show A.Adj (Sum.inr 2) (Sum.inl (p 1)) from ⟨1,rfl,rfl⟩)
      (show A.Adj (Sum.inr 5) (Sum.inl (p 4)) from ⟨4,rfl,rfl⟩)
  have nc : Fintype.card (X⊕Fin 9)=Fintype.card (V⊕Fin 7) :=
    Fintype.card_congr iso.toEquiv
  have sm : EarCase.CyclicF2Below.{u} (Fintype.card (X⊕Fin 9)) := nc.symm ▸ smaller
  have kEar : K.Adj 7 8 := ear
  have f := released_choice sm
    (fun v=>(degree_iso iso v).trans (cub _))
    (small_iso iso small) (small4_iso iso small4) (nc.symm ▸ order)
    s04 s21 e real shape kEar
  rw [←in6]
  exact map_omitted_factor iso matchE f

/-- Exact smaller-F2 conditional theorem with the actual thetas'
genuine absorbed edge as input, not a supplied arbitrary release. -/
theorem original_from_adjacent
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 1) (p 4))
    (cross0 : G.Adj (p 0) (release_of cub ear).next4.val)
    (safe2 : ¬G.Adj (p 2) (release_of cub ear).next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) :=
  original_reduction smaller cub small small4 order (release_of cub ear) ear cross0 safe2 edge other

#print axioms original_from_adjacent
#print axioms original_reduction
end
end KelmansCactus.AtomicBridge.ThetaDeadLeafOriginal
