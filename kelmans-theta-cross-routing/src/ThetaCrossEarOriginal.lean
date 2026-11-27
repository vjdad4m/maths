import ThetaCrossEarCap
import ThetaCrossEarGeometry
import ThetaCrossEarSquareFree
import ThetaAdjacentEarOriginal
import ThetaCase
import EarRelease
import EarPorts

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarOriginal
open SquareCap (FactorOn SmallTrivial omitEdge boundary factor_map)
open PentagonCap (attach attach_degree_outside SmallFourTrivial)
open PentagonProfile (Port)
open EarRelease (Released Rest contacts armEmbedding releasedIso releasedOfAdjacent gadget)
open EarPorts (exterior_contacts_injective)
open ThetaAdjacentEarCap (Omission released place kept_shape target)
open ThetaCrossEarCap (released_reduction)
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

/-- In the original exact theta, cross-route the two old contact
vertices to one cap leaf and the two released contacts to the other.
An omission touching an absorbed endpoint suppresses the actual
corresponding cap wire and must leave both cross edges intact. -/
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
    (safe02 : ¬G.Adj (p 0) (p 2))
    (safe41 : ¬G.Adj L.next4.val L.next1.val)
    (cross0 : G.Adj (p 0) L.next4.val) (cross2 : G.Adj (p 2) L.next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1)))
    (keep0 : ¬((x=p 0 ∧ y=L.next4.val) ∨ (x=L.next4.val ∧ y=p 0)))
    (keep2 : ¬((x=p 2 ∧ y=L.next1.val) ∨ (x=L.next1.val ∧ y=p 2))) :
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
  have s02 : ¬B.Adj (q 0) (q 2) := by
    change ¬G.Adj (q 0).val (q 2).val
    rwa [c00,c22]
  have s41 : ¬B.Adj (q 4) (q 1) := by
    change ¬G.Adj (q 4).val (q 1).val
    rwa [c4,c1]
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
  have ext0 : iso (Out (q 0))=Sum.inl (p 0) := (extPt _).trans (congrArg Sum.inl c00)
  have ext2 : iso (Out (q 2))=Sum.inl (p 2) := (extPt _).trans (congrArg Sum.inl c22)
  have ext1 : iso (Out (q 1))=Sum.inl L.next1.val :=
    (extPt _).trans (congrArg Sum.inl (congrArg Subtype.val c1))
  have ext4 : iso (Out (q 4))=Sum.inl L.next4.val :=
    (extPt _).trans (congrArg Sum.inl (congrArg Subtype.val c4))
  have keep_pair (a b : X) (v w : V)
      (av : iso (Out a)=Sum.inl v) (bw : iso (Out b)=Sum.inl w)
      (ed : G.Adj v w)
      (h : ¬((x=v ∧ y=w)∨(x=w ∧ y=v))) :
      (target B K q e).Adj (Out a) (Out b) := by
    refine ⟨iso.map_adj_iff.mp (by rw [av,bw]; exact ed),?_⟩
    intro deleted
    apply h
    rcases matchE with ⟨mx,my⟩|⟨mx,my⟩ <;> rcases deleted with ⟨ex,ey⟩|⟨ex,ey⟩
    · exact Or.inl ⟨Sum.inl_injective (mx.symm.trans ((congrArg iso ex).symm.trans av)),
        Sum.inl_injective (my.symm.trans ((congrArg iso ey).symm.trans bw))⟩
    · exact Or.inr ⟨Sum.inl_injective (mx.symm.trans ((congrArg iso ey).symm.trans bw)),
        Sum.inl_injective (my.symm.trans ((congrArg iso ex).symm.trans av))⟩
    · exact Or.inr ⟨Sum.inl_injective (my.symm.trans ((congrArg iso ey).symm.trans bw)),
        Sum.inl_injective (mx.symm.trans ((congrArg iso ex).symm.trans av))⟩
    · exact Or.inl ⟨Sum.inl_injective (my.symm.trans ((congrArg iso ex).symm.trans av)),
        Sum.inl_injective (mx.symm.trans ((congrArg iso ey).symm.trans bw))⟩
  have kEar : K.Adj 7 8 := ear
  have nc : Fintype.card (X⊕Fin 9)=Fintype.card (V⊕Fin 7) :=
    Fintype.card_congr iso.toEquiv
  have sm : EarCase.CyclicF2Below.{u} (Fintype.card (X⊕Fin 9)) := nc.symm ▸ smaller
  have f := released_reduction sm
    (fun v=>(degree_iso iso v).trans (cub _))
    (small_iso iso small) (small4_iso iso small4) (nc.symm ▸ order)
    s02 s41 e real shape kEar
    (keep_pair _ _ _ _ ext0 ext4 cross0 keep0) (keep_pair _ _ _ _ ext2 ext1 cross2 keep2)
  rw [←in6]
  exact map_omitted_factor iso matchE f

/-- Canonical route when each originally nominated replacement pair is
an actual retained edge, and the other original opposite pair is a nonedge.
The two replacement vertices form a nonedge by square-freeness. -/
theorem original_from_adjacent_of_square_free
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 1) (p 4))
    (safe02 : ¬G.Adj (p 0) (p 2))
    (noSquare : ∀ a b c d : V,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c∨b=d)
    (cross0 : G.Adj (p 0) (release_of cub ear).next4.val)
    (cross2 : G.Adj (p 2) (release_of cub ear).next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1)))
    (keep0 : ¬((x=p 0 ∧ y=(release_of cub ear).next4.val) ∨
        (x=(release_of cub ear).next4.val ∧ y=p 0)))
    (keep2 : ¬((x=p 2 ∧ y=(release_of cub ear).next1.val) ∨
        (x=(release_of cub ear).next1.val ∧ y=p 2))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  have saf := ThetaCrossEarGeometry.replacements_nonadjacent (release_of cub ear) noSquare ear
  exact original_reduction smaller cub small small4 order (release_of cub ear)
    ear safe02 (fun e=>saf e.symm) cross0 cross2 edge other keep0 keep2

/-- The square-freeness needed by cross routing is automatic in
the exact ambient cubic cyclic-five theta; no additional girth premise. -/
theorem original_from_adjacent
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 1) (p 4))
    (safe02 : ¬G.Adj (p 0) (p 2))
    (cross0 : G.Adj (p 0) (release_of cub ear).next4.val)
    (cross2 : G.Adj (p 2) (release_of cub ear).next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 1 ∧ y=p 4) ∨ (x=p 4 ∧ y=p 1)))
    (keep0 : ¬((x=p 0 ∧ y=(release_of cub ear).next4.val) ∨
        (x=(release_of cub ear).next4.val ∧ y=p 0)))
    (keep2 : ¬((x=p 2 ∧ y=(release_of cub ear).next1.val) ∨
        (x=(release_of cub ear).next1.val ∧ y=p 2))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) :=
  original_from_adjacent_of_square_free smaller cub small small4 order ear safe02
    (ThetaCrossEarSquareFree.no_exterior_square cub small4) cross0 cross2 edge other keep0 keep2

#print axioms original_from_adjacent
#print axioms original_reduction
end
end KelmansCactus.AtomicBridge.ThetaCrossEarOriginal
