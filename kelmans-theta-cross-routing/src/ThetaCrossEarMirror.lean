import ThetaCrossEarOriginal
import ThetaAdjacentEarMirror

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarMirror
open SquareCap (SmallTrivial FactorOn boundary factor_map omitEdge)
open PentagonCap (SmallFourTrivial)
open PentagonProfile (Port)
open EarRelease (Released)
noncomputable section
universe u

open ThetaAdjacentEarMirror (reflectedPorts reflectedIso released_mirror)

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



private theorem reflected_cub {V : Type u} [Fintype V] {G : SimpleGraph V}
    {p : Port↪V} [DecidableRel (ThetaCase.ambient G p).Adj]
    [DecidableRel (ThetaCase.ambient G (reflectedPorts p)).Adj]
    (old : ∀ a,(ThetaCase.ambient G p).degree a=3) :
    ∀ a,(ThetaCase.ambient G (reflectedPorts p)).degree a=3 :=
  fun a=>(degree_iso (reflectedIso G p) a).trans (old _)

private theorem cp0 {V : Type*} (p : Port↪V) : reflectedPorts p 0=p 4 := rfl
private theorem cp1 {V : Type*} (p : Port↪V) : reflectedPorts p 1=p 2 := rfl
private theorem cp2 {V : Type*} (p : Port↪V) : reflectedPorts p 2=p 1 := rfl
private theorem cp4 {V : Type*} (p : Port↪V) : reflectedPorts p 4=p 0 := rfl

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Reflected exact cross routing when the adjacent original pair
is at ring sites 1 and 4 rather than sites 2 and 5. -/
theorem mirrored_original_from_adjacent
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (ear : G.Adj (p 0) (p 2))
    (safe14 : ¬G.Adj (p 1) (p 4))
    (cross0 : G.Adj (reflectedPorts p 0) (released_mirror cub ear).next4.val)
    (cross2 : G.Adj (reflectedPorts p 2) (released_mirror cub ear).next1.val)
    {x y : V} (edge : G.Adj x y)
    (other : ¬((x=p 0 ∧ y=p 2) ∨ (x=p 2 ∧ y=p 0)))
    (keep0 : ¬((x=reflectedPorts p 0 ∧ y=(released_mirror cub ear).next4.val) ∨
        (x=(released_mirror cub ear).next4.val ∧ y=reflectedPorts p 0)))
    (keep2 : ¬((x=reflectedPorts p 2 ∧ y=(released_mirror cub ear).next1.val) ∨
        (x=(released_mirror cub ear).next1.val ∧ y=reflectedPorts p 2))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  classical
  let I := reflectedIso G p
  have ban : ¬((x=reflectedPorts p 1 ∧ y=reflectedPorts p 4)∨
      (x=reflectedPorts p 4 ∧ y=reflectedPorts p 1)) := by
    rw [cp1,cp4]
    tauto
  have ed : G.Adj (reflectedPorts p 1) (reflectedPorts p 4) := by
    rw [cp1,cp4]
    exact ear.symm
  have safe02 : ¬G.Adj (reflectedPorts p 0) (reflectedPorts p 2) := by
    rw [cp0,cp2]
    exact fun e=>safe14 e.symm
  have saf := ThetaCrossEarGeometry.replacements_nonadjacent (released_mirror cub ear)
    (ThetaCrossEarSquareFree.no_exterior_square cub small4) ed
  have f := ThetaCrossEarOriginal.original_reduction smaller
    (reflected_cub cub) (small_iso I small) (small4_iso I small4) order
    (released_mirror cub ear) ed safe02 (fun e=>saf e.symm) cross0 cross2 edge ban keep0 keep2
  have mapp (a b : V⊕Fin 7)
      (ed : (omitEdge (ThetaCase.ambient G (reflectedPorts p)) (Sum.inl x) (Sum.inl y)).Adj a b) :
      (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y)).Adj (I a) (I b) := by
    refine ⟨I.map_adj_iff.mpr ed.1,?_⟩
    change ¬((_=_∧_ = _)∨(_=_∧_ = _))
    have xx : I (Sum.inl x)=Sum.inl x := rfl
    have yy : I (Sum.inl y)=Sum.inl y := rfl
    rw [←xx,←yy]
    rintro (⟨a1,b1⟩|⟨a1,b1⟩)
    · exact ed.2 (Or.inl ⟨I.injective a1,I.injective b1⟩)
    · exact ed.2 (Or.inr ⟨I.injective a1,I.injective b1⟩)
  have result := factor_map I.toEquiv.toEmbedding mapp f
  rw [Finset.map_erase,map_univ_equiv] at result
  change FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
    (univ.erase (I (Sum.inr 6))) at result
  have root : I (Sum.inr 6)=Sum.inr 6 := rfl
  rwa [root] at result

#print axioms mirrored_original_from_adjacent
end
end KelmansCactus.AtomicBridge.ThetaCrossEarMirror
