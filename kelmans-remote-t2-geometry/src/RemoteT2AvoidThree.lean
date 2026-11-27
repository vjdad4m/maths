import RemoteT2Scope

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2AvoidThree
open SquareCap (FactorOn IsTile omitEdge)
open RemoteT2Scope (Remote)
noncomputable section

theorem factor_image_injOn {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph A} {H : SimpleGraph B} {S : Finset A}
    (f : A→B) (inj : Set.InjOn f (↑S : Set A))
    (mono : ∀ x∈S,∀ y∈S,G.Adj x y→H.Adj (f x) (f y))
    (h : FactorOn G S) : FactorOn H (S.image f) := by
  obtain ⟨P,tiles,disj,cover⟩ := h
  have sub {T : Finset A} (h : T∈P) : T⊆S :=
    fun z hz=>cover ▸ mem_biUnion.mpr ⟨T,h,hz⟩
  refine ⟨P.image (fun t=>t.image f),?_,?_,?_⟩
  · intro U u
    obtain ⟨T,m,rfl⟩ := mem_image.mp u
    obtain ⟨n,c,ct,arms⟩ := tiles T m
    have inT : Set.InjOn f (↑T : Set A) :=
      fun _ a _ b e=>inj (sub m a) (sub m b) e
    refine ⟨(card_image_of_injOn inT).trans n,f c,mem_image.mpr ⟨c,ct,rfl⟩,?_⟩
    intro v vT nc
    obtain ⟨z,zt,rfl⟩ := mem_image.mp vT
    exact mono c (sub m ct) z (sub m zt)
      (arms z zt (fun e=>nc (congrArg f e)))
  · intro T t U u differ
    obtain ⟨A,a,rfl⟩ := mem_image.mp t
    obtain ⟨B,b,rfl⟩ := mem_image.mp u
    apply disjoint_left.mpr
    intro w wa wb
    obtain ⟨x,hx,hfx⟩ := mem_image.mp wa
    obtain ⟨y,hy,hfy⟩ := mem_image.mp wb
    have xy : x=y := inj (sub a hx) (sub b hy) (hfx.trans hfy.symm)
    exact disjoint_left.mp (disj A a B b (fun e=>differ (congrArg (fun t=>t.image f) e)))
      hx (xy.symm ▸ hy)
  · ext z
    constructor
    · intro h
      obtain ⟨T,t,hz⟩ := mem_biUnion.mp h
      obtain ⟨A,a,rfl⟩ := mem_image.mp t
      obtain ⟨x,xA,rfl⟩ := mem_image.mp hz
      exact mem_image.mpr ⟨x,sub a xA,rfl⟩
    · intro e
      obtain ⟨x,xS,rfl⟩ := mem_image.mp e
      obtain ⟨T,t,xt⟩ := mem_biUnion.mp (cover.symm ▸ xS)
      exact mem_biUnion.mpr ⟨T.image f,mem_image.mpr ⟨T,t,rfl⟩,mem_image.mpr ⟨x,xt,rfl⟩⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def selected {V : Type*} (a b x y : V) : Prop :=
  (x=a∧y=b)∨(x=b∧y=a)

def target (G : SimpleGraph V) (a b c d e f : V) : SimpleGraph V :=
  omitEdge (omitEdge (omitEdge G a b) c d) e f

abbrev xh : V⊕Bool := .inr false
abbrev yh : V⊕Bool := .inr true

/-- Exact transportation across the usual two-disjoint-edge handle
after the remote packing has been found. This theorem needs only the
listed host adjacencies, not any assumption on unknown packings. -/
theorem transfer (G : SimpleGraph V) (H : SimpleGraph (V⊕Bool))
    (a b c d e f : V)
    (old : ∀ u v : V,H.Adj (.inl u) (.inl v) ↔
        G.Adj u v∧¬selected a b u v∧¬selected c d u v)
    (h : FactorOn (omitEdge H (.inl e) (.inl f)) ((univ.erase xh).erase yh)) :
    FactorOn (target G a b c d e f) univ := by
  let S : Finset (V⊕Bool) := (univ.erase xh).erase yh
  let back : V⊕Bool→V := Sum.elim id (fun _=>a)
  have inj : Set.InjOn back (↑S : Set (V⊕Bool)) := by
    rintro (u|u) hu (v|v) hv eq
    · exact congrArg Sum.inl eq
    · cases v <;> simp [S,xh,yh] at hv
    · cases u <;> simp [S,xh,yh] at hu
    · cases u <;> simp [S,xh,yh] at hu
  have keep (u : V⊕Bool) (hu : u∈S) (v : V⊕Bool) (hv : v∈S)
      (uv : (omitEdge H (.inl e) (.inl f)).Adj u v) :
      (target G a b c d e f).Adj (back u) (back v) := by
    cases u with
    | inr u => cases u <;> simp [S,xh,yh] at hu
    | inl u =>
      cases v with
      | inr v => cases v <;> simp [S,xh,yh] at hv
      | inl v =>
        obtain ⟨ed,one,two⟩ := (old u v).mp uv.1
        refine ⟨⟨⟨ed,one⟩,two⟩,?_⟩
        rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · exact uv.2 (Or.inl ⟨rfl,rfl⟩)
        · exact uv.2 (Or.inr ⟨rfl,rfl⟩)
  have lifted := factor_image_injOn back inj keep h
  have qs : S.image back=univ := by
    apply eq_univ_of_forall
    intro u
    exact mem_image.mpr ⟨Sum.inl u,by simp [S,xh,yh],rfl⟩
  rwa [qs] at lifted

/-- The absence of adjacencies to the synthetic root follows from
edge disjointness. The omitted edge must be unaltered by the first
two subdivisions; it is assumed explicitly through the exact old
edge relation. -/
theorem use_remote_promise (G : SimpleGraph V) (H : SimpleGraph (V⊕Bool))
    (a b c d e f : V)
    (old : ∀ u v : V,H.Adj (.inl u) (.inl v) ↔
        G.Adj u v∧¬selected a b u v∧¬selected c d u v)
    (firstPole : ∀ u : V,H.Adj xh (.inl u)↔u=a∨u=b)
    (link : H.Adj xh yh) (ef : G.Adj e f)
    (far : e≠a∧e≠b∧f≠a∧f≠b) (another : ¬selected c d e f)
    (promise : ∀ x y u v : V⊕Bool,H.Adj x y→H.Adj u v→Remote H x u v→
      FactorOn (omitEdge H u v) ((univ.erase x).erase y)) :
    FactorOn (target G a b c d e f) univ := by
  have keep : ¬selected a b e f := fun h=>h.elim (fun v=>far.1 v.1) (fun v=>far.2.1 v.1)
  have actual : H.Adj (.inl e) (.inl f) := (old e f).mpr ⟨ef,keep,another⟩
  have remote : Remote H xh (.inl e) (.inl f) := by
    refine ⟨Sum.noConfusion,Sum.noConfusion,?_,?_⟩
    · intro h
      exact (firstPole e).mp h |>.elim far.1 far.2.1
    · intro h
      exact (firstPole f).mp h |>.elim far.2.2.1 far.2.2.2
  exact transfer G H a b c d e f old (promise xh yh _ _ link actual remote)

#print axioms factor_image_injOn
#print axioms transfer
#print axioms use_remote_promise
end
end KelmansCactus.AtomicBridge.RemoteT2AvoidThree
