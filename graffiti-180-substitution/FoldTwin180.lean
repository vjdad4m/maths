import DeletionClass180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Add a twin of v, with or without the edge joining the pair. -/
noncomputable def twinPorts (G : SimpleGraph V) (v : V) (join : Bool) : Finset V :=
  univ.filter (fun z => G.Adj z v ∨ (join=true ∧ z=v))

noncomputable def foldTwin (v : V) : V⊕Unit→V := Sum.elim id (fun _ => v)

theorem twin_bags (G : SimpleGraph V) (v : V) (join : Bool) :
    Bags (ear G (twinPorts G v join)) G (foldTwin v) := by
  classical
  refine ⟨fun i => ⟨.inl i,rfl⟩,?_⟩
  rintro (x|⟨⟩) (y|⟨⟩) ne
  · exact Iff.rfl
  · change x≠v at ne
    change x∈twinPorts G v join ↔ G.Adj x v
    simp [twinPorts,ne]
  · change v≠y at ne
    change y∈twinPorts G v join ↔ G.Adj v y
    simp [twinPorts,ne.symm,adj_comm]
  · exact (ne rfl).elim

theorem twin_nonclique (G : SimpleGraph V) (v i : V) (join : Bool) :
    NonCliqueBag (ear G (twinPorts G v join)) (foldTwin v) i ↔ i=v ∧ join=false := by
  classical
  constructor
  · rintro ⟨x,y,xi,yi,ne,no⟩
    rcases x with x|⟨⟩ <;> rcases y with y|⟨⟩
    · exact (ne (congrArg Sum.inl (xi.trans yi.symm))).elim
    · change x=i at xi; change v=i at yi
      subst x; subst i
      refine ⟨rfl,?_⟩
      change v∉twinPorts G v join at no
      cases join <;> simp_all [twinPorts]
    · change y=i at yi; change v=i at xi
      subst y; subst i
      refine ⟨rfl,?_⟩
      change v∉twinPorts G v join at no
      cases join <;> simp_all [twinPorts]
    · exact (ne rfl).elim
  · rintro ⟨rfl,rfl⟩
    refine ⟨.inl i,.inr (),rfl,rfl,by simp,?_⟩
    change i∉twinPorts G i false
    simp [twinPorts]

/-- For false twins the cover hypothesis is exactly extendibility of
the split vertex into some maximum induced bipartite witness. -/
theorem twin_cover_iff (G : SimpleGraph V) (v : V) (join : Bool) :
    CoversBags (ear G (twinPorts G v join)) G (foldTwin v) ↔
      join=true ∨ ∃ Z : Finset V,TwoColor G Z ∧ Z.card=bipartiteNum G ∧ v∈Z := by
  classical
  constructor
  · intro cov
    cases join with
    | true => exact Or.inl rfl
    | false =>
      obtain ⟨Z,col,sz,cover⟩ := cov {v} (by simp [Indep])
      exact Or.inr ⟨Z,col,sz,cover _ (mem_singleton_self _) ((twin_nonclique ..).mpr ⟨rfl,rfl⟩)⟩
  · intro ok I _
    rcases ok with linked|⟨Z,col,sz,vm⟩
    · obtain ⟨Z,col,sz⟩ := optB G
      refine ⟨Z,col,sz,fun i _ nc => ?_⟩
      have h := ((twin_nonclique G v i join).mp nc).2
      simp [linked] at h
    · exact ⟨Z,col,sz,fun i _ nc => ((twin_nonclique ..).mp nc).1.symm ▸ vm⟩

/-- A true twin always allows strict descent. A false twin also does
when the split vertex belongs to some maximum induced bipartite set. -/
theorem twin_descent (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (v : V) (join : Bool) (ok : join=true ∨ ∃ Z : Finset V,TwoColor G Z ∧ Z.card=bipartiteNum G ∧ v∈Z)
    (r : V⊕Unit) (p : Bool) :
    let H := ear G (twinPorts G v join)
    ¬localBound H r (parity H r p) → Fintype.card V<Fintype.card (V⊕Unit) ∧
      ¬localBound G (foldTwin v r) (parity G (foldTwin v r) p) := by
  intro H bad
  have proper : ¬Function.Injective (foldTwin v) := fun inj =>
    Sum.noConfusion (inj (a₁:=.inl v) (a₂:=.inr ()) rfl)
  exact (twin_bags G v join).strictDescent ((twin_cover_iff ..).mpr ok) gc hn proper r p bad

theorem twin_passes (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (v : V) (join : Bool) (ok : join=true ∨ ∃ Z : Finset V,TwoColor G Z ∧ Z.card=bipartiteNum G ∧ v∈Z)
    (degree : 1<(twinPorts G v join).card) (p : Bool) (base : localBound G v (parity G v p)) :
    Passes G (twinPorts G v join) degree p := by
  apply (deleted_root_iff G gc hn _ degree p).mp
  exact (twin_bags G v join).rooted ((twin_cover_iff ..).mpr ok) gc (by omega) (.inr ()) p base

#print axioms twin_bags
#print axioms twin_nonclique
#print axioms twin_cover_iff
#print axioms twin_descent
#print axioms twin_passes
end Minimal180.Substitution
