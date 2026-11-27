import RemoteT2AvoidThree
import RemoteT2CompletionTransfer
import RemoteT2ForcedChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3RootTransfer
open SquareCap (FactorOn HasFactor)
open RemoteT2CompletionTransfer (marked eraseEdge SmallerIsolatedAvoid3)
open RemoteT2ForcedChain (factor_iff_strip_leaf_chain)
open RemoteT2AvoidThree (factor_image_injOn)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev sPole : V⊕Bool := Sum.inr false
abbrev tPole : V⊕Bool := Sum.inr true

def strippedHost (H : SimpleGraph (V⊕Bool)) (w r s : V) : SimpleGraph (V⊕Bool) :=
  eraseEdge (eraseEdge (eraseEdge H sPole (Sum.inl w)) tPole (Sum.inl r)) tPole (Sum.inl s)

/-- Generic graph transport for a two-edge handle with a prescribed
original root. On deleting the marked three wires, T has unique
neighbor S, and S has unique other neighbor X. The forced X-S-T tile
strips precisely the root X together with both synthetic vertices.
The selected edge r-s is already absent on the old side. -/
theorem strip_root_handle (G : SimpleGraph V) (H : SimpleGraph (V⊕Bool))
    (x w r s : V) (xw : x≠w) (rs : r≠s)
    (old : ∀ a b : V,H.Adj (.inl a) (.inl b) ↔
       G.Adj a b ∧ ¬marked x w a b ∧ ¬marked r s a b)
    (sl : ∀ a : V,H.Adj sPole (.inl a) ↔ a=x∨a=w)
    (tl : ∀ a : V,H.Adj tPole (.inl a) ↔ a=r∨a=s)
    (link : H.Adj sPole tPole)
    (f : HasFactor (strippedHost H w r s)) :
    FactorOn (eraseEdge G r s) (univ.erase x) := by
  classical
  let D := strippedHost H w r s
  have tS : D.Adj tPole sPole := by
    change ((H.Adj tPole sPole ∧ ¬marked sPole (Sum.inl w) tPole sPole) ∧
      ¬marked tPole (Sum.inl r) tPole sPole) ∧ ¬marked tPole (Sum.inl s) tPole sPole
    simp [marked,link.symm]
  have sX : D.Adj sPole (Sum.inl x) := by
    change ((H.Adj sPole (Sum.inl x) ∧ ¬marked sPole (Sum.inl w) sPole (Sum.inl x)) ∧
      ¬marked tPole (Sum.inl r) sPole (Sum.inl x)) ∧ ¬marked tPole (Sum.inl s) sPole (Sum.inl x)
    simp [marked,sl,xw]
  have onlyT : ∀ a∈(univ : Finset (V⊕Bool)),D.Adj tPole a→a=sPole := by
    rintro (a|a) _ h
    · change ((H.Adj tPole (Sum.inl a) ∧ _) ∧ ¬marked tPole (Sum.inl r) tPole (Sum.inl a)) ∧
        ¬marked tPole (Sum.inl s) tPole (Sum.inl a) at h
      rcases (tl a).mp h.1.1.1 with rfl|rfl
      · exact (h.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
      · exact (h.2 (Or.inl ⟨rfl,rfl⟩)).elim
    · cases a
      · rfl
      · exact (D.loopless _ h).elim
  have onlyS : ∀ a∈(univ : Finset (V⊕Bool)),D.Adj sPole a→a=tPole∨a=Sum.inl x := by
    rintro (a|a) _ h
    · change ((H.Adj sPole (Sum.inl a) ∧ ¬marked sPole (Sum.inl w) sPole (Sum.inl a)) ∧ _) ∧ _ at h
      rcases (sl a).mp h.1.1.1 with rfl|rfl
      · exact Or.inr rfl
      · exact (h.1.1.2 (Or.inl ⟨rfl,rfl⟩)).elim
    · cases a
      · exact (D.loopless _ h).elim
      · exact Or.inl rfl
  let S : Finset (V⊕Bool) := univ \ {tPole,sPole,Sum.inl x}
  have f' : FactorOn D S := (factor_iff_strip_leaf_chain (mem_univ _) (mem_univ _)
    (mem_univ _) Sum.noConfusion tS sX onlyT onlyS).mp f
  let back : V⊕Bool→V := Sum.elim id (fun _=>x)
  have inj : Set.InjOn back (↑S : Set (V⊕Bool)) := by
    rintro (a|a) ha (b|b) hb h
    · exact congrArg Sum.inl h
    · cases b <;> simp [S] at hb
    · cases a <;> simp [S] at ha
    · cases a <;> simp [S] at ha
  have keep : ∀ a∈S,∀ b∈S,D.Adj a b→(eraseEdge G r s).Adj (back a) (back b) := by
    rintro (a|a) ha (b|b) hb h
    · have p : H.Adj (Sum.inl a) (Sum.inl b) := h.1.1.1
      have e := (old a b).mp p
      exact ⟨e.1,e.2.2⟩
    · cases b <;> simp [S] at hb
    · cases a <;> simp [S] at ha
    · cases a <;> simp [S] at ha
  have cover : S.image back =univ.erase x := by
    ext z
    constructor
    · intro m
      obtain ⟨a,am,eq⟩ := mem_image.mp m
      cases a with
      | inr a => cases a <;> simp [S] at am
      | inl a =>
        simp only [back,Sum.elim_inl] at eq
        subst z
        simpa [S] using am
    · intro m
      exact mem_image.mpr ⟨Sum.inl z,by simpa [S] using m,rfl⟩
  rw [←cover]
  exact factor_image_injOn back inj keep f'

/-- The domain geometry can be supplied by the published disjoint
two-edge handle theorem. Here its exact adjacency and cyclic-four
conclusions are the explicit inputs. The only factor promise is the
order-bounded isolated-edge-pattern Avoid3 on that handle. -/
theorem use_smaller_avoid3 (G : SimpleGraph V) (H : SimpleGraph (V⊕Bool))
    [DecidableRel H.Adj] (x w r s : V) (xw : x≠w) (rs : r≠s)
    (old : ∀ a b : V,H.Adj (.inl a) (.inl b) ↔
       G.Adj a b ∧ ¬marked x w a b ∧ ¬marked r s a b)
    (sl : ∀ a : V,H.Adj sPole (.inl a) ↔ a=x∨a=w)
    (tl : ∀ a : V,H.Adj tPole (.inl a) ↔ a=r∨a=s)
    (link : H.Adj sPole tPole) (wr : w≠r) (ws : w≠s)
    (n : ℕ) (bound : Fintype.card (V⊕Bool)<n) (order : Fintype.card (V⊕Bool)%6=0)
    (cub : ∀ z,H.degree z=3) (conn : SquareCap.ThreeConnected H) (cut : SquareCap.SmallTrivial H)
    (smaller : SmallerIsolatedAvoid3.{u} n) :
    FactorOn (eraseEdge G r s) (univ.erase x) := by
  apply strip_root_handle G H x w r s xw rs old sl tl link
  exact smaller (V⊕Bool) H bound cub conn cut order sPole (Sum.inl w)
    tPole (Sum.inl r) tPole (Sum.inl s)
    ((sl w).mpr (Or.inr rfl)) ((tl r).mpr (Or.inl rfl)) ((tl s).mpr (Or.inr rfl))
    (fun h=>Bool.false_ne_true (Sum.inr.inj h)) Sum.noConfusion Sum.noConfusion (fun h=>wr (Sum.inl.inj h))
    (fun h=>Bool.false_ne_true (Sum.inr.inj h)) Sum.noConfusion Sum.noConfusion (fun h=>ws (Sum.inl.inj h))
    (fun h=>h.elim (fun h=>rs (Sum.inl.inj h.2).symm) (fun h=>Sum.noConfusion h.1))

#print axioms strip_root_handle
#print axioms use_smaller_avoid3
end KelmansCactus.AtomicBridge.RemoteAvoid3RootTransfer
