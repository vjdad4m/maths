import HandleCuts
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3SixTester
open SquareCap (Port cap coord SmallTrivial)
open HandleExtension (Edges)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def wireIndex (k a s : Bool) : Port := if k then (s,a) else (a,s)

theorem wireIndex_coord (k a s : Bool) : coord k (wireIndex k a s)=s := by
  cases k <;> rfl

theorem wireIndex_eq (k a b s t : Bool) :
    wireIndex k a s=wireIndex k b t ↔ a=b∧s=t := by
  cases k <;> simp [wireIndex,and_comm]

abbrev Stage (V : Type u) := ((V⊕Bool)⊕Bool)⊕Bool
abbrev out (v : V) : Stage V := .inl (.inl (.inl v))
abbrev oldPole (s : Bool) : Stage V := .inl (.inl (.inr s))

def contact (a s : Bool) : Stage V :=
  if a then .inr s else .inl (.inr s)

omit [Fintype V] [DecidableEq V] in
private theorem capwire (G : SimpleGraph V) (p : Port↪V) (k a s : Bool) :
    (cap G p k).Adj (Sum.inr s) (Sum.inl (p (wireIndex k a s))) :=
  ⟨wireIndex k a s,rfl,wireIndex_coord k a s⟩

omit [Fintype V] [DecidableEq V] in
def first (G : SimpleGraph V) (p : Port↪V) (k : Bool) : Edges (cap G p k) where
  a s := Sum.inr s
  b s := Sum.inl (p (wireIndex k false s))
  edge s := capwire G p k false s
  separated := by
    intro s t z h b
    rcases h with rfl|rfl
    · rcases b with eq|eq
      · exact Sum.inr.inj eq
      · exact Sum.noConfusion eq
    · rcases b with eq|eq
      · exact Sum.noConfusion eq
      · exact ((wireIndex_eq k false false s t).mp (p.injective (Sum.inl.inj eq))).2

omit [Fintype V] [DecidableEq V] in
def second (G : SimpleGraph V) (p : Port↪V) (k : Bool) : Edges (first G p k).host where
  a s := Sum.inl (Sum.inr s)
  b s := Sum.inl (Sum.inl (p (wireIndex k true s)))
  edge s := by
    refine ⟨capwire G p k true s,?_⟩
    rintro ⟨a,⟨_,h⟩|⟨h,_⟩⟩
    · have eq := (wireIndex_eq k true false s a).mp (p.injective (Sum.inl.inj h))
      exact (by decide : true≠false) eq.1
    · exact Sum.noConfusion h
  separated := by
    intro s t z h b
    rcases h with rfl|rfl
    · rcases b with eq|eq
      · exact Sum.inr.inj (Sum.inl.inj eq)
      · exact Sum.noConfusion (Sum.inl.inj eq)
    · rcases b with eq|eq
      · exact Sum.noConfusion (Sum.inl.inj eq)
      · exact ((wireIndex_eq k true true s t).mp (p.injective (Sum.inl.inj (Sum.inl.inj eq)))).2

omit [Fintype V] [DecidableEq V] in
abbrev tester (G : SimpleGraph V) (p : Port↪V) (k : Bool) : SimpleGraph (Stage V) :=
  (second G p k).host

omit [DecidableEq V] in
theorem tester_card : Fintype.card (Stage V)=Fintype.card V+6 := by
  simp [Stage]

theorem tester_cubic (G : SimpleGraph V) (p : Port↪V) (k : Bool) [DecidableRel (cap G p k).Adj]
    (h : ∀ v,(cap G p k).degree v=3) : ∀ z,(tester G p k).degree z=3 := by
  exact (second G p k).cubic ((first G p k).cubic h)

theorem tester_small (G : SimpleGraph V) (p : Port↪V) (k : Bool) [DecidableRel (cap G p k).Adj]
    (h : ∀ v,(cap G p k).degree v=3) (small : SmallTrivial (cap G p k)) :
    SmallTrivial (tester G p k) := by
  exact (second G p k).preserves_small_trivial ((first G p k).cubic h)
    ((first G p k).preserves_small_trivial h small)

omit [Fintype V] [DecidableEq V] in
theorem tester_old_iff (G : SimpleGraph V) (p : Port↪V) (k : Bool) (u v : V) :
    (tester G p k).Adj (out u) (out v) ↔ G.Adj u v := by
  constructor
  · intro e
    exact e.1.1
  · intro e
    refine ⟨⟨e,?_⟩,?_⟩
    · rintro ⟨s,⟨l,_⟩|⟨_,r⟩⟩
      · exact Sum.noConfusion l
      · exact Sum.noConfusion r
    · rintro ⟨s,⟨l,_⟩|⟨_,r⟩⟩
      · exact Sum.noConfusion (Sum.inl.inj l)
      · exact Sum.noConfusion (Sum.inl.inj r)

omit [Fintype V] [DecidableEq V] in
theorem tester_contact_iff (G : SimpleGraph V) (p : Port↪V) (k a s : Bool) (u : V) :
    (tester G p k).Adj (out u) (contact a s) ↔ u=p (wireIndex k a s) := by
  cases a
  · constructor
    · intro h
      have hh : (first G p k).host.Adj (Sum.inl (Sum.inl u)) (Sum.inr s) := h.1
      rcases hh with e|e
      · exact Sum.noConfusion e
      · exact Sum.inl.inj e
    · intro h
      refine ⟨Or.inr (congrArg Sum.inl h),?_⟩
      rintro ⟨b,⟨_,e⟩|⟨_,e⟩⟩ <;> exact Sum.noConfusion e
  · change (Sum.inl (Sum.inl u) = Sum.inl (Sum.inr s) ∨
      Sum.inl (Sum.inl u) = Sum.inl (Sum.inl (p (wireIndex k true s)))) ↔ _
    simp

omit [Fintype V] [DecidableEq V] in
theorem no_old_pole_contact (G : SimpleGraph V) (p : Port↪V) (k s : Bool) (v : V) :
    ¬(tester G p k).Adj (out v) (oldPole s) := by
  intro h
  have ed : (cap G p k).Adj (Sum.inl v) (Sum.inr s) := h.1.1
  obtain ⟨i,iv,is⟩ := ed
  have list : i=wireIndex k false s ∨ i=wireIndex k true s := by
    rcases i with ⟨a,b⟩
    cases k <;> cases a <;> cases b <;> cases s <;> simp_all [coord,wireIndex]
  rcases list with p0|p1
  · apply h.1.2
    exact ⟨s,Or.inr ⟨congrArg Sum.inl (iv.symm.trans (congrArg p p0)),rfl⟩⟩
  · apply h.2
    exact ⟨s,Or.inr ⟨congrArg Sum.inl (congrArg Sum.inl (iv.symm.trans (congrArg p p1))),rfl⟩⟩

#print axioms tester_cubic
#print axioms tester_small
#print axioms tester_old_iff
#print axioms tester_contact_iff
#print axioms no_old_pole_contact
end KelmansCactus.AtomicBridge.RemoteAvoid3SixTester
