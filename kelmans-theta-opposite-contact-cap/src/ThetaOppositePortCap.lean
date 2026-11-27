import ThetaRootContactCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaOppositePortCap
open SquareCap (SmallTrivial FactorOn omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach attach_degree_outside)
open ThetaFiveExterior (live liveIdx target_shape)
open ThetaRootContactSplice (stem)
open ThetaRootContactCap (eligible paired neighborWire live_index_not3)
noncomputable section
universe u

variable {V : Type u}

private def perm (s i : Bool) : Equiv.Perm Port := Equiv.swap (liveIdx s (!i)) 3

def ports (p : Port↪V) (s i : Bool) : Port↪V := (perm s i).toEmbedding.trans p

private theorem perm_a : ∀ s i : Bool,perm s i (liveIdx s i)=liveIdx s i := by decide
private theorem perm_b : ∀ s i : Bool,perm s i (liveIdx s (!i))=3 := by decide
private theorem perm_3 : ∀ s i : Bool,perm s i 3=liveIdx s (!i) := by decide
private theorem b_eligible : ∀ s i : Bool,eligible (liveIdx s i) (liveIdx s (!i)) := by decide

private theorem other_live : ∀ s i : Bool,∀ j : Port,
    eligible (liveIdx s i) j → j≠liveIdx s (!i) →
    perm s i j=liveIdx (!s) false ∨ perm s i j=liveIdx (!s) true := by decide

@[simp] theorem ports_a (p : Port↪V) (s i : Bool) :
    ports p s i (liveIdx s i)=p (liveIdx s i) := congrArg p (perm_a s i)
@[simp] theorem ports_b (p : Port↪V) (s i : Bool) :
    ports p s i (liveIdx s (!i))=p 3 := congrArg p (perm_b s i)
@[simp] theorem ports_3 (p : Port↪V) (s i : Bool) :
    ports p s i 3=p (liveIdx s (!i)) := congrArg p (perm_3 s i)

def candidate (G : SimpleGraph V) (p : Port↪V) (s i : Bool) : SimpleGraph (V⊕Unit) :=
  ThetaRootContactCap.cap G (ports p s i) (liveIdx s i) (live_index_not3 s i)

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V) (s i : Bool) :
    DecidableRel (candidate G p s i).Adj :=
  inferInstanceAs (DecidableRel (ThetaRootContactCap.cap G (ports p s i)
    (liveIdx s i) (live_index_not3 s i)).Adj)

private theorem same_count [DecidableEq V] (p : Port↪V) (s i : Bool) (x : V) :
    ((univ : Finset Port).filter (fun j=>ports p s i j=x)).card =
    ((univ : Finset Port).filter (fun j=>p j=x)).card := by
  apply card_bij (fun j _=>perm s i j)
  · intro j xj
    simpa [ports] using xj
  · intro j _ k _ e
    exact (perm s i).injective e
  · intro j xj
    refine ⟨(perm s i).symm j,?_,(perm s i).apply_symm_apply j⟩
    simpa [ports] using xj

variable [Fintype V] [DecidableEq V]

theorem candidate_cubic (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V)
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3) (s i : Bool)
    (safe : ¬G.Adj (p (liveIdx s i)) (p (liveIdx s (!i)))) :
    ∀ v,(candidate G p s i).degree v=3 := by
  have sa : ¬G.Adj (ports p s i (liveIdx s i)) (ports p s i 3) := by simpa using safe
  intro v
  cases v with
  | inr w => exact ThetaRootContactCap.degree_stem G (ports p s i) (live_index_not3 s i)
  | inl x =>
    change (ThetaRootContactCap.cap G (ports p s i) (liveIdx s i)
      (live_index_not3 s i)).degree (Sum.inl x)=3
    rw [ThetaRootContactCap.degree_old G (ports p s i) (live_index_not3 s i) sa,
      same_count]
    letI : DecidableRel (attach G ThetaCase.theta p ThetaCase.arm).Adj :=
      ‹DecidableRel (ThetaCase.ambient G p).Adj›
    have c := cub (Sum.inl x)
    change (attach G ThetaCase.theta p ThetaCase.arm).degree (Sum.inl x)=3 at c
    rwa [attach_degree_outside] at c

theorem lift_certified_cap {G : SimpleGraph V} {p : Port↪V}
    (s i : Bool) (y : V)
    (fact : FactorOn (omitEdge (candidate G p s i) stem (Sum.inl (p 3)))
      (univ.erase (Sum.inl (p (liveIdx s i))))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p (liveIdx s i))) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  let C := omitEdge (candidate G p s i) stem (Sum.inl (p 3))
  refine ThetaRootContactSplice.lift_after_removed_terminal (C:=C) s i
    (target_shape p (p (liveIdx s i)) y) ?_ ?_ fact
  · intro z hz
    cases z with
    | inr _ => exact hz.1.elim
    | inl w =>
      obtain ⟨j,elig,e⟩ : neighborWire (ports p s i) (liveIdx s i) w := hz.1
      have nb : j≠liveIdx s (!i) := by
        intro h
        apply hz.2
        rw [h,ports_b] at e
        exact Or.inl ⟨rfl,congrArg Sum.inl e.symm⟩
      rcases other_live s i j elig nb with h|h
      · exact Or.inl (congrArg Sum.inl (e.symm.trans (congrArg p h)))
      · exact Or.inr (congrArg Sum.inl (e.symm.trans (congrArg p h)))
  · intro x z xa za e
    obtain real|broken : G.Adj x z ∨ paired (ports p s i) (liveIdx s i) x z := e.1
    · refine ⟨real,?_⟩
      rintro (⟨xq,_⟩|⟨_,zq⟩)
      · exact xa (Sum.inl_injective xq)
      · exact za (Sum.inl_injective zq)
    · exact (broken.elim (fun k=>xa (k.1.trans (ports_a p s i)))
        (fun k=>za (k.2.trans (ports_a p s i)))).elim

/-- Alternative one-cap: pair the removed live terminal with its
opposite live contact, then block the original root-contact cap wire.
The true exterior omission again disappears when the terminal is removed. -/
theorem incident_exterior
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (s i : Bool) (safe : ¬G.Adj (p (liveIdx s i)) (p (liveIdx s (!i))))
    (valid : SmallTrivial (candidate G p s i)) (y : V) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p (liveIdx s i))) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  let C := candidate G p s i
  have cc : ∀ v,C.degree v=3 := candidate_cubic G p cub s i safe
  have wire : C.Adj stem (Sum.inl (p 3)) :=
    ⟨liveIdx s (!i),b_eligible s i,ports_b p s i⟩
  have big : 5≤Fintype.card V := by simpa using (Fintype.card_le_of_injective p p.injective)
  have n1 : Fintype.card (V⊕Unit)=Fintype.card V+1 := by simp
  have n7 : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have conn := three_connected_of_small_trivial C cc (by omega) valid
  have f := smaller (V⊕Unit) C (by omega) cc conn valid (by omega)
    (Sum.inl (p (liveIdx s i))) stem (Sum.inl (p 3)) wire
  exact lift_certified_cap s i y f

#print axioms candidate_cubic
#print axioms lift_certified_cap
#print axioms incident_exterior
end
end KelmansCactus.AtomicBridge.ThetaOppositePortCap
