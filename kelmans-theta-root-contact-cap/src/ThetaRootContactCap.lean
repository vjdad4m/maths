import ThetaRootContactSplice
import ThetaFiveExterior
import EarCase

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaRootContactCap
open SquareCap (SmallTrivial FactorOn omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach attach_degree_outside)
open ThetaFiveExterior (live liveIdx target_shape)
open ThetaFiveRing (outer)
open ThetaRootContactSplice (stem)
noncomputable section
universe u

variable {V : Type u}

def eligible (a j : Port) : Prop := j≠a ∧ j≠3
instance (a j : Port) : Decidable (eligible a j) := inferInstanceAs (Decidable (j≠a∧j≠3))

def neighborWire (p : Port↪V) (a : Port) (x : V) : Prop :=
  ∃ j : Port, eligible a j ∧ p j=x

instance [DecidableEq V] (p : Port↪V) (a : Port) (x : V) :
    Decidable (neighborWire p a x) := inferInstanceAs (Decidable (∃ j : Port,eligible a j ∧ p j=x))

def paired (p : Port↪V) (a : Port) (x y : V) : Prop :=
  (x=p a∧y=p 3)∨(x=p 3∧y=p a)

instance [DecidableEq V] (p : Port↪V) (a : Port) (x y : V) :
    Decidable (paired p a x y) := inferInstanceAs (Decidable ((x=p a∧y=p 3)∨(x=p 3∧y=p a)))

def edge (G : SimpleGraph V) (p : Port↪V) (a : Port) :
    (V⊕Unit)→(V⊕Unit)→Prop
  | .inl x,.inl y => G.Adj x y ∨ paired p a x y
  | .inl x,.inr _ => neighborWire p a x
  | .inr _,.inl x => neighborWire p a x
  | .inr _,.inr _ => False

/-- Complete the original five-pole by adding one vertex at the
three unpaired contacts and the artificial terminal/root-contact edge. -/
def cap (G : SimpleGraph V) (p : Port↪V) (a : Port) (ne : a≠3) : SimpleGraph (V⊕Unit) where
  Adj := edge G p a
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h.elim (fun e=>Or.inl e.symm) (fun z=>Or.inr (z.elim
        (fun e=>Or.inr ⟨e.2,e.1⟩) (fun e=>Or.inl ⟨e.2,e.1⟩)))
    · exact h
    · exact h
    · exact h
  loopless := by
    intro x h
    cases x with
    | inr _ => exact h
    | inl x =>
      rcases h with e|⟨a,b⟩|⟨a,b⟩
      · exact G.loopless x e
      · exact ne (p.injective (a.symm.trans b))
      · exact ne (p.injective (b.symm.trans a))

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V)
    (a : Port) (n : a≠3) : DecidableRel (cap G p a n).Adj := by
  intro x y
  cases x <;> cases y
  · exact inferInstanceAs (Decidable (G.Adj _ _ ∨ paired _ _ _ _))
  · exact inferInstanceAs (Decidable (neighborWire _ _ _))
  · exact inferInstanceAs (Decidable (neighborWire _ _ _))
  · exact inferInstanceAs (Decidable False)

private theorem eligible_not_a (p : Port↪V) (a : Port) : ¬neighborWire p a (p a) := by
  rintro ⟨j,h,e⟩
  exact h.1 (p.injective e)

private theorem eligible_not_three (p : Port↪V) (a : Port) : ¬neighborWire p a (p 3) := by
  rintro ⟨j,h,e⟩
  exact h.2 (p.injective e)

variable [DecidableEq V]

private def delta (p : Port↪V) (a : Port) (x : V) : Finset (V⊕Unit) :=
  if x=p a then {Sum.inl (p 3)} else if x=p 3 then {Sum.inl (p a)}
  else if neighborWire p a x then {stem} else ∅

private theorem delta_old (p : Port↪V) {a : Port} (a3 : a≠3) (x y : V) :
    Sum.inl y ∈ delta p a x ↔ paired p a x y := by
  have s : p a≠p 3 := fun h=>a3 (p.injective h)
  by_cases h : x=p a
  · subst x; simp [delta,paired,s]
  by_cases j : x=p 3
  · simp [delta,paired,h,j,Ne.symm a3]
  by_cases k : neighborWire p a x <;> simp [delta,paired,h,j,k,stem]

private theorem delta_stem (p : Port↪V) (a : Port) (x : V) :
    stem∈delta p a x ↔ neighborWire p a x := by
  by_cases h : x=p a
  · subst x; simp [delta,stem,eligible_not_a]
  by_cases j : x=p 3
  · subst x; simp [delta,h,stem,eligible_not_three]
  by_cases k : neighborWire p a x <;> simp [delta,h,j,k,stem]

private theorem delta_card (p : Port↪V) (a : Port) (x : V) :
    (delta p a x).card = ((univ : Finset Port).filter (fun j=>p j=x)).card := by
  by_cases exist : ∃ j : Port,p j=x
  · obtain ⟨j,rfl⟩ := exist
    have eq : (univ : Finset Port).filter (fun k=>p k=p j)={j} := by
      ext k; simp [p.injective.eq_iff]
    rw [eq,card_singleton]
    by_cases h : j=a
    · subst j; simp [delta]
    by_cases k : j=3
    · subst j
      have not : p 3≠p a := fun e=>h (p.injective e)
      simp [delta,not]
    · have yes : neighborWire p a (p j) := ⟨j,⟨h,k⟩,rfl⟩
      have h' : p j≠p a := fun e=>h (p.injective e)
      have k' : p j≠p 3 := fun e=>k (p.injective e)
      simp [delta,h',k',yes]
  · have empty : (univ : Finset Port).filter (fun j=>p j=x)=∅ := by
      ext j; simp only [mem_filter,mem_univ,true_and,not_mem_empty,iff_false]
      exact fun h=>exist ⟨j,h⟩
    rw [empty]
    have no : ¬neighborWire p a x := fun ⟨j,_,h⟩=>exist ⟨j,h⟩
    have qa : x≠p a := fun h=>exist ⟨a,h.symm⟩
    have q3 : x≠p 3 := fun h=>exist ⟨3,h.symm⟩
    simp [delta,qa,q3,no]

variable [Fintype V]

theorem degree_old (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V)
    {a : Port} (an : a≠3) (safe : ¬G.Adj (p a) (p 3)) (x : V) :
    (cap G p a an).degree (Sum.inl x) =
      G.degree x + ((univ : Finset Port).filter (fun j=>p j=x)).card := by
  let E : V↪(V⊕Unit) := ⟨Sum.inl,Sum.inl_injective⟩
  let old := (G.neighborFinset x).map E
  have old_mem (y : V) : Sum.inl y∈old ↔ G.Adj x y := by
    simp [old,E,mem_map,mem_neighborFinset]
  have no_stem : (stem : V⊕Unit)∉old := by simp [old,E,mem_map,stem]
  have eq : (cap G p a an).neighborFinset (Sum.inl x) = old ∪ delta p a x := by
    ext z
    rw [mem_neighborFinset,mem_union]
    cases z with
    | inl y =>
      change G.Adj x y ∨ paired p a x y ↔ _
      rw [old_mem,delta_old p an]
    | inr v =>
      cases v
      change neighborWire p a x ↔ stem ∈ old ∨ stem∈delta p a x
      simp [no_stem,delta_stem]
  have sep : Disjoint old (delta p a x) := by
    rw [disjoint_left]
    intro z hz ds
    cases z with
    | inr v => cases v; exact no_stem hz
    | inl y =>
      have e := (old_mem y).mp hz
      rcases (delta_old p an x y).mp ds with ⟨ax,byy⟩|⟨ax,byy⟩
      · exact safe (by simpa [ax,byy] using e)
      · exact safe (by simpa [ax,byy] using e.symm)
  rw [←card_neighborFinset_eq_degree,eq,card_union_of_disjoint sep,delta_card p a]
  simp [old,card_neighborFinset_eq_degree]

theorem degree_stem (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V)
    {a : Port} (an : a≠3) : (cap G p a an).degree stem=3 := by
  let E : Port↪(V⊕Unit) := ⟨fun j=>.inl (p j),fun _ _ h=>p.injective (Sum.inl_injective h)⟩
  let S := (univ : Finset Port).filter (eligible a)
  have eq : (cap G p a an).neighborFinset stem = S.map E := by
    ext z
    rw [mem_neighborFinset,mem_map]
    cases z with
    | inl v => simp [stem,S,E,edge,neighborWire,cap]
    | inr v => simp [stem,S,E,edge,cap]
  rw [←card_neighborFinset_eq_degree,eq,card_map]
  exact (by decide : ∀ a : Port,a≠3 → ((univ : Finset Port).filter (eligible a)).card=3) a an

/-- One-vertex closure has exactly the same degree at every old
exterior point as the true five-wire attachment. -/
theorem cap_cubic (G : SimpleGraph V) [DecidableRel G.Adj] (p : Port↪V)
    [DecidableRel (ThetaCase.ambient G p).Adj] {a : Port} (an : a≠3)
    (safe : ¬G.Adj (p a) (p 3))
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3) :
    ∀ v,(cap G p a an).degree v=3 := by
  intro v
  cases v with
  | inr _ => exact degree_stem G p an
  | inl x =>
    rw [degree_old G p an safe]
    letI : DecidableRel (attach G ThetaCase.theta p ThetaCase.arm).Adj :=
      ‹DecidableRel (ThetaCase.ambient G p).Adj›
    have h := cub (Sum.inl x)
    change (attach G ThetaCase.theta p ThetaCase.arm).degree (Sum.inl x)=3 at h
    rwa [attach_degree_outside] at h

theorem live_index_not3 : ∀ s i : Bool,liveIdx s i≠3 := by decide
private theorem eligible_opposite : ∀ s i : Bool,
    eligible (liveIdx s i) (liveIdx s (!i)) := by decide
private theorem only_other_live : ∀ (s i : Bool) (j : Port),
    eligible (liveIdx s i) j → j≠liveIdx s (!i) →
    j=liveIdx (!s) false ∨ j=liveIdx (!s) true := by decide

/-- Lift any actual factor of the exact cap minus the selected
terminal and opposite wire, without an order or cyclicity premise. -/
theorem lift_certified_cap
    {G : SimpleGraph V} {p : Port↪V} (s i : Bool) (y : V)
    (fact : FactorOn (omitEdge (cap G p (liveIdx s i) (live_index_not3 s i))
      stem (Sum.inl (p (liveIdx s (!i))))) (univ.erase (Sum.inl (p (liveIdx s i))))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p (liveIdx s i))) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  let a := liveIdx s i
  let b := liveIdx s (!i)
  let C := cap G p a (live_index_not3 s i)
  let J := omitEdge C stem (Sum.inl (p b))
  refine ThetaRootContactSplice.lift_after_removed_terminal (C:=J) s i
    (target_shape p (p a) y) ?_ ?_ fact
  · intro z hz
    cases z with
    | inr _ => exact hz.1.elim
    | inl w =>
      obtain ⟨j,elig,wj⟩ : neighborWire p a w := hz.1
      have jb : j≠b := by
        intro h
        apply hz.2
        exact Or.inl ⟨rfl,congrArg Sum.inl (wj.symm.trans (congrArg p h))⟩
      rcases only_other_live s i j elig jb with h|h
      · exact Or.inl (congrArg Sum.inl (wj.symm.trans (congrArg p h)))
      · exact Or.inr (congrArg Sum.inl (wj.symm.trans (congrArg p h)))
  · intro x z xa za e
    obtain real|broken : G.Adj x z ∨ paired p a x z := e.1
    · refine ⟨real,?_⟩
      rintro (⟨xq,_⟩|⟨_,zq⟩)
      · exact xa (Sum.inl_injective xq)
      · exact za (Sum.inl_injective zq)
    · exact (broken.elim (fun q=>xa q.1) (fun q=>za q.2)).elim

/-- If the exact artificial root-contact closure is cyclic-four
and the true exterior omitted edge touches the removed terminal,
smaller cyclic-four F2 suffices. No order-zero avoidance is used.
Removing the terminal erases the artificial and the genuine edge at once;
the smaller factor's prescribed omission suppresses the opposite wire. -/
theorem incident_exterior
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (s i : Bool) (safe : ¬G.Adj (p (liveIdx s i)) (p 3))
    (valid : SmallTrivial (cap G p (liveIdx s i) (live_index_not3 s i)))
    (y : V) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (p (liveIdx s i))) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  let a := liveIdx s i
  let b := liveIdx s (!i)
  let C := cap G p a (live_index_not3 s i)
  let J := omitEdge C stem (Sum.inl (p b))
  have cc : ∀ v,C.degree v=3 := cap_cubic G p (live_index_not3 s i) safe cub
  have wire : C.Adj stem (Sum.inl (p b)) := ⟨b,eligible_opposite s i,rfl⟩
  have big : 5≤Fintype.card V := by simpa using (Fintype.card_le_of_injective p p.injective)
  have n1 : Fintype.card (V⊕Unit)=Fintype.card V+1 := by simp
  have n7 : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have conn := three_connected_of_small_trivial C cc (by omega) valid
  have fact : FactorOn J (univ.erase (Sum.inl (p a))) :=
    smaller (V⊕Unit) C (by omega) cc conn valid (by omega) (Sum.inl (p a)) stem
      (Sum.inl (p b)) wire
  exact lift_certified_cap s i y fact

#print axioms degree_old
#print axioms degree_stem
#print axioms cap_cubic
#print axioms lift_certified_cap
#print axioms incident_exterior
end
end KelmansCactus.AtomicBridge.ThetaRootContactCap
