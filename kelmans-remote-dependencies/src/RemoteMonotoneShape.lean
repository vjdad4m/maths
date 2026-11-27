import RemoteMonotoneDependencies

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteMonotoneShape
open RemoteMonotoneRank RemoteMonotoneCompletion RemoteMonotoneDependencies
open RemoteVacancyReach (Packing OneCleanup)
variable {V : Type*} [DecidableEq V]

private theorem extra_at_most_one {H : Family V} {A B : Finset V}
    (t : Target H A B) (b : B.card≤3) : (B\A).card≤1 := by
  have h := card_sdiff_add_card_inter B A
  rw [inter_comm B A,t.2] at h
  omega

private theorem origin_unique {U H : Family V} {A C T : Finset V}
    (h : T.card≤3) (old : ∀ A∈U,∀ C∈U,A≠C→Disjoint A C)
    (a : A∈U) (c : C∈U) (ta : Target H A T) (tc : Target H C T) : A=C := by
  have p : Target U T A := ⟨a,by rw [inter_comm]; exact ta.2⟩
  have q : Target U T C := ⟨c,by rw [inter_comm]; exact tc.2⟩
  exact target_unique h old p q

/-- In two families of disjoint triples an old tile has at most one
blocking old tile, because its unique target needs only one extra vertex. -/
theorem blocker_unique {H U : Family V} {A C D : Finset V}
    (old : ∀ B∈U,∀ E∈U,B≠E→Disjoint B E)
    (hA : A.card≤3) (hH : ∀ B∈H,B.card≤3)
    (fin : ∀ B∈H,∀ E∈H,B≠E→Disjoint B E)
    (a : A∈U) (bc : Dependency H U A C) (bd : Dependency H U A D) :
    C=D := by
  obtain ⟨B,t,cb⟩:=bc
  obtain ⟨K,k,db⟩:=bd
  have e := target_unique hA fin t k
  subst K
  obtain ⟨x,xb,xc⟩:=Finset.not_disjoint_iff.mp cb.2.2
  obtain ⟨y,yb,yd⟩:=Finset.not_disjoint_iff.mp db.2.2
  have nx : x∉A := Finset.disjoint_left.mp (old C cb.1 A a cb.2.1) xc
  have ny : y∉A := Finset.disjoint_left.mp (old D db.1 A a db.2.1) yd
  have xy := card_le_one.mp (extra_at_most_one t (hH B t.1)) x
    (mem_sdiff.mpr ⟨xb,nx⟩) y (mem_sdiff.mpr ⟨yb,ny⟩)
  by_contra ne
  exact Finset.disjoint_left.mp (old C cb.1 D db.1 ne) xc (xy.symm ▸ yd)

/-- At each matched old tile at most one other tile can depend on it.
Any branching in the reverse dependence direction is confined to
targetless old tiles. -/
theorem matched_predecessor_unique {H U : Family V} {A C D Z : Finset V}
    (old : ∀ B∈U,∀ E∈U,B≠E→Disjoint B E)
    (hC : C.card≤3) (hH : ∀ B∈H,B.card≤3)
    (fin : ∀ B∈H,∀ E∈H,B≠E→Disjoint B E)
    (a : A∈U) (d : D∈U)
    (z : Target H C Z) (bc : Dependency H U A C) (bd : Dependency H U D C) :
    A=D := by
  obtain ⟨B,t,cb⟩:=bc
  obtain ⟨K,k,kb⟩:=bd
  have bz : B≠Z := by
    intro eq
    subst Z
    exact cb.2.1 (origin_unique (hH B t.1) old a cb.1 t z).symm
  have kz : K≠Z := by
    intro eq
    subst Z
    exact kb.2.1 (origin_unique (hH K k.1) old d kb.1 k z).symm
  obtain ⟨x,xb,xc⟩:=Finset.not_disjoint_iff.mp cb.2.2
  obtain ⟨y,yk,yc⟩:=Finset.not_disjoint_iff.mp kb.2.2
  have nx : x∉Z := Finset.disjoint_left.mp (fin B t.1 Z z.1 bz) xb
  have ny : y∉Z := Finset.disjoint_left.mp (fin K k.1 Z z.1 kz) yk
  have card := card_sdiff_add_card_inter C Z
  rw [z.2] at card
  have one : (C\Z).card≤1 := by omega
  have xy := card_le_one.mp one x (mem_sdiff.mpr ⟨xc,nx⟩) y
    (mem_sdiff.mpr ⟨yc,ny⟩)
  have bk : B=K := by
    by_contra nb
    exact Finset.disjoint_left.mp (fin B t.1 K k.1 nb) xb (xy.symm ▸ yk)
  subst K
  exact origin_unique (hH B t.1) old a d t k

theorem no_pins_touched {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (h : Route G F H n P Q) {S : Finset V}
    (menu : ∀ T∈H,Disjoint T S) (prior : ∀ T∈P,Disjoint T S) :
    ∀ T∈Q,Disjoint T S := by
  induction h with
  | stop _ => exact prior
  | move head _ ih =>
    apply ih
    obtain ⟨A,am,B,t,rfl,_⟩ := head
    intro T tm
    rcases mem_insert.mp tm with e|m
    · exact e ▸ menu B t.1
    · exact prior T (mem_of_mem_erase m)

theorem route_preserves_card {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (h : Route G F H n P Q) (hp : Packing G P) (allow : H⊆F) :
    P.card=Q.card := by
  induction h with
  | stop _ => rfl
  | @move n P T Q head _ ih =>
    obtain ⟨A,am,B,t,rfl,pp⟩ := head
    have nn : B∉P.erase A := fun bm=>fresh hp allow am t (mem_of_mem_erase bm)
    have k := ih pp
    rw [card_insert_of_not_mem nn,card_erase_of_mem (mem_sdiff.mp am).1] at k
    have p : 0<P.card := card_pos.mpr ⟨A,(mem_sdiff.mp am).1⟩
    omega

theorem monotone_cleanup_iff {G : SimpleGraph V} {F H P : Family V}
    (hf : Packing G F) (hp : Packing G P) (allow : H⊆F) (nonempty : P.Nonempty) :
    (∃ Q,Route G F H ((P\F).card-1) P Q ∧ OneCleanup Q F) ↔
    (stuck H (P\F)).card≤1 := by
  have nQ {Q : Family V} {n : Nat} (r : Route G F H n P Q) : Q.Nonempty := by
    apply card_pos.mp
    rw [←route_preserves_card r hp allow]
    exact card_pos.mpr nonempty
  constructor
  · rintro ⟨Q,r,clean⟩
    exact (monotone_iff_stuck_card hf hp allow).mp
      ⟨_,Q,r,(one_cleanup_iff (nQ r)).mp clean⟩
  · intro small
    obtain ⟨n,Q,r,ok⟩ := (monotone_iff_stuck_card hf hp allow).mpr small
    obtain ⟨R,r',ok'⟩ := shorten_route allow r ok
    exact ⟨R,r',(one_cleanup_iff (nQ r')).mpr ok'⟩

#print axioms blocker_unique
#print axioms matched_predecessor_unique
#print axioms monotone_cleanup_iff
end KelmansCactus.AtomicBridge.RemoteMonotoneShape
