import RemoteMonotoneCompletion

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteMonotoneDependencies
open RemoteMonotoneRank RemoteMonotoneCompletion
open RemoteVacancyReach (Packing)
variable {V : Type*} [DecidableEq V]

/-- A→C means moving the original tile A to its two-overlap target
would use a vertex still occupied by original C. -/
def Dependency (H U : Family V) (A C : Finset V) : Prop :=
  ∃ B, Target H A B ∧ Blocks U A B C

def Dead (H U : Family V) (A : Finset V) : Prop :=
  (¬∃ B,Target H A B) ∨ Relation.TransGen (Dependency H U) A A

def Bad (H U : Family V) (A : Finset V) : Prop :=
  ∃ C, Relation.ReflTransGen (Dependency H U) A C ∧ Dead H U C

noncomputable def stuck (H U : Family V) : Family V := by
  classical
  exact U.filter (Bad H U)

theorem in_stuck {H U : Family V} {A : Finset V} :
    A∈stuck H U ↔ A∈U∧Bad H U A := by
  classical
  simp [stuck]

/-- These are precisely the tasks that can be executed early: they have
targets, contain all their predecessors, and contain no directed cycle. -/
def Clean (H U D : Family V) : Prop :=
  (∀ A∈D,∃ B,Target H A B) ∧
  (∀ A∈D,∀ C,Dependency H U A C→C∈D) ∧
  (∀ A∈D,¬Relation.TransGen (Dependency H U) A A)

theorem dependency_stays {H U D : Family V} (h : Clean H U D)
    {A C : Finset V} (am : A∈D) (p : Relation.ReflTransGen (Dependency H U) A C) :
    C∈D := by
  induction p with
  | refl => exact am
  | tail _ edge ih => exact h.2.1 _ ih _ edge

theorem ranked_edges {H U D : Family V} {r : Finset V→Nat}
    (hs : ∀ A∈U,A.card≤3) (apart : ∀ B∈H,∀ C∈H,B≠C→Disjoint B C)
    (sub : D⊆U) (h : Ranked H U D r) {A C : Finset V}
    (a : A∈D) (e : Dependency H U A C) : C∈D∧r C<r A := by
  obtain ⟨B,tb,cb⟩ := e
  obtain ⟨E,te,pred⟩ := h A a
  have eq := target_unique (hs A (sub a)) apart tb te
  exact pred C (eq ▸ cb)

theorem ranked_paths {H U D : Family V} {r : Finset V→Nat}
    (hs : ∀ A∈U,A.card≤3) (apart : ∀ B∈H,∀ C∈H,B≠C→Disjoint B C)
    (sub : D⊆U) (h : Ranked H U D r) {A C : Finset V}
    (a : A∈D) (p : Relation.TransGen (Dependency H U) A C) :
    C∈D∧r C<r A := by
  induction p with
  | single e => exact ranked_edges hs apart sub h a e
  | tail _ e ih =>
    obtain ⟨c,cr⟩ := ranked_edges hs apart sub h ih.1 e
    exact ⟨c,cr.trans ih.2⟩

/-- Ranking by number of reachable old vertices establishes the converse
without assuming a topological ordering theorem. Along A→C the positive
successors of C are a proper subset of the positive successors of A. -/
theorem ranked_iff_clean {H U D : Family V}
    (hs : ∀ A∈U,A.card≤3) (apart : ∀ B∈H,∀ C∈H,B≠C→Disjoint B C)
    (sub : D⊆U) :
    (∃ r,Ranked H U D r) ↔ Clean H U D := by
  constructor
  · rintro ⟨r,h⟩
    refine ⟨?_,?_,?_⟩
    · intro A a
      obtain ⟨B,b,_⟩ := h A a
      exact ⟨B,b⟩
    · intro A a C e
      exact (ranked_edges hs apart sub h a e).1
    · intro A a p
      exact (Nat.lt_irrefl (r A)) (ranked_paths hs apart sub h a p).2
  · intro h
    classical
    let successor (A : Finset V) := D.filter (Relation.TransGen (Dependency H U) A)
    refine ⟨fun A=>(successor A).card,?_⟩
    intro A a
    obtain ⟨B,b⟩ := h.1 A a
    refine ⟨B,b,?_⟩
    intro C cb
    have edge : Dependency H U A C := ⟨B,b,cb⟩
    have c := h.2.1 A a C edge
    refine ⟨c,card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩)⟩
    · intro T t
      obtain ⟨td,tp⟩ := mem_filter.mp t
      exact mem_filter.mpr ⟨td,(Relation.TransGen.single edge).trans tp⟩
    · intro eq
      have m : C∈successor A := mem_filter.mpr ⟨c,Relation.TransGen.single edge⟩
      have m' : C∈successor C := eq.symm ▸ m
      exact h.2.2 C c (mem_filter.mp m').2

theorem clean_avoids_stuck {H U D : Family V} (h : Clean H U D)
    {A : Finset V} (a : A∈D) : ¬Bad H U A := by
  rintro ⟨C,p,dead⟩
  have c := dependency_stays h a p
  exact dead.elim (fun no=>no (h.1 C c)) (h.2.2 C c)

theorem all_other_clean (H U : Family V) : Clean H U (U\stuck H U) := by
  refine ⟨?_,?_,?_⟩
  · intro A a
    obtain ⟨u,ok⟩ := mem_sdiff.mp a
    by_contra no
    exact ok (in_stuck.mpr ⟨u,A,.refl,Or.inl no⟩)
  · intro A a C e
    obtain ⟨u,oka⟩ := mem_sdiff.mp a
    obtain ⟨B,t,blocks⟩ := e
    refine mem_sdiff.mpr ⟨blocks.1,?_⟩
    intro ec
    obtain ⟨D,path,dead⟩ := (in_stuck.mp ec).2
    have ad : Dependency H U A C := ⟨B,t,blocks⟩
    exact oka (in_stuck.mpr ⟨u,D,Relation.ReflTransGen.head ad path,dead⟩)
  · intro A a cycle
    obtain ⟨u,ok⟩ := mem_sdiff.mp a
    exact ok (in_stuck.mpr ⟨u,A,.refl,Or.inr cycle⟩)

/-- The unique best residual set consists of the old tiles that can
reach a targetless tile or a directed cycle. In particular, all other
old tiles can be discharged together, not merely one at a time. -/
theorem exact_residual {H U : Family V}
    (hs : ∀ A∈U,A.card≤3) (apart : ∀ B∈H,∀ C∈H,B≠C→Disjoint B C) :
    Reduce H U (stuck H U) ∧ ∀ R,Reduce H U R→stuck H U⊆R := by
  constructor
  · have sub : stuck H U⊆U := fun _ h=>(in_stuck.mp h).1
    exact reduce_iff_ranked.mpr
      ⟨sub,(ranked_iff_clean hs apart sdiff_subset).mpr (all_other_clean H U)⟩
  · intro R route A a
    obtain ⟨au,abad⟩ := in_stuck.mp a
    have rank := (reduce_iff_ranked.mp route).2
    have clean : Clean H U (U\R) := (ranked_iff_clean hs apart sdiff_subset).mp rank
    by_contra n
    exact clean_avoids_stuck clean (mem_sdiff.mpr ⟨au,n⟩) abad

/-- Exact static graph criterion for monotone completion to a prescribed F:
all but at most one old non-target tile must avoid reaching a targetless
tile or a dependency cycle. H allows a stricter menu, such as frozen pins. -/
theorem monotone_iff_stuck_card {G : SimpleGraph V} {F H P : Family V}
    (hf : Packing G F) (hp : Packing G P) (allow : H⊆F) :
    (∃ n Q,Route G F H n P Q ∧ (Q\F).card≤1) ↔ (stuck H (P\F)).card≤1 := by
  have hs (A : Finset V) (a : A∈P\F) : A.card≤3 :=
    Nat.le_of_eq (hp.1 A (mem_sdiff.mp a).1).1
  have apart (B : Finset V) (b : B∈H) (C : Finset V) (c : C∈H) (ne : B≠C) :
      Disjoint B C := hf.2 B (allow b) C (allow c) ne
  have ideal := exact_residual hs apart
  constructor
  · rintro ⟨n,Q,route,done⟩
    exact (card_le_card (ideal.2 _ (route_to_reduce allow route))).trans done
  · intro small
    obtain ⟨n,Q,route,residual⟩ := realize_reduce hf allow ideal.1 P hp rfl
    exact ⟨n,Q,route,residual ▸ small⟩

#print axioms exact_residual
#print axioms monotone_iff_stuck_card
end KelmansCactus.AtomicBridge.RemoteMonotoneDependencies
