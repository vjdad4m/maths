import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteMonotoneRank
variable {V : Type*} [DecidableEq V]
abbrev Family (V : Type*) := Finset (Finset V)

/-- Candidates come from a fixed target factor. Only their two-vertex
overlap with the old tile matters for a one-hole slide. -/
def Target (F : Family V) (A B : Finset V) : Prop :=
  B∈F ∧ (A∩B).card=2

/-- The extra vertex of target B may still be owned by another old tile C. -/
def Blocks (U : Family V) (A B C : Finset V) : Prop :=
  C∈U ∧ C≠A ∧ ¬Disjoint B C

/-- With frozen vacancies, quite simply omit target tiles that hit a pin
from F for the purpose of the neutral moves. -/
def Ready (F U : Family V) (A B : Finset V) : Prop :=
  A∈U ∧ Target F A B ∧ ∀ C, ¬Blocks U A B C

/-- Evolution of untouched old tiles only, not of the complete partial
factor. Newly inserted target tiles never need to be moved. -/
inductive Reduce (F : Family V) : Family V → Family V → Prop
  | stop (U) : Reduce F U U
  | move {U R A B} : Ready F U A B → Reduce F (U.erase A) R → Reduce F U R

/-- Finite static certificate: every old tile that will move has a target;
every old tile blocking that target must also move and has lower rank. -/
def Ranked (F U D : Family V) (r : Finset V→Nat) : Prop :=
  ∀ A∈D, ∃ B, Target F A B ∧ ∀ C, Blocks U A B C → C∈D ∧ r C<r A

theorem reduce_subset {F U R : Family V} (h : Reduce F U R) : R⊆U := by
  induction h with
  | stop _ => exact Subset.rfl
  | move _ _ ih => exact ih.trans (erase_subset _ _)

theorem ranking_of_reduce {F U R : Family V} (h : Reduce F U R) :
    ∃ r, Ranked F U (U\R) r := by
  induction h with
  | stop U =>
    exact ⟨fun _=>0,by simp [Ranked]⟩
  | @move U R A B now later ih =>
    obtain ⟨r,ih⟩ := ih
    let r' : Finset V→Nat := fun C=>if C=A then 0 else r C+1
    have sub : R⊆U.erase A := reduce_subset later
    have an : A∉R := fun e=>not_mem_erase A U (sub e)
    refine ⟨r',?_⟩
    intro T tm
    obtain ⟨tu,tn⟩ := mem_sdiff.mp tm
    by_cases ta : T=A
    · subst T
      exact ⟨B,now.2.1,fun C bad=>(now.2.2 C bad).elim⟩
    · have tf : T∈U.erase A\R := mem_sdiff.mpr ⟨mem_erase.mpr ⟨ta,tu⟩,tn⟩
      obtain ⟨K,targ,small⟩ := ih T tf
      refine ⟨K,targ,?_⟩
      intro C cb
      by_cases ca : C=A
      · subst C
        exact ⟨mem_sdiff.mpr ⟨now.1,an⟩,by simp [r',ta]⟩
      · have b : Blocks (U.erase A) T K C :=
          ⟨mem_erase.mpr ⟨ca,cb.1⟩,cb.2⟩
        obtain ⟨cm,low⟩ := small C b
        have md : C∈U\R := mem_sdiff.mpr ⟨cb.1,(mem_sdiff.mp cm).2⟩
        exact ⟨md,by simpa [r',ca,ta] using low⟩

theorem reduce_from_ranking (F D : Family V) (r : Finset V→Nat) :
    ∀ U, D⊆U → Ranked F U D r → Reduce F U (U\D) := by
  refine D.strongInductionOn ?_
  intro D ih U sub ready
  by_cases e : D=∅
  · subst D
    simpa using (Reduce.stop (F:=F) U)
  · obtain ⟨A,am,minA⟩ := exists_min_image D r (nonempty_iff_ne_empty.mpr e)
    obtain ⟨B,targ,small⟩ := ready A am
    have legal : Ready F U A B := by
      refine ⟨sub am,targ,?_⟩
      intro C cb
      obtain ⟨cm,low⟩ := small C cb
      exact Nat.not_lt_of_ge (minA C cm) low
    have less : D.erase A ⊂ D := erase_ssubset am
    have sub' : D.erase A ⊆ U.erase A := by
      intro C hm
      exact mem_erase.mpr ⟨(mem_erase.mp hm).1,sub (mem_erase.mp hm).2⟩
    have rk' : Ranked F (U.erase A) (D.erase A) r := by
      intro C cm
      obtain ⟨T,hT,pred⟩ := ready C (mem_erase.mp cm).2
      refine ⟨T,hT,?_⟩
      intro E em
      obtain ⟨ed,low⟩ := pred E ⟨(mem_erase.mp em.1).2,em.2⟩
      exact ⟨mem_erase.mpr ⟨(mem_erase.mp em.1).1,ed⟩,low⟩
    have eq : U.erase A\D.erase A=U\D := by
      ext C
      by_cases h : C=A
      · subst C
        simp [am]
      · simp [h]
    have tail := ih (D.erase A) less (U.erase A) sub' rk'
    rw [eq] at tail
    exact Reduce.move legal tail

theorem reduce_iff_ranked {F U R : Family V} :
    Reduce F U R ↔ R⊆U ∧ ∃ r,Ranked F U (U\R) r := by
  constructor
  · intro a
    exact ⟨reduce_subset a,ranking_of_reduce a⟩
  · rintro ⟨sub,r,rank⟩
    have h := reduce_from_ranking F (U\R) r U sdiff_subset rank
    have eq : U\(U\R)=R := by
      ext a
      constructor
      · intro m
        obtain ⟨u,no⟩ := mem_sdiff.mp m
        by_contra n
        exact no (mem_sdiff.mpr ⟨u,n⟩)
      · intro aR
        exact mem_sdiff.mpr ⟨sub aR,fun z=>(mem_sdiff.mp z).2 aR⟩
    rwa [eq] at h

/-- In any packing of triples, one old tile can have at most one
two-vertex-overlap target. The conclusion needs no ambient graph. -/
theorem target_unique {F : Family V} {A B C : Finset V}
    (hA : A.card≤3) (apart : ∀ Q∈F,∀ S∈F,Q≠S→Disjoint Q S)
    (hb : Target F A B) (hc : Target F A C) : B=C := by
  by_contra np
  have d : Disjoint (A∩B) (A∩C) :=
    (apart B hb.1 C hc.1 np).mono inter_subset_right inter_subset_right
  have h := card_le_card (union_subset inter_subset_left inter_subset_left :
    (A∩B)∪(A∩C)⊆A)
  rw [card_union_of_disjoint d,hb.2,hc.2] at h
  omega

#print axioms reduce_iff_ranked
#print axioms target_unique
end KelmansCactus.AtomicBridge.RemoteMonotoneRank
