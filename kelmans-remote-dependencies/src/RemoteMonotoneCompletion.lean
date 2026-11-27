import RemoteMonotoneRank
import RemoteVacancyReach

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteMonotoneCompletion
open RemoteMonotoneRank
open RemoteVacancyReach (Packing OneSlide OneCleanup Slides)
variable {V : Type*} [DecidableEq V]

/-- F is the prescribed final factor, H⊆F the targets allowed during
neutral transport. Requiring H disjoint from chosen pins models fixed pins. -/
def Step (G : SimpleGraph V) (F H P Q : Family V) : Prop :=
  ∃ A∈P\F, ∃ B, Target H A B ∧ Q=insert B (P.erase A) ∧ Packing G Q

inductive Route (G : SimpleGraph V) (F H : Family V) :
    Nat→Family V→Family V→Prop
  | stop (P) : Route G F H 0 P P
  | move {n P Q R} : Step G F H P Q → Route G F H n Q R →
    Route G F H (n+1) P R

/-- A target sharing two vertices with a different old tile cannot
already be present in the old packing. -/
theorem fresh {G : SimpleGraph V} {P F H : Family V} {A B : Finset V}
    (hp : Packing G P) (allowed : H⊆F) (a : A∈P\F) (b : Target H A B) :
    B∉P := by
  intro bm
  have ab : A≠B := fun e=>(mem_sdiff.mp a).2 (e.symm ▸ allowed b.1)
  have apart := disjoint_iff_inter_eq_empty.mp (hp.2 A (mem_sdiff.mp a).1 B bm ab)
  have impossible := b.2
  rw [apart] at impossible
  simp at impossible

theorem after_nonfinal {F P : Family V} {A B : Finset V} (b : B∈F) :
    (insert B (P.erase A))\F=(P\F).erase A := by
  ext C
  constructor
  · intro h
    obtain ⟨c,nc⟩ := mem_sdiff.mp h
    rcases mem_insert.mp c with eq|old
    · exact (nc (eq.symm ▸ b)).elim
    · obtain ⟨ne,p⟩ := mem_erase.mp old
      exact mem_erase.mpr ⟨ne,mem_sdiff.mpr ⟨p,nc⟩⟩
  · intro h
    obtain ⟨ne,c⟩ := mem_erase.mp h
    obtain ⟨cm,cn⟩ := mem_sdiff.mp c
    exact mem_sdiff.mpr
      ⟨mem_insert_of_mem (mem_erase.mpr ⟨ne,cm⟩),cn⟩

theorem step_enables {G : SimpleGraph V} {F H P Q : Family V}
    (allowed : H⊆F) (h : Step G F H P Q) :
    ∃ A B, Ready H (P\F) A B ∧ Q\F=(P\F).erase A := by
  obtain ⟨A,am,B,targ,rfl,hq⟩ := h
  refine ⟨A,B,⟨am,targ,?_⟩,after_nonfinal (allowed targ.1)⟩
  intro C x
  obtain ⟨cm,ca,bad⟩ := x
  obtain ⟨cp,cf⟩ := mem_sdiff.mp cm
  have cb : B≠C := fun e=>cf (e ▸ allowed targ.1)
  apply bad
  exact hq.2 B (mem_insert_self _ _) C
    (mem_insert_of_mem (mem_erase.mpr ⟨ca,cp⟩)) cb

theorem realize_step {G : SimpleGraph V} {F H P : Family V} {A B : Finset V}
    (hf : Packing G F) (hp : Packing G P) (allowed : H⊆F)
    (h : Ready H (P\F) A B) :
    Step G F H P (insert B (P.erase A)) := by
  have bf := allowed h.2.1.1
  have new := fresh hp allowed h.1 h.2.1
  have apart (C : Finset V) (mc : C∈P.erase A) : Disjoint B C := by
    obtain ⟨ne,cp⟩ := mem_erase.mp mc
    by_cases cf : C∈F
    · exact hf.2 B bf C cf (fun e=>new (e.symm ▸ cp))
    · by_contra d
      exact h.2.2 C ⟨mem_sdiff.mpr ⟨cp,cf⟩,ne,d⟩
  refine ⟨A,h.1,B,h.2.1,rfl,?_,?_⟩
  · intro C cm
    rcases mem_insert.mp cm with e|m
    · exact e ▸ hf.1 B bf
    · exact hp.1 C (mem_of_mem_erase m)
  · intro C cm D dm ne
    rcases mem_insert.mp cm with e|pc <;> rcases mem_insert.mp dm with f|pd
    · exact (ne (e.trans f.symm)).elim
    · exact e ▸ apart D pd
    · exact f ▸ (apart C pc).symm
    · exact hp.2 C (mem_of_mem_erase pc) D (mem_of_mem_erase pd) ne

theorem step_is_slide {G : SimpleGraph V} {F H P Q : Family V}
    (hp : Packing G P) (allow : H⊆F) (h : Step G F H P Q) :
    OneSlide P Q := by
  obtain ⟨A,am,B,targ,rfl,_⟩ := h
  have n := fresh hp allow am targ
  refine ⟨A,(mem_sdiff.mp am).1,B,mem_insert_self _ _,targ.2,?_⟩
  ext C
  by_cases cb : C=B
  · subst C
    simp [n]
  · simp [cb]

theorem route_to_reduce {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (allowed : H⊆F) (h : Route G F H n P Q) : Reduce H (P\F) (Q\F) := by
  induction h with
  | stop _ => exact Reduce.stop _
  | move h _ ih =>
    obtain ⟨A,B,ready,eq⟩ := step_enables allowed h
    rw [eq] at ih
    exact Reduce.move ready ih

theorem realize_reduce {G : SimpleGraph V} {F H U R : Family V}
    (hf : Packing G F) (allowed : H⊆F) (h : Reduce H U R) :
    ∀ P, Packing G P → P\F=U → ∃ n Q,Route G F H n P Q ∧ Q\F=R := by
  induction h with
  | stop U =>
    intro P hp eq
    exact ⟨0,P,Route.stop _,eq⟩
  | @move U R A B enabled _ ih =>
    intro P hp eq
    have h : Ready H (P\F) A B := eq.symm ▸ enabled
    let Q := insert B (P.erase A)
    have step : Step G F H P Q := realize_step hf hp allowed h
    have hQ : Packing G Q := by
      obtain ⟨_,_,_,_,_,q⟩ := step
      exact q
    have shape : Q\F=U.erase A := (after_nonfinal (allowed h.2.1.1)).trans (congrArg (fun x=>x.erase A) eq)
    obtain ⟨n,T,endgame,rem⟩ := ih Q hQ shape
    exact ⟨n+1,T,Route.move step endgame,rem⟩

/-- The exact monotone completion criterion for any graph and any fixed
target factor F. At most one old non-target tile may remain for the final
cleanup. This does not assert existence of F or of a favorable rank. -/
theorem monotone_completion_iff {G : SimpleGraph V} {F H P : Family V}
    (hf : Packing G F) (hp : Packing G P) (allowed : H⊆F) :
    (∃ n Q,Route G F H n P Q ∧ (Q\F).card≤1) ↔
    ∃ D⊆P\F, ∃ r,Ranked H (P\F) D r ∧ ((P\F)\D).card≤1 := by
  constructor
  · rintro ⟨n,Q,route,small⟩
    let U := P\F
    let R := Q\F
    have reach : Reduce H U R := route_to_reduce allowed route
    obtain ⟨sub,r,rank⟩ := reduce_iff_ranked.mp reach
    refine ⟨U\R,sdiff_subset,r,rank,?_⟩
    have eq : U\(U\R)=R := by
      ext a
      constructor
      · intro m
        obtain ⟨u,no⟩ := mem_sdiff.mp m
        by_contra n
        exact no (mem_sdiff.mpr ⟨u,n⟩)
      · intro aR
        exact mem_sdiff.mpr ⟨sub aR,fun z=>(mem_sdiff.mp z).2 aR⟩
    change (U\(U\R)).card≤1
    rw [eq]
    exact small
  · rintro ⟨D,sub,r,rank,small⟩
    have red := reduce_from_ranking H D r (P\F) sub rank
    obtain ⟨n,Q,h,eq⟩ := realize_reduce hf allowed red P hp rfl
    exact ⟨n,Q,h,eq ▸ small⟩

theorem one_cleanup_iff {P F : Family V} (hne : P.Nonempty) :
    OneCleanup P F ↔ (P\F).card≤1 := by
  constructor
  · rintro ⟨A,am,sub⟩
    apply card_le_one.mpr
    intro B b C c
    have atMost (T : Finset V) (m : T∈P\F) : T=A := by
      by_contra ne
      exact (mem_sdiff.mp m).2 (sub (mem_erase.mpr ⟨ne,(mem_sdiff.mp m).1⟩))
    exact (atMost B b).trans (atMost C c).symm
  · intro h
    by_cases z : (P\F).Nonempty
    · obtain ⟨A,a⟩ := z
      refine ⟨A,(mem_sdiff.mp a).1,?_⟩
      intro B bm
      by_contra b
      exact (mem_erase.mp bm).1 (card_le_one.mp h B
        (mem_sdiff.mpr ⟨mem_of_mem_erase bm,b⟩) A a)
    · obtain ⟨A,a⟩ := hne
      refine ⟨A,a,?_⟩
      intro B b
      by_contra no
      exact z ⟨B,mem_sdiff.mpr ⟨mem_of_mem_erase b,no⟩⟩

/-- The counted length of any monotone route is the exact number of
old non-target supports it discharged. -/
theorem route_card {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (allow : H⊆F) (h : Route G F H n P Q) :
    (P\F).card=(Q\F).card+n := by
  induction h with
  | stop _ => simp
  | @move n P Q R move _ ih =>
    obtain ⟨A,B,r,eq⟩ := step_enables allow move
    rw [eq,card_erase_of_mem r.1] at ih
    have gt : 0<(P\F).card := card_pos.mpr ⟨A,r.1⟩
    omega

/-- A successful monotone completion can always stop at the first
eligible cleanup. Its optimal number of steps is exactly d−1 truncated
at 0, where d is the number of original tiles not in F. -/
theorem shorten_route {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (allowed : H⊆F) (route : Route G F H n P Q) (clean : (Q\F).card≤1) :
    ∃ R,Route G F H ((P\F).card-1) P R ∧ (R\F).card≤1 := by
  induction route with
  | stop P =>
    rw [Nat.sub_eq_zero_of_le clean]
    exact ⟨P,Route.stop _,clean⟩
  | @move n P T Q step _ ih =>
    by_cases ready : (P\F).card≤1
    · rw [Nat.sub_eq_zero_of_le ready]
      exact ⟨P,Route.stop _,ready⟩
    · obtain ⟨R,r,e⟩ := ih clean
      obtain ⟨A,B,am,eq⟩ := step_enables allowed step
      have same : (T\F).card=(P\F).card-1 := by
        rw [eq,card_erase_of_mem am.1]
      have len : ((T\F).card-1)+1=(P\F).card-1 := by omega
      refine ⟨R,?_ ,e⟩
      rw [←len]
      exact Route.move step r

theorem least_route_length {G : SimpleGraph V} {F H P Q : Family V} {n : Nat}
    (allowed : H⊆F) (route : Route G F H n P Q) (clean : (Q\F).card≤1) :
    (P\F).card-1≤n := by
  have eq := route_card allowed route
  omega

#print axioms monotone_completion_iff
#print axioms shorten_route
#print axioms least_route_length
#print axioms one_cleanup_iff
#print axioms route_card
end KelmansCactus.AtomicBridge.RemoteMonotoneCompletion
