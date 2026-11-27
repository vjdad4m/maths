import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteVacancyReach
open SquareCap (IsTile FactorOn HasFactor)
variable {V : Type*} [DecidableEq V]

/-- A packing is a family of genuine tiles with disjoint supports. -/
def Packing (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ T∈P,IsTile G T) ∧ (∀ A∈P,∀ B∈P,A≠B→Disjoint A B)

def OneSlide (P Q : Finset (Finset V)) : Prop :=
  ∃ A∈P, ∃ B∈Q, (A∩B).card=2 ∧ P.erase A = Q.erase B

def OneCleanup (P F : Finset (Finset V)) : Prop :=
  ∃ A∈P, P.erase A ⊆ F

/-- Completeness of a finite exact-cover search, using the least remaining
vertex. Soundness is unnecessary when checking that no extension exists. -/
def search [LinearOrder V] (menu : V→List (Finset V)) : Nat → Finset V → Bool
  | 0,S => decide (S=∅)
  | n+1,S => if h:S.Nonempty then
      (menu (S.min' h)).any fun T => if T⊆S then search menu n (S\T) else false
    else true

theorem erase_cover {G : SimpleGraph V} {P : Finset (Finset V)}
    (h : Packing G P) {T : Finset V} (m : T∈P) :
    (P.erase T).biUnion id=P.biUnion id\T := by
  ext x
  rw [mem_sdiff]
  constructor
  · intro hx
    obtain ⟨U,um,xu⟩ := mem_biUnion.mp hx
    obtain ⟨ne,u⟩ := mem_erase.mp um
    exact ⟨mem_biUnion.mpr ⟨U,u,xu⟩,fun xt=>disjoint_left.mp (h.2 U u T m ne) xu xt⟩
  · rintro ⟨hx,nx⟩
    obtain ⟨U,u,xu⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨U,mem_erase.mpr ⟨fun e=>nx (e ▸ xu),u⟩,xu⟩

theorem search_complete [LinearOrder V] {G : SimpleGraph V} {menu : V→List (Finset V)}
    (contained : ∀ T,IsTile G T→∀ x∈T,T∈menu x) (n : Nat) {P : Finset (Finset V)}
    (h : Packing G P) (hn : P.card≤n) :
    search menu n (P.biUnion id)=true := by
  induction n generalizing P with
  | zero =>
    have z : P=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp [z,search]
  | succ n ih =>
    rw [search]
    split
    next nonempty =>
      let S := P.biUnion id
      obtain ⟨T,tm,xt⟩ := mem_biUnion.mp (min'_mem S nonempty)
      have sub : T⊆S := fun x hx=>mem_biUnion.mpr ⟨T,tm,hx⟩
      have less : (P.erase T).card≤n := by rw [card_erase_of_mem tm]; omega
      have pack : Packing G (P.erase T) :=
        ⟨fun A m=>h.1 A (mem_erase.mp m).2,
          fun A a B b d=>h.2 A (mem_erase.mp a).2 B (mem_erase.mp b).2 d⟩
      apply List.any_eq_true.mpr
      refine ⟨T,contained T (h.1 T tm) _ xt,?_⟩
      simp only [id_eq] at xt
      rw [if_pos sub,←erase_cover h tm]
      exact ih pack less
    next => rfl

theorem packing_vertex_count {G : SimpleGraph V} {P : Finset (Finset V)}
    (h : Packing G P) : (P.biUnion id).card=3*P.card := by
  rw [card_biUnion]
  · simp only [id_eq]
    rw [sum_congr rfl (fun T m=>(h.1 T m).1)]
    simp [Nat.mul_comm]
  · exact fun A a B b d=>h.2 A a B b d

theorem keep_card_le {A P Q : Finset (Finset V)} (step : OneSlide P Q) :
    (A∩P).card≤(A∩Q).card+1 := by
  obtain ⟨T,tm,U,um,_,eq⟩ := step
  by_cases mt : T∈A
  · have sub : (A∩P).erase T⊆A∩Q := by
      intro S sm
      have e := mem_erase.mp sm
      obtain ⟨hA,hP⟩ := mem_inter.mp e.2
      have q : S∈Q.erase U := eq ▸ mem_erase.mpr ⟨e.1,hP⟩
      exact mem_inter.mpr ⟨hA,mem_of_mem_erase q⟩
    have b := card_le_card sub
    rw [card_erase_of_mem (mem_inter.mpr ⟨mt,tm⟩)] at b
    omega
  · have sub : A∩P⊆A∩Q := by
      intro S sm
      obtain ⟨hA,hP⟩ := mem_inter.mp sm
      have q : S∈Q.erase U := eq ▸ mem_erase.mpr ⟨fun e=>mt (e ▸ hA),hP⟩
      exact mem_inter.mpr ⟨hA,mem_of_mem_erase q⟩
    have b := card_le_card sub
    omega

theorem cleanup_card_le {A P F : Finset (Finset V)} (close : OneCleanup P F) :
    (A∩P).card≤(A∩F).card+1 := by
  obtain ⟨T,tm,sub⟩ := close
  by_cases t : T∈A
  · have s : (A∩P).erase T⊆A∩F := by
      intro x hx
      obtain ⟨ne,hx⟩:=mem_erase.mp hx
      obtain ⟨a,p⟩:=mem_inter.mp hx
      exact mem_inter.mpr ⟨a,sub (mem_erase.mpr ⟨ne,p⟩)⟩
    have b:=card_le_card s
    rw [card_erase_of_mem (mem_inter.mpr ⟨t,tm⟩)] at b
    omega
  · have s : A∩P⊆A∩F := by
      intro x hx
      obtain ⟨a,p⟩:=mem_inter.mp hx
      exact mem_inter.mpr ⟨a,sub (mem_erase.mpr ⟨fun eq=>t (eq ▸ a),p⟩)⟩
    have b:=card_le_card s
    omega

inductive Slides : Nat → Finset (Finset V) → Finset (Finset V) → Prop
  | zero (P) : Slides 0 P P
  | step {n P Q R} : OneSlide P Q → Slides n Q R → Slides (n+1) P R

theorem slides_card_le {n : Nat} {A P Q : Finset (Finset V)}
    (steps : Slides n P Q) : (A∩P).card≤(A∩Q).card+n := by
  induction steps with
  | zero => simp
  | step h _ ih =>
    have b := keep_card_le (A:=A) h
    omega

theorem cleanup_lower_bound {n : Nat} {P Q F : Finset (Finset V)}
    (steps : Slides n P Q) (close : OneCleanup Q F) : P.card≤(P∩F).card+n+1 := by
  have a := slides_card_le (A:=P) steps
  have b := cleanup_card_le (A:=P) close
  rw [inter_self] at a
  omega

#print axioms search_complete
#print axioms cleanup_lower_bound
end KelmansCactus.AtomicBridge.RemoteVacancyReach
