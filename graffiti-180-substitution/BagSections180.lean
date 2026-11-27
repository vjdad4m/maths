import BagMetric180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- The tree representatives include the actual root. The color
representatives can differ only in its bag, and only at odd parity
when the root lies outside the original independent set. -/
theorem Bags.sections (h : Bags H G f) (r : V) (p : Bool) (A : Finset V) (ai : Indep H A) :
    ∃ s t : B→V, Function.LeftInverse f s ∧ Function.LeftInverse f t ∧
    s (f r)=r ∧ (∀ i,i≠f r → s i=t i) ∧ (p=false → s=t) ∧
    (∀ i,s i∈A → s i=t i) ∧
    ∀ x∈(A∩parity H r p)\univ.image t,¬H.Adj x (t (f x)) := by
  classical
  let occurs (i : B) := ∃ v∈A,f v=i
  let w (i : B) := if on : occurs i then on.choose else (h.onto i).choose
  have sectionW (i : B) : f (w i)=i := by
    by_cases on : occurs i
    · simpa only [w,dif_pos on] using on.choose_spec.2
    · simpa only [w,dif_neg on] using (h.onto i).choose_spec
  have markW {i : B} (on : occurs i) : w i∈A := by
    simpa only [w,dif_pos on] using on.choose_spec.1
  let s (i : B) := if i=f r then r else w i
  let t (i : B) := if i=f r ∧ (p=false ∨ r∈A) then r else w i
  have secS : Function.LeftInverse f s := by intro i; by_cases eq : i=f r <;> simp [s,eq,sectionW]
  have secT : Function.LeftInverse f t := by
    intro i; by_cases same : i=f r ∧ (p=false ∨ r∈A)
    · rw [show t i=r from if_pos same,same.1]
    · simpa only [t,if_neg same] using sectionW i
  have atRoot : s (f r)=r := by simp [s]
  have off (i : B) (diff : i≠f r) : s i=t i := by simp [s,t,diff]
  have even (pe : p=false) : s=t := by funext i; simp [s,t,pe]
  refine ⟨s,t,secS,secT,atRoot,off,even,?_,?_⟩
  · intro i im
    by_cases ir : i=f r
    · subst i; rw [atRoot] at im ⊢; simp [t,im]
    · exact off i ir
  · intro x xm edge
    obtain ⟨inside,gap⟩ := mem_sdiff.mp xm
    obtain ⟨xa,xp⟩ := mem_inter.mp inside
    have ne : x≠t (f x) := fun eq => gap (eq ▸ mem_image_of_mem _ (mem_univ _))
    by_cases same : f x=f r ∧ (p=false ∨ r∈A)
    · rw [show t (f x)=r from if_pos same] at edge ne
      rcases same.2 with pe|ra
      · simp [pe,mem_parity,dist_eq_one_iff_adj.mpr edge] at xp
      · exact ai _ xa _ ra ne edge
    · have ta : t (f x)∈A := by
        rw [show t (f x)=w (f x) from if_neg same]; exact markW ⟨x,xa,rfl⟩
      exact ai _ xa _ ta ne edge

theorem Bags.eligible_pull (h : Bags H G f) (gc : G.Connected) (r : V) (p : Bool) (A : Finset V)
    (s t : B→V) (ss : Function.LeftInverse f s) (atRoot : s (f r)=r)
    (off : ∀ i,i≠f r → s i=t i) (even : p=false → s=t) :
    pull s (eligible A (parity H r p) r)=eligible (pull t A) (parity G (f r) p) (f r) ∧
    pull s (parity H r p)=parity G (f r) p := by
  classical
  have par (i : B) : s i∈parity H r p ↔ i∈parity G (f r) p := by
    have d := h.repDist gc s ss i (f r)
    rw [atRoot] at d
    simp only [mem_parity,d]
  refine ⟨?_,by ext i; simp only [mem_pull,par]⟩
  ext i
  by_cases eq : i=f r
  · subst i
    cases p
    · have st := even rfl
      simp [mem_pull,eligible_iff,←st,atRoot,dist_self]
    · simp [mem_pull,eligible_iff,atRoot,dist_self]
  · have sr : s i≠r := fun same => eq (by rw [←same,ss i])
    simp only [mem_pull,eligible_iff,sr,eq,true_or,and_true]
    rw [par i,off i eq]
    have tr : t i≠r := off i eq ▸ sr
    tauto

#print axioms Bags.sections
#print axioms Bags.eligible_pull
end Minimal180.Substitution
