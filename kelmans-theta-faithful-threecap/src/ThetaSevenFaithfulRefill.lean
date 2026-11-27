import ThetaSevenFaithfulPatch

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulRefill
open SquareCap (FactorOn)
open ThetaSevenFaithfulPatch (Site lift)
noncomputable section

variable {V : Type*}
abbrev In (j : Fin 9) : V⊕Fin 9 := .inr j

structure Shape (H : SimpleGraph (V⊕Fin 9)) : Prop where
  e01 : H.Adj (In 0) (In 1)
  e12 : H.Adj (In 1) (In 2)
  e23 : H.Adj (In 2) (In 3)
  e34 : H.Adj (In 3) (In 4)
  e45 : H.Adj (In 4) (In 5)
  e50 : H.Adj (In 5) (In 0)
  e17 : H.Adj (In 1) (In 7)

private def code (j : Fin 7) : Fin 9 :=
  if j=6 then 7 else ⟨j.val,by have l:=j.isLt; omega⟩

private theorem code_inj : Function.Injective code :=
  (by decide : ∀ a b : Fin 7,code a=code b → a=b)

private theorem code_inv : ∀ j : Fin 9,(∃ i : Fin 7,code i=j) ↔ j≠6 ∧ j≠8 := by decide

private def fixed (V : Type*) : Fin 7↪(V⊕Fin 9) :=
  ⟨fun j=>In (code j),fun _ _ h=>code_inj (Sum.inr_injective h)⟩

def inner (V : Type*) [DecidableEq V] : Finset (V⊕Fin 9) := univ.map (fixed V)

theorem inner_iff [DecidableEq V] (j : Fin 9) :
    In (V:=V) j∈inner V ↔ j≠6 ∧ j≠8 := by
  simpa [inner,fixed,mem_map] using code_inv j

theorem out_not_inner [DecidableEq V] (v : V) :
    (Sum.inl v : V⊕Fin 9)∉inner V := by
  simp [inner,fixed,mem_map]

private def put (a b : V⊕Fin 9) (j : Site) : V⊕Fin 9 :=
  if h : j.val<7 then fixed V ⟨j.val,h⟩ else if j=7 then a else b

private theorem put_inj [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) :
    Function.Injective (put a b) := by
  have fmem (j : Fin 7) : fixed V j∈inner V := mem_map.mpr ⟨j,mem_univ _,rfl⟩
  have cases_high : ∀ j : Site,¬j.val<7 → j=7∨j=8 := by decide
  intro x y eq
  by_cases hx : x.val<7 <;> by_cases hy : y.val<7
  · simp only [put,dif_pos hx,dif_pos hy] at eq
    exact Fin.ext (congrArg (fun j : Fin 7=>j.val) ((fixed V).injective eq))
  · rcases cases_high y hy with rfl|rfl
    · have h : fixed V ⟨x.val,hx⟩=a := by simpa [put,hx] using eq
      exact (na (h ▸ fmem _)).elim
    · have h : fixed V ⟨x.val,hx⟩=b := by simpa [put,hx] using eq
      exact (nb (h ▸ fmem _)).elim
  · rcases cases_high x hx with rfl|rfl
    · have h : fixed V ⟨y.val,hy⟩=a := by simpa [put,hy] using eq.symm
      exact (na (h ▸ fmem _)).elim
    · have h : fixed V ⟨y.val,hy⟩=b := by simpa [put,hy] using eq.symm
      exact (nb (h ▸ fmem _)).elim
  · rcases cases_high x hx with rfl|rfl <;> rcases cases_high y hy with rfl|rfl
    all_goals first | rfl | exact (ab (by simpa [put] using eq)).elim |
      exact (ab (by simpa [put] using eq.symm)).elim

private def emb [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : Site↪(V⊕Fin 9) :=
  ⟨put a b,put_inj ab na nb⟩

@[simp] private theorem em0 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 0=In 0 := rfl

@[simp] private theorem em1 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 1=In 1 := rfl

@[simp] private theorem em2 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 2=In 2 := rfl

@[simp] private theorem em3 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 3=In 3 := rfl

@[simp] private theorem em4 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 4=In 4 := rfl

@[simp] private theorem em5 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 5=In 5 := rfl

@[simp] private theorem em6 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 6=In 7 := rfl

@[simp] private theorem em7 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 7=a := rfl

@[simp] private theorem em8 [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) : emb ab na nb 8=b := rfl

private theorem support [DecidableEq V] {a b : V⊕Fin 9}
    (ab : a≠b) (na : a∉inner V) (nb : b∉inner V) :
    (univ : Finset Site).map (emb ab na nb)=inner V ∪ {a,b} := by
  ext x
  constructor
  · intro e
    obtain ⟨j,_,rfl⟩ := mem_map.mp e
    by_cases h : j.val<7
    · apply mem_union_left
      exact mem_map.mpr ⟨⟨j.val,h⟩,mem_univ _,by simp [emb,put,h]⟩
    · have cs : ∀ j : Site,¬j.val<7→j=7∨j=8 := by decide
      rcases cs j h with rfl|rfl <;> simp
  · intro e
    rcases mem_union.mp e with e|e
    · obtain ⟨j,_,rfl⟩ := mem_map.mp e
      let k : Site := ⟨j.val,by have jlt:=j.isLt; omega⟩
      exact mem_map.mpr ⟨k,mem_univ _,by
        have hr : k.val<7 := j.isLt
        simp [emb,put,hr,k]⟩
    · simp only [mem_insert,mem_singleton] at e
      rcases e with rfl|rfl
      · exact mem_map.mpr ⟨7,mem_univ _,by simp⟩
      · exact mem_map.mpr ⟨8,mem_univ _,by simp⟩

def Allowed (H : SimpleGraph (V⊕Fin 9)) (m : Fin 3) (a b : V⊕Fin 9) : Prop :=
  (m=0 ∧ H.Adj (In 2) a ∧ H.Adj (In 5) b) ∨
  (m=1 ∧ H.Adj (In 2) a ∧ H.Adj a b) ∨
  (m=2 ∧ H.Adj (In 5) a ∧ H.Adj a b)

/-- Ring and restored terminal are filled with the two surviving
vertices of the live cap tile. Either guest may be the faithful
vertex, so no artificial edges are required. -/
theorem refills [DecidableEq V] {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    {a b : V⊕Fin 9} (ab : a≠b) (na : a∉inner V) (nb : b∉inner V)
    (m : Fin 3) (allow : Allowed H m a b) :
    FactorOn H (inner V ∪ {a,b}) := by
  rw [←support ab na nb]
  apply lift m (emb ab na nb)
  intro x y e
  simp only [ThetaSevenFaithfulPatch.separateEdges,List.mem_append] at e
  rcases e with q|q
  · simp [ThetaSevenFaithfulPatch.core] at q
    rcases q with w|w|w|w|w|w|w <;> have xx := w.1 <;> have yy := w.2 <;>
      subst x <;> subst y
    all_goals first | simpa using sh.e01 | simpa using sh.e12 | simpa using sh.e23 |
      simpa using sh.e34 | simpa using sh.e45 | simpa using sh.e50 | simpa using sh.e17
  · rcases allow with ⟨rfl,p,q'⟩|⟨rfl,p,q'⟩|⟨rfl,p,q'⟩
    all_goals
      simp at q
      rcases q with ⟨xx,yy⟩|⟨xx,yy⟩ <;> subst x <;> subst y
      all_goals first | simpa using p | simpa using q'

#print axioms refills
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulRefill
