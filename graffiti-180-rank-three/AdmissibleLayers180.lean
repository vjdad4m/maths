import BreadthScore180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
def Entry (G : SimpleGraph V) (r : V) (D : Finset V) (x : V) : Prop :=
  x∈D ∧ ∃ y,Pred G r x y ∧ y∉D

omit [Fintype V] [DecidableEq V] in
def Allowed (G : SimpleGraph V) (r : V) (D : Finset V) (x y : V) : Prop :=
  Pred G r x y ∧ (Entry G r D x → y∉D)

noncomputable def entries (G : SimpleGraph V) (r : V) (D : Finset V) : Finset V :=
  (univ.erase r).filter (Entry G r D)

noncomputable def children (G : SimpleGraph V) (r : V) (D B : Finset V) : Finset V :=
  (univ.erase r).filter (fun x => ∃ y∈B,Allowed G r D x y)

/-- Entry takes priority without any loss in the optimum. The remaining
unit a child can supply is precisely its incidence with an allowed center. -/
theorem local_score_formula (G : SimpleGraph V) (r : V) (D B : Finset V) (x : V) :
    localScore G r D B x=(if Entry G r D x then 1 else 0)+
      (if ∃ y∈B,Allowed G r D x y then 1 else 0) := by
  classical
  let e := Entry G r D x
  let c := ∃ y∈B,Allowed G r D x y
  change _=(if e then 1 else 0)+(if c then 1 else 0)
  have lower (y : V) (hy : Pred G r x y) : reward D B x y≤localScore G r D B x :=
    le_sup (f:=reward D B x) (mem_filter.mpr ⟨mem_univ _,hy⟩)
  apply le_antisymm
  · unfold localScore
    apply Finset.sup_le
    intro y hy
    have pred := (mem_filter.mp hy).2
    have one : x∈D ∧ y∉D → e := fun h => ⟨h.1,y,pred,h.2⟩
    have two : x∈D ∧ y∉D → y∈B → c := fun h yy => ⟨y,yy,pred,fun _ => h.2⟩
    have free : ¬e → y∈B → c := fun no yy => ⟨y,yy,pred,fun h => (no h).elim⟩
    by_cases good : x∈D ∧ y∉D
    · have he := one good
      by_cases yb : y∈B
      · simp only [reward,if_pos good,if_pos he,if_pos yb,if_pos (two good yb),le_refl]
      · simp only [reward,if_pos good,if_pos he,if_neg yb,add_zero]; omega
    · by_cases yb : y∈B
      · by_cases he : e
        · simp only [reward,if_neg good,if_pos yb,if_pos he,zero_add]; omega
        · simp only [reward,if_neg good,if_pos yb,if_neg he,if_pos (free he yb),le_refl]
      · simp [reward,good,yb]
  · by_cases h : c
    · rw [if_pos h]
      obtain ⟨y,yb,hy⟩ := h
      have lo := lower y hy.1
      by_cases he : e
      · have ok : x∈D ∧ y∉D := ⟨he.1,hy.2 he⟩
        simpa [reward,he,ok,yb] using lo
      · simp only [if_neg he,zero_add]
        simp only [reward,if_pos yb] at lo
        omega
    · rw [if_neg h,add_zero]
      by_cases he : e
      · obtain ⟨y,pr,yd⟩ := he.2
        have lo := lower y pr
        simp only [reward,if_pos (And.intro he.1 yd)] at lo
        rw [if_pos he]
        omega
      · simp [he]

theorem score_formula (G : SimpleGraph V) (r : V) (D B : Finset V) :
    score G r D B=(entries G r D).card+(children G r D B).card := by
  classical
  simp [score,local_score_formula,sum_add_distrib,entries,children]

theorem children_union (G : SimpleGraph V) (r : V) (D B C : Finset V) :
    children G r D (B∪C)=children G r D B∪children G r D C := by
  classical
  ext x
  simp only [children,mem_filter,mem_union,mem_erase,mem_univ,and_true]
  constructor
  · rintro ⟨xr,y,hy,allow⟩
    exact hy.elim (fun yb => Or.inl ⟨xr,y,yb,allow⟩) (fun yc => Or.inr ⟨xr,y,yc,allow⟩)
  · rintro (⟨xr,y,yb,allow⟩|⟨xr,y,yc,allow⟩)
    · exact ⟨xr,y,Or.inl yb,allow⟩
    · exact ⟨xr,y,Or.inr yc,allow⟩

#print axioms local_score_formula
#print axioms score_formula
#print axioms children_union
end Minimal180.HigherRank
