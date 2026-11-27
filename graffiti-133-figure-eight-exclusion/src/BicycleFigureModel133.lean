import BicycleHubChannels133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

def figureRel (n m i j : Nat) : Prop :=
  if i=0 then (j=1 ∨ j=n ∨ j=n+1 ∨ j=n+m) else
  if j=0 then (i=1 ∨ i=n ∨ i=n+1 ∨ i=n+m) else
  if i≤n ∧ j≤n then (i+1=j ∨ j+1=i) else
  if n < i ∧ n < j then (i+1=j ∨ j+1=i) else False

instance (n m i j : Nat) : Decidable (figureRel n m i j) := by unfold figureRel; infer_instance

structure FigureModel {V : Type*} (G : SimpleGraph V) (n m : Nat) where
  f : Fin (n+m+1) → V
  inj : Function.Injective f
  adj : ∀ i j, G.Adj (f i) (f j) ↔ figureRel n m i.val j.val

variable {V : Type*} {G : SimpleGraph V} {h : V}
def TwoHubPaths.figureModel (P : TwoHubPaths G h) : FigureModel G P.one.n P.two.n := by
  let n := P.one.n
  let m := P.two.n
  have n2 : 2≤n := P.one.nontriv
  have m2 : 2≤m := P.two.nontriv
  let label (i : Fin (n+m+1)) : V :=
    if i.val=0 then h else
      if le : i.val≤n then (P.one.f ⟨i.val-1,by omega⟩).val
      else (P.two.f ⟨i.val-(n+1),by omega⟩).val
  have hub (i : Fin (n+m+1)) (e : i.val=0) : label i=h := if_pos e
  have left (i : Fin (n+m+1)) (e : i.val≠0) (le : i.val≤n) :
      label i=(P.one.f ⟨i.val-1,by omega⟩).val := by unfold label; rw [if_neg e,dif_pos le]
  have right (i : Fin (n+m+1)) (gt : n < i.val) :
      label i=(P.two.f ⟨i.val-(n+1),by omega⟩).val := by
    have ne : i.val≠0 := by omega
    unfold label
    rw [if_neg ne,dif_neg (not_le_of_gt gt)]
  have insideLeft (i : Fin (n+m+1)) (e : i.val≠0) (le : i.val≤n) : label i∈P.S := by
    rw [left i e le]
    exact (P.one.f _).property
  have insideRight (i : Fin (n+m+1)) (gt : n < i.val) : label i∈P.T := by
    rw [right i gt]
    exact (P.two.f _).property
  refine ⟨label,?_,?_⟩
  · intro i j eq
    by_cases iz : i.val=0
    · by_cases jz : j.val=0
      · exact Fin.ext (iz.trans jz.symm)
      · by_cases jl : j.val≤n
        · have inS := insideLeft j jz jl
          rw [←eq,hub i iz] at inS
          exact (P.offS inS).elim
        · have inT := insideRight j (by omega)
          rw [←eq,hub i iz] at inT
          exact (P.offT inT).elim
    · by_cases jz : j.val=0
      · by_cases il : i.val≤n
        · have inS := insideLeft i iz il
          rw [eq,hub j jz] at inS
          exact (P.offS inS).elim
        · have inT := insideRight i (by omega)
          rw [eq,hub j jz] at inT
          exact (P.offT inT).elim
      · by_cases il : i.val≤n <;> by_cases jl : j.val≤n
        · rw [left i iz il,left j jz jl] at eq
          have q := congrArg Fin.val (P.one.path.1 (Subtype.ext eq))
          change i.val-1=j.val-1 at q
          exact Fin.ext (by omega)
        · exact (Finset.disjoint_left.mp P.sep (insideLeft i iz il)
            (eq.symm ▸ insideRight j (by omega))).elim
        · exact (Finset.disjoint_left.mp P.sep (insideLeft j jz jl)
            (eq ▸ insideRight i (by omega))).elim
        · rw [right i (by omega),right j (by omega)] at eq
          have q := congrArg Fin.val (P.two.path.1 (Subtype.ext eq))
          change i.val-(n+1)=j.val-(n+1) at q
          exact Fin.ext (by omega)
  · intro i j
    change G.Adj (label i) (label j) ↔ figureRel n m i.val j.val
    by_cases iz : i.val=0 <;> by_cases jz : j.val=0
    · rw [hub i iz,hub j jz]
      simp [figureRel,iz,jz]
      omega
    · rw [hub i iz]
      by_cases jl : j.val≤n
      · rw [left j jz jl,P.one.attached]
        simp only [figureRel,iz,if_true]
        change (j.val-1=0 ∨ j.val-1+1=n) ↔ _
        omega
      · rw [right j (by omega),P.two.attached]
        simp only [figureRel,iz,if_true]
        change (j.val-(n+1)=0 ∨ j.val-(n+1)+1=m) ↔ _
        omega
    · rw [hub j jz,G.adj_comm]
      by_cases il : i.val≤n
      · rw [left i iz il,P.one.attached]
        simp only [figureRel,iz,if_false,jz,if_true]
        change (i.val-1=0 ∨ i.val-1+1=n) ↔ _
        omega
      · rw [right i (by omega),P.two.attached]
        simp only [figureRel,iz,if_false,jz,if_true]
        change (i.val-(n+1)=0 ∨ i.val-(n+1)+1=m) ↔ _
        omega
    · by_cases il : i.val≤n <;> by_cases jl : j.val≤n
      · rw [left i iz il,left j jz jl]
        simp only [figureRel,iz,jz,if_false,il,jl,and_self,if_true]
        have eq := induced_adj_both_orders P.one.path ⟨i.val-1,by omega⟩ ⟨j.val-1,by omega⟩
        rw [show G.Adj (P.one.f _).val (P.one.f _).val ↔ _ from eq]
        change (i.val-1+1=j.val-1 ∨ j.val-1+1=i.val-1) ↔ _
        omega
      · simp only [figureRel,iz,jz,if_false,il,jl,and_false,
          show ¬n < i.val from not_lt_of_ge il,false_and]
        exact ⟨P.noCross _ (insideLeft i iz il) _ (insideRight j (by omega)),False.elim⟩
      · simp only [figureRel,iz,jz,if_false,il,jl,false_and,
          show ¬n < j.val from not_lt_of_ge jl,and_false]
        exact ⟨fun e => P.noCross _ (insideLeft j jz jl) _ (insideRight i (by omega)) e.symm,False.elim⟩
      · rw [right i (by omega),right j (by omega)]
        simp only [figureRel,iz,jz,if_false,il,jl,false_and,
          show n < i.val by omega,show n < j.val by omega,and_self,if_true]
        have eq := induced_adj_both_orders P.two.path ⟨i.val-(n+1),by omega⟩ ⟨j.val-(n+1),by omega⟩
        rw [show G.Adj (P.two.f _).val (P.two.f _).val ↔ _ from eq]
        change (i.val-(n+1)+1=j.val-(n+1) ∨ j.val-(n+1)+1=i.val-(n+1)) ↔ _
        omega

#print axioms TwoHubPaths.figureModel
end Graffiti133Bicycle
