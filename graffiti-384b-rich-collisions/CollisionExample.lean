import CollisionBudget
namespace Graffiti384b.OddStars.CollisionExample
open Finset SimpleGraph EarPacking CollisionBudget
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
def N : Fin 11→Finset (Fin 11)
  | 0 => {3,4,5,6,7,8,10}
  | 1 => {4,5,6}
  | 2 => {5,6,9}
  | 3 => {0,5,6,7}
  | 4 => {0,1,5,6}
  | 5 => {0,1,2,3,4,6,8,9}
  | 6 => {0,1,2,3,4,5}
  | 7 => {0,3}
  | 8 => {0,5}
  | 9 => {2,5}
  | 10 => {0}
def graph : SimpleGraph (Fin 11) where
  Adj u v := v∈N u
  symm := by have eq : ∀u v : Fin 11,v∈N u → u∈N v := by decide
             exact fun _ _ h => eq _ _ h
  loopless := by have h : ∀v : Fin 11,v∉N v := by decide
                 exact h
instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v∈N u))

theorem profile : List.ofFn (trianglesAt graph)=[7,3,2,4,5,10,8,1,1,1,0] ∧
    rich graph={0,1,2,3,4,5,6} ∧ bound graph=6 ∧ graph.degree 10=1 := by decide

theorem connected : graph.Connected := by
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨5,fun v => ?_⟩
  have hub : ∀v : Fin 11,v=5 ∨ graph.Adj 5 v ∨
      ∃w : Fin 11,graph.Adj 5 w ∧ graph.Adj w v := by decide
  rcases hub v with rfl|a|⟨w,a,b⟩
  · exact Reachable.refl _
  · exact a.reachable
  · exact a.reachable.trans b.reachable

theorem supported : ∀u v : Fin 11,u≠10 → v≠10 → graph.Adj u v →
    ∃w : Fin 11,w≠10 ∧ graph.Adj u w ∧ graph.Adj v w := by decide

theorem losses : List.ofFn (fun v : Fin 7 => loss graph ⟨v.val,by omega⟩)=[2,0,1,1,0,2,0] ∧
    exceptional graph={0,5} := by
  unfold loss exceptional EarTriangleLoss.inside
  rw [profile.2.1]
  decide

theorem tight : gamma graph=6 := by
  have dom : TwoDominates graph ({0,1,2,3,5,10}:Finset (Fin 11)) :=
    (by decide : ∀v : Fin 11,v∉({0,1,2,3,5,10}:Finset (Fin 11)) → 2≤nbr graph v {0,1,2,3,5,10})
  have att : ∃d,TwoDominates graph d ∧ d.card=6 := ⟨_,dom,by decide⟩
  apply le_antisymm (Nat.sInf_le att)
  apply le_csInf ⟨6,att⟩
  rintro k ⟨d,hd,rfl⟩
  have all : ∀D : Finset (Fin 11),D.card≤5 → ∃v : Fin 11,v∉D ∧ nbr graph v D≤1 := by decide
  by_contra! low
  obtain ⟨v,vm,few⟩ := all d (by omega)
  have two := hd v vm
  omega

end Graffiti384b.OddStars.CollisionExample
#print axioms Graffiti384b.OddStars.CollisionExample.profile
#print axioms Graffiti384b.OddStars.CollisionExample.connected
#print axioms Graffiti384b.OddStars.CollisionExample.supported
#print axioms Graffiti384b.OddStars.CollisionExample.losses
#print axioms Graffiti384b.OddStars.CollisionExample.tight
