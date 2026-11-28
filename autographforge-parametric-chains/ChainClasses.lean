import ChainHubs
import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace TwinForcing
open SimpleGraph

theorem graphResidue_eq_residue {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : graphResidue G = Graffiti324.residue G := by
  apply graphResidue_of_list
  unfold degreeBag Graffiti324.degreeList
  rw [← Multiset.map_coe, Finset.coe_toList]
  congr 1
  funext v
  unfold SimpleGraph.degree
  congr 1
  ext w
  simp

private def fanColor {n m : ℕ} : PageVertex n m → Fin 2
  | .inl (i,_) => ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  | .inr (i,_) => ⟨(i.val+1) % 2, Nat.mod_lt _ (by decide)⟩

theorem fan_chain_two_colorable (n m : ℕ) : (chainGraph n m false).Colorable 2 := by
  refine ⟨Coloring.mk fanColor ?_⟩
  rintro (⟨i,b⟩|⟨i,p⟩) (⟨j,c⟩|⟨j,q⟩) e same
  · change chainHubAdj false (i,b) (j,c) at e
    have h := congrArg Fin.val same
    change i.val % 2 = j.val % 2 at h
    rcases e with ⟨bad,_,_⟩|⟨_,_,k⟩|⟨_,_,k⟩
    · cases bad
    · change i.val+1 = j.val at k
      omega
    · change j.val+1 = i.val at k
      omega
  · change i = j at e
    subst j
    have h := congrArg Fin.val same
    change i.val % 2 = (i.val+1) % 2 at h
    omega
  · change j = i at e
    subst j
    have h := congrArg Fin.val same
    change (i.val+1) % 2 = i.val % 2 at h
    omega
  · exact e

theorem chain_connected {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (spine : Bool) :
    (chainGraph n m spine).Connected := by
  let G := chainGraph n m spine
  let a : Fin n := ⟨0,hn⟩
  let z : Fin m := ⟨0,hm⟩
  have page (i : Fin n) (b : Bool) (p : Fin m) :
      G.Adj (.inl (i,b)) (.inr (i,p)) := rfl
  have lr (i : Fin n) : G.Reachable (.inl (i,false)) (.inl (i,true)) :=
    ((page i false z).reachable).trans (page i true z).reachable.symm
  have next (i j : Fin n) (h : i.val+1 = j.val) :
      G.Reachable (.inl (i,true)) (.inl (j,false)) :=
    SimpleGraph.Adj.reachable (G := G)
      (show chainHubAdj spine (i,true) (j,false) from Or.inr (Or.inl ⟨rfl,rfl,h⟩))
  have fromRoot (k : ℕ) (h : k < n) :
      G.Reachable (.inl (a,false)) (.inl (⟨k,h⟩,false)) := by
    induction k with
    | zero => exact .rfl
    | succ k ih =>
      let i : Fin n := ⟨k,by omega⟩
      exact (ih i.isLt).trans ((lr i).trans (next i ⟨k+1,h⟩ rfl))
  apply (connected_iff_exists_forall_reachable G).mpr
  refine ⟨.inl (a,false),?_⟩
  rintro (⟨i,b⟩|⟨i,p⟩)
  · cases b
    · exact fromRoot i.val i.isLt
    · exact (fromRoot i.val i.isLt).trans (lr i)
  · exact (fromRoot i.val i.isLt).trans (page i false p).reachable

#print axioms graphResidue_eq_residue
#print axioms fan_chain_two_colorable
#print axioms chain_connected
end TwinForcing
