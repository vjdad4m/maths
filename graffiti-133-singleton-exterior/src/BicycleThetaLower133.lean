import BicycleRelayNetworks133
import FirstBandFour133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem ThetaRelays.pair_size_lower (P : ThetaRelays G u v) (uv : u≠v)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) (k l : Fin 3) (ne : k≠l) :
    3≤(P.rel k).n+(P.rel l).n := by
  have bad01 (a b : Fin 3) (az : (P.rel a).n=0) (bo : (P.rel b).n=1) : False := by
    let x : Fin (P.rel b).n := ⟨0,by omega⟩
    have xu := ((P.rel b).attached x u (by simp)).mpr (Or.inl ⟨rfl,rfl⟩)
    have xv := ((P.rel b).attached x v (by simp)).mpr (Or.inr ⟨by change 0+1=(P.rel b).n; omega,rfl⟩)
    exact tri _ _ _ (P.direct.mpr ⟨a,az⟩) xv xu.symm
  have bad02 (a b : Fin 3) (az : (P.rel a).n=0) (bt : (P.rel b).n=2) : False := by
    let x : Fin (P.rel b).n := ⟨0,by omega⟩
    let y : Fin (P.rel b).n := ⟨1,by omega⟩
    have xy : x < y := by change (0:Nat)<1; decide
    have xu := ((P.rel b).attached x u (by simp)).mpr (Or.inl ⟨rfl,rfl⟩)
    have yv := ((P.rel b).attached y v (by simp)).mpr
      (Or.inr ⟨by change 1+1=(P.rel b).n; omega,rfl⟩)
    have ed := ((P.rel b).path.2 x y xy).mpr rfl
    have uy : u≠(P.rel b).f y := fun e=>(P.rel b).off y (e ▸ (by simp : u∈({u,v}:Finset V)))
    have bad := h4 u ((P.rel b).f y) v ((P.rel b).f x) uy (P.direct.mpr ⟨a,az⟩) yv.symm xu ed.symm
    exact (P.rel b).off x (bad ▸ (by simp : v∈({u,v}:Finset V)))
  by_cases large : 3≤(P.rel k).n+(P.rel l).n
  · exact large
  exfalso
  rcases (show
    ((P.rel k).n=0 ∧ (P.rel l).n=0) ∨
    ((P.rel k).n=0 ∧ (P.rel l).n=1) ∨
    ((P.rel k).n=1 ∧ (P.rel l).n=0) ∨
    ((P.rel k).n=0 ∧ (P.rel l).n=2) ∨
    ((P.rel k).n=2 ∧ (P.rel l).n=0) ∨
    ((P.rel k).n=1 ∧ (P.rel l).n=1) by omega) with
      ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
  · exact ne (P.atMostOneEmpty k l a b)
  · exact bad01 k l a b
  · exact bad01 l k b a
  · exact bad02 k l a b
  · exact bad02 l k b a
  · let x : Fin (P.rel k).n := ⟨0,by omega⟩
    let y : Fin (P.rel l).n := ⟨0,by omega⟩
    have xu := ((P.rel k).attached x u (by simp)).mpr (Or.inl ⟨rfl,rfl⟩)
    have xv := ((P.rel k).attached x v (by simp)).mpr
      (Or.inr ⟨by change 0+1=(P.rel k).n; omega,rfl⟩)
    have yu := ((P.rel l).attached y u (by simp)).mpr (Or.inl ⟨rfl,rfl⟩)
    have yv := ((P.rel l).attached y v (by simp)).mpr
      (Or.inr ⟨by change 0+1=(P.rel l).n; omega,rfl⟩)
    exact (P.sep k l ne x y).1 (h4 _ _ _ _ uv xu xv yu yv)

#print axioms ThetaRelays.pair_size_lower
end Graffiti133Bicycle
