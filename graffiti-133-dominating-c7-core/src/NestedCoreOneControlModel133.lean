import NestedCoreOneControlSpec133
import NestedCorePrivateWeightedFitHelpers133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133PrivateGeneric
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V}

def embedCore (i : Fin 8) : Fin 16 := Fin.castLE (by decide) i
def embedPrivate (i : Fin 8) : Fin 16 := ⟨i.val+8,by have := i.isLt; omega⟩

def stitch (core priv : Fin 8→V) (i : Fin 16) : V :=
  if hi : i.val < 8 then core ⟨i.val,hi⟩ else priv ⟨i.val-8,by have := i.isLt; omega⟩

theorem stitch_injective {core priv : Fin 8→V} (ci : Function.Injective core)
    (dis : ∀ i j,priv i≠core j)
    (site : ∀ i j,G.Adj (priv i) (core j)↔i=j) : Function.Injective (stitch core priv) := by
  intro a b eq
  by_cases alo : a.val < 8 <;> by_cases blo : b.val < 8
  · rw [stitch,dif_pos alo,stitch,dif_pos blo] at eq
    exact Fin.ext (congrArg (fun i : Fin 8=>i.val) (ci eq))
  · rw [stitch,dif_pos alo,stitch,dif_neg blo] at eq
    exact (dis _ _ eq.symm).elim
  · rw [stitch,dif_neg alo,stitch,dif_pos blo] at eq
    exact (dis _ _ eq).elim
  · rw [stitch,dif_neg alo,stitch,dif_neg blo] at eq
    let i : Fin 8 := ⟨a.val-8,by have := a.isLt; omega⟩
    let j : Fin 8 := ⟨b.val-8,by have := b.isLt; omega⟩
    have ij : priv i=priv j := eq
    have adj := (site i i).mpr rfl
    have j_i := (site j i).mp (ij ▸ adj)
    have val : b.val-8=a.val-8 := congrArg Fin.val j_i
    exact Fin.ext (by omega)


def core (H : Hole G 7) (u : V) : Fin 8→V :=
  ![H.c 0,H.c 1,H.c 2,H.c 3,H.c 4,H.c 5,H.c 6,u]

def csite (i : Fin 7) : Fin 8 := Fin.castLE (by decide) i

theorem core_at_site (H : Hole G 7) (u : V) (i : Fin 7) : core H u (csite i)=H.c i := by
  fin_cases i <;> rfl

theorem core_injective (H : Hole G 7) (u : V) (uo : Outside H.c u) :
    Function.Injective (core H u) := by
  have hu (i : Fin 7) : H.c i≠u := (uo i).symm
  have eq (a b : Fin 7) : H.c a=H.c b↔a=b := H.inj.eq_iff
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [core,eq,hu,uo] at h ⊢ <;> exact uo _ h

def PrivateFor (G : SimpleGraph V) (core : Fin 8→V) (i : Fin 8) (x : V) : Prop :=
  (∀ j,x≠core j) ∧ ∀ j,G.Adj x (core j)↔i=j

def CoreFits (G : SimpleGraph V) (c : Fin 8→V) : Prop :=
  ∀ a b,G.Adj (c a) (c b)↔coreEdge (min a.val b.val) (max a.val b.val)=true

def CoreKnown (G : SimpleGraph V) (f : Fin 16→V) : Prop :=
  ∀ a b : Fin 16,a.val<8 ∨ b.val<8 →
    (G.Adj (f a) (f b)↔coreEdge (min a.val b.val) (max a.val b.val)=true)

theorem core_fits (H : Hole G 7) (u : V)
    (up : ∀ i : Fin 7,G.Adj u (H.c i)↔i=0 ∨ i=3) : CoreFits G (core H u) := by
  have un (i : Fin 7) : G.Adj (H.c i) u↔i=0 ∨ i=3 := (G.adj_comm _ _).trans (up i)
  intro a b
  fin_cases a <;> fin_cases b <;> simp [core,coreEdge,H.adj,up,un,Cyclic] <;> decide

theorem stitch_known {c p : Fin 8→V} (fit : CoreFits G c)
    (site : ∀ i j,G.Adj (p i) (c j)↔i=j) : CoreKnown G (stitch c p) := by
  intro a b h
  by_cases aa : a.val<8 <;> by_cases bb : b.val<8
  · rw [stitch,dif_pos aa,stitch,dif_pos bb]
    exact fit _ _
  · rw [stitch,dif_pos aa,stitch,dif_neg bb,G.adj_comm,site]
    have ab : a.val≤b.val := by omega
    simp only [coreEdge,Nat.min_eq_left ab,Nat.max_eq_right ab,
      show ¬b.val<7 by omega,show b.val≠7 by omega,if_false,decide_eq_true_eq,Fin.ext_iff]
    omega
  · rw [stitch,dif_neg aa,stitch,dif_pos bb,site]
    have ba : b.val≤a.val := by omega
    simp only [coreEdge,Nat.min_eq_right ba,Nat.max_eq_left ba,
      show ¬a.val<7 by omega,show a.val≠7 by omega,if_false,decide_eq_true_eq,Fin.ext_iff]
    omega
  · exact (h.elim aa bb).elim

theorem stitch_at_core (c p : Fin 8→V) (i : Fin 8) :
    stitch c p (embedCore i)=c i := by simp [stitch,embedCore,i.isLt]

theorem stitch_at_private (c p : Fin 8→V) (i : Fin 8) :
    stitch c p (embedPrivate i)=p i := by
  have no : ¬(embedPrivate i).val<8 := by simp [embedPrivate]
  rw [stitch,dif_neg no]
  congr 1

#print axioms core_fits
#print axioms stitch_known
end Graffiti133NestedOneControl
