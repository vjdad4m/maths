import AffineHostCuts
import ControlBudget
import FourRingCyclicEquivalence

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open AffineBase FourRingBudget FourRingReplica FourRingReplica.Layout FourRingCutAux
open FourRingCyclicEquivalence NearPerfectEquivalence
noncomputable section
universe u

/-- Plain factors at order 0 mod 6 in the cubic cyclic-four class
imply adjacent-pair deletion factors at order 2 mod 6 within the
same class. Unlike the unrestricted three-pole constructions, the
affine host introduces no nontrivial three-edge cut. -/
theorem cyclic4_factor_implies_t2 (promise : CyclicUniversal.{u})
    {U : Type u} [Fintype U] [DecidableEq U] {A : SimpleGraph U} [DecidableRel A.Adj]
    (cub : ∀ x,A.degree x=3) (conn : KelmansStarter.ThreeConnected A)
    (closed : SmallTrivial A) (res : Fintype.card U%6=2)
    (r : Bool→U) (edge : A.Adj (r false) (r true)) :
    KelmansStarter.HasP3Factor (minor A r) := by
  classical
  have big := conn.1
  have nf := triangle_free_of_small_trivial A cub (by omega) closed
  have free (x : U) (a : A.Adj (r false) x) (b : A.Adj (r true) x) : False :=
    nf _ _ _ edge b a.symm
  let L := from_triangle_free_edge A r cub edge free
  let H := AffineHost.graph L
  have C : SmallTrivial H := AffineHost.preserves_small_trivial L cub closed
  have D : ∀ v,H.degree v=3 := AffineHost.cubic L cub
  have eq := AffineHost.card_host L
  have HH : CyclicDomain H := by
    have h1 : 4≤Fintype.card (AffineHost.V r) := by omega
    have div : 6∣Fintype.card (AffineHost.V r) := by omega
    exact ⟨⟨D,three_connected_of_small_trivial H D h1 C,div⟩,C⟩
  have res' : 3∣Fintype.card (Piece r) := by
    rw [L.piece_card]
    omega
  have f := promise (AffineHost.V r) H HH
  exact ControlBudget.cell_factor_of_host_factor (minor A r) H
    (by decide : Fintype.card Point=9) (by decide : Fintype.card Line=12) res'
    (fun _ _ _ _ e=>AffineHost.separate L e) (fun _ _ _ e=>AffineHost.inside L e) f

#print axioms cyclic4_factor_implies_t2
end
end KelmansCactus.AtomicBridge
