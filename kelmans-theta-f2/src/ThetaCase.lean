import ThetaGeometry
import ThetaModes
import ThetaTransfer

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCase
open PentagonCap (attach pathCap path_cap_cubic SmallFourTrivial)
open PentagonProfile (Port)
open ThetaGeometry (good_theta_cap_of_cyclic5)
open ThetaModes (CyclicZ5Promise theta_modes_of_cyclic_z5)
open ThetaTransfer (Target theta_factor_of_two_modes)
open SquareCap (FactorOn omitEdge SmallTrivial)
noncomputable section

universe u

/-- Two pentagons sharing the length-two 0-6-3 arm. -/
def theta : SimpleGraph (Fin 7) where
  Adj a b := (a.val<6 ∧ b.val<6 ∧ ((a.val+1)%6=b.val ∨ (b.val+1)%6=a.val)) ∨
    (a=6 ∧ (b=0∨b=3)) ∨ (b=6 ∧ (a=0∨a=3))
  symm := by
    intro a b h
    rcases h with ⟨la,lb,e⟩|l|r
    · exact Or.inl ⟨lb,la,e.elim Or.inr Or.inl⟩
    · exact Or.inr (Or.inr l)
    · exact Or.inr (Or.inl r)
  loopless := by
    have audit : ∀ a : Fin 7, ¬ ((a.val<6 ∧ a.val<6 ∧
        ((a.val+1)%6=a.val ∨ (a.val+1)%6=a.val)) ∨
        (a=6 ∧ (a=0∨a=3)) ∨ (a=6 ∧ (a=0∨a=3))) := by decide
    exact audit

instance : DecidableRel theta.Adj := fun a b=>
  inferInstanceAs (Decidable ((a.val<6 ∧ b.val<6 ∧ ((a.val+1)%6=b.val ∨ (b.val+1)%6=a.val)) ∨
    (a=6 ∧ (b=0∨b=3)) ∨ (b=6 ∧ (a=0∨a=3))))

/-- Port numbers are the path cap's role numbers. The singleton
at 0 transfers to ring vertex 1, kept leaf 1/4 to ring vertices 2/5,
discarded leaf 2/3 to ring vertex 4 or deleted vertex 6. -/
def arm (j : Port) : Fin 7 :=
  if j=0 then 1 else if j=1 then 2 else if j=2 then 4 else if j=3 then 6 else 5

variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev ambient (G : SimpleGraph V) (p : Port↪V) := attach G theta p arm

/-- Conditional F2 for this exact adjacent-contact 7-vertex theta.
In cyclic5 the only obstructions to the fixed cap are edges between
one of the two specified pairs of exterior contacts.
This theorem requires their nonadjacency; it does not assert that
these two constraints can always be met by permuting the roles. -/
theorem theta_f2_of_cyclic_z5 (z5 : CyclicZ5Promise.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ambient G p).Adj]
    (cub : ∀ x,(ambient G p).degree x=3)
    (small : SmallTrivial (ambient G p)) (small4 : SmallFourTrivial (ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (safe14 : ¬G.Adj (p 1) (p 4)) (safe23 : ¬G.Adj (p 2) (p 3)) :
    FactorOn (omitEdge (ambient G p) (Sum.inr 5) (Sum.inr 0)) (univ.erase (Sum.inr 6)) := by
  letI : DecidableRel (attach G theta p arm).Adj := ‹DecidableRel (ambient G p).Adj›
  classical
  let orig := ambient G p
  let K := omitEdge orig (Sum.inr 5) (Sum.inr 0)
  have capGood : SmallTrivial (pathCap G p) := good_theta_cap_of_cyclic5 small small4 cub safe14 safe23
  have capCub := path_cap_cubic (G:=G) (P:=theta) (p:=p) (r:=arm) (fun v => cub (Sum.inl v))
  have modes := theta_modes_of_cyclic_z5 z5 capCub capGood order
  have shape : Target G K (p 0) (p 1) (p 4) := by
    constructor
    · exact ⟨by exact (by decide : theta.Adj 0 1), by simp⟩
    · exact ⟨by exact (by decide : theta.Adj 1 2), by simp⟩
    · exact ⟨by exact (by decide : theta.Adj 2 3), by simp⟩
    · exact ⟨by exact (by decide : theta.Adj 3 4), by simp⟩
    · exact ⟨by exact (by decide : theta.Adj 4 5), by simp⟩
    · exact ⟨⟨0,rfl,rfl⟩,by simp⟩
    · exact ⟨⟨1,rfl,rfl⟩,by simp⟩
    · exact ⟨⟨4,rfl,rfl⟩,by simp⟩
    · intro v w vw
      exact ⟨vw,by simp⟩
  exact theta_factor_of_two_modes shape
    (fun e => (by decide : (1:Port)≠4) (p.injective e)) modes

#print axioms theta_f2_of_cyclic_z5

end
end KelmansCactus.AtomicBridge.ThetaCase
