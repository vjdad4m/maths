import FourRingCyclicGeometry
import FourRingGirthGeometry

open Finset SimpleGraph
namespace KelmansCactus.FourRingStandardEquivalence
open NearPerfectEquivalence PathSlides FourRingCutAux FourRingCyclicEquivalence
open FourRingGirthEquivalence FourRingGirthGeometry
noncomputable section
universe u

/-- The order-divisible-by-six, cubic, 3-connected Kelmans domain,
with no cyclic cut of size at most three and extended girth ≥g. -/
def StandardDomain {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (g : ℕ) : Prop :=
  Domain G ∧ NoCyclicCutBelowFour G ∧ (g:ℕ∞)≤G.egirth

theorem domain_equiv {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (g : ℕ) : StandardDomain G g ↔ DomainAtGirth G g := by
  constructor
  · rintro ⟨dom,cyc,gi⟩
    exact ⟨⟨dom,(small_trivial_iff_no_cyclic_cut G dom.1).mpr cyc⟩,(noCycles_iff_egirth g).mpr gi⟩
  · rintro ⟨⟨dom,cyc⟩,gi⟩
    exact ⟨dom,(small_trivial_iff_no_cyclic_cut G dom.1).mp cyc,(noCycles_iff_egirth g).mp gi⟩

def ExactFactors (g : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    StandardDomain G g → KelmansStarter.HasP3Factor G

def UniformlyVanishing (g : ℕ) : Prop :=
  ∀ scale : ℕ,∃ minOrder : ℕ,
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    StandardDomain G g → minOrder≤Fintype.card V →
      ∃ P : Parts V,PackIn G univ P ∧ scale*vacancies P≤Fintype.card V

def UniformlyBounded (g b : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    StandardDomain G g → ∃ P : Parts V,PackIn G univ P ∧ vacancies P≤b

/-- In the cyclically 4-edge-connected Kelmans domain at any
fixed girth threshold, a uniform sublinear vacancy bound is
equivalent to each graph in the same class having a P₃-factor. -/
theorem uniformly_vanishing_iff_exact (g : ℕ) :
    UniformlyVanishing.{u} g ↔ ExactFactors.{u} g := by
  simpa only [UniformlyVanishing,ExactFactors,domain_equiv,VanishingAtGirth,UniversalAtGirth]
    using vanishing_equiv_at_girth.{u} g

theorem uniformly_bounded_iff_exact (g b : ℕ) :
    UniformlyBounded.{u} g b ↔ ExactFactors.{u} g := by
  simpa only [UniformlyBounded,ExactFactors,domain_equiv,BoundedAtGirth,UniversalAtGirth]
    using bounded_equiv_at_girth.{u} g b

#print axioms domain_equiv
#print axioms uniformly_vanishing_iff_exact
#print axioms uniformly_bounded_iff_exact
end
end KelmansCactus.FourRingStandardEquivalence
