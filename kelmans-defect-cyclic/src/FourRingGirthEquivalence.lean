import FourRingGirth

open Finset SimpleGraph KelmansCactus.NearPerfectReplica.Layout
namespace KelmansCactus.FourRingGirthEquivalence
open FourRingReplica FourRingReplica.Layout FourRingPropagation FourRingCyclicEquivalence
open FourRingCutAux NearPerfectEquivalence PathSlides
noncomputable section
universe u

def DomainAtGirth {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (g : ℕ) : Prop :=
  CyclicDomain G ∧ NoCyclesBelow G g

def UniversalAtGirth (g : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    DomainAtGirth G g → KelmansStarter.HasP3Factor G

def VanishingAtGirth (g : ℕ) : Prop :=
  ∀ scale : ℕ,∃ minOrder : ℕ,
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    DomainAtGirth G g → minOrder≤Fintype.card V →
      ∃ P : Parts V,PackIn G univ P ∧ scale*vacancies P≤Fintype.card V

def BoundedAtGirth (g b : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    DomainAtGirth G g → ∃ P : Parts V,PackIn G univ P ∧ vacancies P≤b

private theorem order_ge_six {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) : 6≤Fintype.card V := by
  obtain ⟨t,et⟩ := dom.2.2
  have h := dom.2.1.1
  omega

private theorem usable_edge {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : CyclicDomain G) :
    ∃ r : Bool→V,G.Adj (r false) (r true) ∧
      ∀ u,G.Adj (r false) u→G.Adj (r true) u→False := by
  have order := order_ge_six dom.1
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card V)
  have nc : 0<(G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree,dom.1.1]
    decide
  obtain ⟨y,ym⟩ := card_pos.mp nc
  have edge := (mem_neighborFinset G x y).mp ym
  let r : Bool→V := fun b=>if b then y else x
  have triangle := triangle_free_of_small_trivial G dom.1.1 (by omega) dom.2
  exact ⟨r,edge,fun u xU yU=>triangle x y u edge yU xU.symm⟩

/-- For any fixed girth threshold and cyclically four-edge-connected
cubic domain, uniformly vanishing vacancy density is equivalent
to the exact P₃-factor conjecture within that same class. -/
theorem vanishing_equiv_at_girth (g : ℕ) : VanishingAtGirth.{u} g ↔ UniversalAtGirth.{u} g := by
  constructor
  · intro promise V _ _ G _ dom
    classical
    by_contra bad
    obtain ⟨r,edge,noCommon⟩ := usable_edge dom.1
    let size := Fintype.card V-2
    obtain ⟨n,answer⟩ := promise (size+1)
    let m := 6*(n+1)
    letI : NeZero m := ⟨by dsimp [m]; omega⟩
    have two : 2≤m := by dsimp [m]; omega
    let L := from_triangle_free_edge G r dom.1.1.1 edge noCommon
    let ring := spin_circular two
    let H := L.graph (spin m) ring.fixed
    obtain ⟨domain,order,gap⟩ := cyclic_family_gap dom.1 r edge noCommon bad m two ⟨n+1,rfl⟩
    have dir := spin_distinct_directions (n:=m) (by dsimp [m]; omega)
    have full : DomainAtGirth H g := ⟨domain,L.preserves_girth_bound (spin m) dir g dom.2⟩
    have mL : n≤m := by dsimp [m]; omega
    have ss : 1≤size := by have q:=order_ge_six dom.1.1; dsimp [size]; omega
    have large : n≤Fintype.card (Host (Fin m) r) := by
      rw [order]
      change n≤m*size
      exact mL.trans (by simpa using (Nat.mul_le_mul_left m ss))
    obtain ⟨P,ok,upper⟩ := answer (Host (Fin m) r) H full large
    have lower := gap P ok
    change Fintype.card (Host (Fin m) r)≤size*vacancies P at lower
    rw [Nat.add_mul,Nat.one_mul] at upper
    have z : vacancies P=0 := by omega
    rw [z,Nat.mul_zero] at lower
    have positive : 0<Fintype.card (Host (Fin m) r) := by
      have q := domain.1.2.1.1
      omega
    omega
  · intro yes scale
    refine ⟨0,?_⟩
    intro V _ _ G _ d _
    obtain ⟨P,tile,disjoint,cov⟩ := yes V G d
    exact ⟨P,⟨⟨tile,disjoint,rfl⟩,subset_univ _⟩,by simp [vacancies,cov]⟩

/-- In particular, any one constant bound, even a large one,
forces P₃-factors in all members of the same restricted class. -/
theorem bounded_equiv_at_girth (g b : ℕ) : BoundedAtGirth.{u} g b ↔ UniversalAtGirth.{u} g := by
  constructor
  · intro hb
    apply (vanishing_equiv_at_girth g).mp
    intro s
    refine ⟨s*b,?_⟩
    intro V _ _ G _ d large
    obtain ⟨P,ok,h⟩ := hb V G d
    exact ⟨P,ok,(Nat.mul_le_mul_left s h).trans large⟩
  · intro yes V _ _ G _ d
    obtain ⟨P,tile,disjoint,cov⟩ := yes V G d
    exact ⟨P,⟨⟨tile,disjoint,rfl⟩,subset_univ _⟩,by simp [vacancies,cov]⟩

#print axioms vanishing_equiv_at_girth
#print axioms bounded_equiv_at_girth
end
end KelmansCactus.FourRingGirthEquivalence
