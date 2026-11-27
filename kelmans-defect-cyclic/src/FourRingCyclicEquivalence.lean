import FourRingCapDomain

open Finset SimpleGraph
namespace KelmansCactus.FourRingCyclicEquivalence
open FourRingReplica FourRingReplica.Layout FourRingPropagation FourRingCutAux NearPerfectEquivalence PathSlides
noncomputable section
universe u

/-- Cyclically four-edge-connected cubic graphs in the cut formulation:
there is no boundary of at most three edges with at least two vertices
on each side. Order is divisible by six, as in Kelmans's conjecture. -/
def CyclicDomain {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := Domain G ∧ SmallTrivial G

def CyclicUniversal : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    CyclicDomain G → KelmansStarter.HasP3Factor G

def CyclicVanishing : Prop :=
  ∀ scale : ℕ,∃ minOrder : ℕ,
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    CyclicDomain G → minOrder≤Fintype.card V →
      ∃ P : Parts V,PackIn G univ P ∧ scale*vacancies P≤Fintype.card V

def CyclicBounded (b : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    CyclicDomain G → ∃ P : Parts V,PackIn G univ P ∧ vacancies P≤b

private theorem minOrder {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) : 6≤Fintype.card V := by
  obtain ⟨t,et⟩ := dom.2.2
  have h := dom.2.1.1
  omega

private theorem root_choice {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : CyclicDomain G) :
    ∃ r : Bool→V,G.Adj (r false) (r true) ∧
      ∀ u,G.Adj (r false) u→G.Adj (r true) u→False := by
  have order := minOrder dom.1
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card V)
  have nc : 0<(G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree,dom.1.1]
    decide
  obtain ⟨y,ym⟩ := card_pos.mp nc
  have edge := (mem_neighborFinset G x y).mp ym
  let r : Bool→V := fun b=>if b then y else x
  have triangle := triangle_free_of_small_trivial G dom.1.1 (by omega) dom.2
  exact ⟨r,edge,fun u xU yU=>triangle x y u edge yU xU.symm⟩

/-- A bad cap in the cyclic-four class produces a family of
bad paired rings with a positive vacancy density. All graph
domain conditions are checked, not assumed of the ring. -/
theorem cyclic_family_gap {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : CyclicDomain G)
    (r : Bool→V) (edge : G.Adj (r false) (r true))
    (noCommon : ∀u,G.Adj (r false) u→G.Adj (r true) u→False)
    (bad : ¬KelmansStarter.HasP3Factor G)
    (m : ℕ) [NeZero m] (m2 : 2≤m) (mDiv : 6∣m) :
    let L := from_triangle_free_edge G r dom.1.1 edge noCommon
    let ring := spin_circular m2
    let H := L.graph (spin m) ring.fixed
    CyclicDomain H ∧
      Fintype.card (Host (Fin m) r)=m*(Fintype.card V-2) ∧
      ∀ P : Parts (Host (Fin m) r),PackIn H univ P →
        Fintype.card (Host (Fin m) r)≤(Fintype.card V-2)*vacancies P := by
  let L := from_triangle_free_edge G r dom.1.1 edge noCommon
  let ring : Circular (spin m) := spin_circular m2
  let H := L.graph (spin m) ring.fixed
  change CyclicDomain H ∧ _ ∧ _
  have cub : ∀ v,H.degree v=3 := L.cubic _ _ dom.1.1
  have cc : SmallTrivial H := L.preserves_small_trivial _ ring dom.1.1 dom.2
  have eq : Fintype.card (Host (Fin m) r)=m*(Fintype.card V-2) := by
    rw [L.host_card,Fintype.card_fin]
  have min := minOrder dom.1
  have four : 4≤Fintype.card (Host (Fin m) r) := by
    rw [eq]
    have s : 4≤Fintype.card V-2 := by omega
    exact (show 4≤m*4 from by omega).trans (Nat.mul_le_mul_left m s)
  have conn := three_connected_of_small_trivial H cub four cc
  have divH : 6∣Fintype.card (Host (Fin m) r) := by
    rw [eq]
    exact dvd_mul_of_dvd_left mDiv _
  refine ⟨⟨⟨cub,conn,divH⟩,cc⟩,eq,?_⟩
  intro P ok
  have residue : Fintype.card V%3=0 := by
    obtain ⟨t,e⟩ := dom.1.2.2
    omega
  have h : Fintype.card (Fin m) ≤ vacancies P :=
    Nat.le_of_not_gt (fun lt=>bad (L.factor_of_few_vacancies _ ring.fixed ok residue lt))
  rw [eq,mul_comm]
  change (Fintype.card V-2)*m≤(Fintype.card V-2)*vacancies P
  rw [Fintype.card_fin] at h
  exact Nat.mul_le_mul_left _ h

theorem cyclic_vanishing_equiv : CyclicVanishing.{u} ↔ CyclicUniversal.{u} := by
  constructor
  · intro promise V _ _ G _ dom
    classical
    by_contra bad
    obtain ⟨r,edge,noCommon⟩ := root_choice dom
    let size := Fintype.card V-2
    obtain ⟨n,answer⟩ := promise (size+1)
    let m := 6*(n+1)
    letI : NeZero m := ⟨by dsimp [m]; omega⟩
    have two : 2≤m := by dsimp [m]; omega
    let L := from_triangle_free_edge G r dom.1.1 edge noCommon
    let ring := spin_circular two
    let H := L.graph (spin m) ring.fixed
    obtain ⟨domain,order,gap⟩ := cyclic_family_gap dom r edge noCommon bad m two ⟨n+1,rfl⟩
    have mL : n≤m := by dsimp [m]; omega
    have ss : 1≤size := by have q:=minOrder dom.1; dsimp [size]; omega
    have large : n≤Fintype.card (Host (Fin m) r) := by
      rw [order]
      change n≤m*size
      exact mL.trans (by simpa using (Nat.mul_le_mul_left m ss))
    obtain ⟨P,ok,upper⟩ := answer (Host (Fin m) r) H domain large
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

theorem cyclic_bounded_equiv (b : ℕ) : CyclicBounded.{u} b ↔ CyclicUniversal.{u} := by
  constructor
  · intro hb
    apply cyclic_vanishing_equiv.mp
    intro s
    refine ⟨s*b,?_⟩
    intro V _ _ G _ d large
    obtain ⟨P,ok,h⟩ := hb V G d
    exact ⟨P,ok,(Nat.mul_le_mul_left s h).trans large⟩
  · intro yes V _ _ G _ d
    obtain ⟨P,tile,disjoint,cov⟩ := yes V G d
    exact ⟨P,⟨⟨tile,disjoint,rfl⟩,subset_univ _⟩,by simp [vacancies,cov]⟩

#print axioms cyclic_family_gap
#print axioms cyclic_vanishing_equiv
#print axioms cyclic_bounded_equiv
end
end KelmansCactus.FourRingCyclicEquivalence
