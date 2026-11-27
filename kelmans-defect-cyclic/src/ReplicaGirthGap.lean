import ReplicaGirth

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectEquivalence
open NearPerfectReplica NearPerfectReplica.Layout PathSlides
noncomputable section
universe u

/-- The quantitatively bad family keeps a prescribed girth bound.
The original need only avoid cycles shorter than g−1 if all
remaining cycles of length g−1 are destroyed by the root deletion. -/
theorem replica_family_gap_with_girth
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) (r : V) (t g : ℕ)
    (near : NoCyclesBelow G (g-1))
    (inside : NoCyclesBelow (rootDeleted (A:=G) (r:=r)) g)
    (bad : ¬KelmansStarter.HasP3Factor G) :
    let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
    Domain L.graph ∧ NoCyclesBelow L.graph g ∧
      Fintype.card (Host (PrismTrap.Vertex t) r)=(18*t+6)*(Fintype.card V-1) ∧
      ∀ P : Parts (Host (PrismTrap.Vertex t) r), PackIn L.graph univ P →
        Fintype.card (Host (PrismTrap.Vertex t) r) ≤ 2*(Fintype.card V-1)*vacancies P := by
  let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
  obtain ⟨d,m,defect⟩ := replica_family_gap dom r t bad
  exact ⟨d,L.no_cycles_of_root_and_cell g near inside,m,defect⟩

def GirthUniversal (g : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Domain G → NoCyclesBelow G g → KelmansStarter.HasP3Factor G

def GirthVanishingVacancyFraction (g : ℕ) : Prop :=
  ∀ scale : ℕ, ∃ minOrder : ℕ,
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Domain G → NoCyclesBelow G g → minOrder≤Fintype.card V →
        ∃ P : Parts V, PackIn G univ P ∧ scale*vacancies P≤Fintype.card V

/-- For every fixed girth threshold, a uniform sublinear vacancy bound
on that class is equivalent to perfect packing throughout that class.
This does not transfer from a high-girth class to unrestricted graphs. -/
theorem girth_vanishing_equiv (g : ℕ) :
    GirthVanishingVacancyFraction.{u} g ↔ GirthUniversal.{u} g := by
  constructor
  · intro asym V _ _ G _ dom clean
    classical
    by_contra no
    have pos : 0<Fintype.card V := by have h:=dom.2.1.1; omega
    obtain ⟨r⟩ := Fintype.card_pos_iff.mp pos
    let size := Fintype.card V-1
    obtain ⟨n,report⟩ := asym (2*size+1)
    let t := n+1
    let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
    have near : NoCyclesBelow G (g-1) := fun k kk kg ki=>clean k kk (by omega) ki
    have inside : NoCyclesBelow (rootDeleted (A:=G) (r:=r)) g :=
      root_deletion_preserves_lower_bound g clean
    obtain ⟨d,c,order,defect⟩ := replica_family_gap_with_girth dom r t g near inside no
    have sz : 1≤size := by have h:=dom.2.1.1; dsimp [size]; omega
    have upper : n≤Fintype.card (Host (PrismTrap.Vertex t) r) := by
      rw [order]
      change n≤(18*(n+1)+6)*size
      exact (show n≤18*(n+1)+6 by omega).trans
        (by simpa only [Nat.mul_one] using (Nat.mul_le_mul_left (18*(n+1)+6) sz))
    obtain ⟨P,ok,cost⟩ := report (Host (PrismTrap.Vertex t) r) L.graph d c upper
    have low := defect P ok
    change Fintype.card (Host (PrismTrap.Vertex t) r)≤2*size*vacancies P at low
    rw [Nat.add_mul,Nat.one_mul] at cost
    have pzero : vacancies P=0 := by omega
    rw [pzero,Nat.mul_zero] at low
    have cpos : 0<Fintype.card (Host (PrismTrap.Vertex t) r) := by have hh:=d.2.1.1; omega
    omega
  · intro yes scale
    refine ⟨0,?_⟩
    intro V _ _ G _ d c _
    obtain ⟨P,tile,disj,cov⟩ := yes V G d c
    exact ⟨P,⟨⟨tile,disj,rfl⟩,subset_univ _⟩,by simp [vacancies,cov]⟩

#print axioms replica_family_gap_with_girth
#print axioms girth_vanishing_equiv
end
end KelmansCactus.NearPerfectEquivalence
