import NearPerfectReplicaConnected
import PrismTrap

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectEquivalence
open NearPerfectReplica PathSlides
noncomputable section
universe u

/-- Exact order-divisible-by-six Kelmans domain, and quantification over
all finite simple graphs in a single universe. -/
def Domain {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  (∀ v,G.degree v=3) ∧ KelmansStarter.ThreeConnected G ∧ 6∣Fintype.card V

def Universal : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Domain G → KelmansStarter.HasP3Factor G

theorem universal_iff_starter :
    Universal.{u} ↔
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        KelmansStarter.Conjecture G := by
  constructor
  · intro all V _ _ G _ cub con dvd
    exact all V G ⟨cub,con,dvd⟩
  · intro all V _ _ G _ h
    exact all V G h.1 h.2.1 h.2.2

def vacancies {V : Type u} [Fintype V] [DecidableEq V]
    (P : Parts V) : ℕ := ((univ : Finset V)\P.biUnion id).card

def BoundedVacancies (h : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Domain G → ∃ P : Parts V, PackIn G univ P ∧ vacancies P≤h

/-- Uniform sublinear vacancy form: for every positive integer scale,
all sufficiently large graphs admit a packing with vacancy fraction
at most the reciprocal of that scale. No limit machinery is needed. -/
def VanishingVacancyFraction : Prop :=
  ∀ scale : ℕ, ∃ minOrder : ℕ,
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Domain G → minOrder≤Fintype.card V →
        ∃ P : Parts V, PackIn G univ P ∧ scale*vacancies P≤Fintype.card V

private theorem full_pack {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (f : KelmansStarter.HasP3Factor G) :
    ∃ P : Parts V, PackIn G univ P ∧ vacancies P=0 := by
  obtain ⟨P,tile,disj,cov⟩ := f
  exact ⟨P,⟨⟨tile,disj,rfl⟩,subset_univ _⟩,by simp [vacancies,cov]⟩

private theorem baseOrder (t : ℕ) :
    Fintype.card (PrismTrap.Vertex t)=18*t+6 := by
  simp only [PrismTrap.Vertex,Fintype.card_sum,Fintype.card_fin,PrismTrap.m]
  omega

private theorem baseDiv (t : ℕ) : 6∣Fintype.card (PrismTrap.Vertex t) := by
  rw [baseOrder]
  exact ⟨3*t+1,by omega⟩

private theorem root_exists {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) : Nonempty V :=
  Fintype.card_pos_iff.mp (by have zz := dom.2.1.1; omega)

private theorem chooseDomain {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) (r : V) (t : ℕ) :
    Domain (Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)).graph := by
  let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
  exact ⟨L.cubic dom.1,L.three_connected dom.2.1 (PrismTrap.three_connected t),
    by rw [host_card]; exact dvd_mul_of_dvd_left (baseDiv t) _⟩

/-- Quantitative contrapositive: one bad graph yields an unbounded
family in the same domain, all with a uniform positive vacancy
fraction. The family has exact orders (18t+6)(n−1). -/
theorem replica_family_gap {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (dom : Domain G) (r : V) (t : ℕ)
    (bad : ¬KelmansStarter.HasP3Factor G) :
    let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
    Domain L.graph ∧
      Fintype.card (Host (PrismTrap.Vertex t) r)=(18*t+6)*(Fintype.card V-1) ∧
      ∀ P : Parts (Host (PrismTrap.Vertex t) r), PackIn L.graph univ P →
        Fintype.card (Host (PrismTrap.Vertex t) r) ≤ 2*(Fintype.card V-1)*vacancies P := by
  let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
  refine ⟨chooseDomain dom r t,by rw [host_card,baseOrder],?_⟩
  intro P ok
  have k := baseOrder t
  have ct : 2≤Fintype.card (PrismTrap.Vertex t) := by omega
  have rr : Fintype.card V%3=0 := by
    obtain ⟨j,jEq⟩ := dom.2.2
    omega
  have need : Fintype.card (PrismTrap.Vertex t) ≤ 2*vacancies P :=
    Nat.le_of_not_gt (fun tooFew=>bad (L.close_of_few_vacancies ok rr ct tooFew))
  rw [host_card]
  calc
    _ ≤ (2*vacancies P)*(Fintype.card V-1) := Nat.mul_le_mul_right _ need
    _ = _ := by ac_rfl

/-- Every constant uniform defect bound on the divisible-order domain is
equivalent to a full factor guarantee. In particular set h=3. -/
theorem bounded_equiv (h : ℕ) : BoundedVacancies.{u} h ↔ Universal.{u} := by
  constructor
  · intro bd V _ _ G _ dom
    obtain ⟨r⟩ := root_exists dom
    let t := h+1
    let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
    obtain ⟨P,ok,m⟩ := bd (Host (PrismTrap.Vertex t) r) L.graph (chooseDomain dom r t)
    have rr : Fintype.card V%3=0 := by
      obtain ⟨k,kEq⟩ := dom.2.2
      omega
    have card : Fintype.card (PrismTrap.Vertex t)=18*(h+1)+6 := baseOrder t
    have ct : 2≤Fintype.card (PrismTrap.Vertex t) := by omega
    apply L.close_of_few_vacancies ok rr ct
    change 2*vacancies P < Fintype.card (PrismTrap.Vertex t)
    omega
  · intro yes V _ _ G _ dom
    obtain ⟨P,ok,zero⟩ := full_pack (yes V G dom)
    exact ⟨P,ok,by omega⟩

/-- A uniform vanishing vacancy fraction is equivalent to exact perfect
packing in the Kelmans domain. The proof amplifies a putative fixed
bad brick to arbitrarily large valid cubic 3-connected graphs. -/
theorem vanishing_equiv : VanishingVacancyFraction.{u} ↔ Universal.{u} := by
  constructor
  · intro asym V _ _ G _ dom
    obtain ⟨r⟩ := root_exists dom
    let size := Fintype.card V-1
    obtain ⟨n,report⟩ := asym (2*size+1)
    let t := n+1
    let L := Layout.fromCubic G (PrismTrap.graph t) r dom.1 (PrismTrap.cubic t)
    have sz : 1≤size := by have z:=dom.2.1.1; dsimp [size]; omega
    have k : Fintype.card (PrismTrap.Vertex t)=18*(n+1)+6 := baseOrder t
    have ct : 2≤Fintype.card (PrismTrap.Vertex t) := by omega
    have large : n≤Fintype.card (Host (PrismTrap.Vertex t) r) := by
      rw [host_card]
      change n≤Fintype.card (PrismTrap.Vertex t)*size
      exact (show n≤Fintype.card (PrismTrap.Vertex t) from by omega)
        |>.trans (by simpa only [Nat.mul_one] using
          (Nat.mul_le_mul_left (Fintype.card (PrismTrap.Vertex t)) sz))
    obtain ⟨P,ok,m⟩ := report (Host (PrismTrap.Vertex t) r) L.graph (chooseDomain dom r t) large
    have rr : Fintype.card V%3=0 := by
      obtain ⟨j,jEq⟩ := dom.2.2
      omega
    apply L.close_of_few_vacancies ok rr ct
    change 2*vacancies P < Fintype.card (PrismTrap.Vertex t)
    by_cases bad : Fintype.card (PrismTrap.Vertex t)≤2*vacancies P
    · have positive : 0<vacancies P := by omega
      have multiply := Nat.mul_le_mul_right size bad
      rw [host_card,Nat.add_mul,Nat.one_mul] at m
      change 2*size*vacancies P+vacancies P ≤ Fintype.card (PrismTrap.Vertex t)*size at m
      have easy : 2*size*vacancies P = 2*vacancies P*size := by ac_rfl
      rw [easy] at m
      omega
    · exact Nat.lt_of_not_ge bad
  · intro yes scale
    refine ⟨0,?_⟩
    intro V _ _ G _ dom _
    obtain ⟨P,ok,zero⟩ := full_pack (yes V G dom)
    exact ⟨P,ok,by rw [zero,Nat.mul_zero]; exact Nat.zero_le _⟩

#print axioms universal_iff_starter
#print axioms replica_family_gap
#print axioms bounded_equiv
#print axioms vanishing_equiv
end
end KelmansCactus.NearPerfectEquivalence
