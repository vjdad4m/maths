import PortHall189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.PortHall
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.ForeignPorts
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def shoreNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) : Finset V :=
  A.filter (fun a => ∃ s∈S,G.Adj s a)

/-- For a vertex across an exact cut, each adjacent matched port charges
a distinct distance-two vertex on the other side. In fact all neighbors
of those ports charge the budget, whether selected by the matching or not. -/
theorem opposite_port_budget (hc : G.Connected) (d k : Nat) (A B : Finset V)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (dis : Disjoint A B) (exactB : B.card=k) (large : k≤A.card)
    {z : V} (za : z∉A) (zb : z∉B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (cap : (EvenFrom G z).card≤d+1) :
    let S := B.filter (G.Adj z)
    S.card ≤ (shoreNeighbors G A S).card ∧
      (shoreNeighbors G A S).card + (DistanceTwo G z \ A).card ≤ d := by
  classical
  dsimp only
  let S := B.filter (G.Adj z)
  let N := shoreNeighbors G A S
  obtain ⟨f,inj,mem⟩ := ports_match_into_shore k A B conn dis exactB large za zb boundary
  let T : Finset ↥(B : Set V) := univ.filter (fun s => G.Adj z s.val)
  have s_eq : T.image Subtype.val = S := by
    ext u
    constructor
    · intro hu
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
      exact mem_filter.mpr ⟨v.property,(mem_filter.mp hv).2⟩
    · intro hu
      exact mem_image.mpr ⟨⟨u,(mem_filter.mp hu).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩,rfl⟩
  have sz : T.card=S.card := by
    rw [← s_eq,card_image_of_injective T Subtype.val_injective]
  have selected : T.image f ⊆ N := by
    intro a ha
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ha
    exact mem_filter.mpr ⟨(mem s).1,s.val,mem_filter.mpr ⟨s.property,(mem_filter.mp hs).2⟩,(mem s).2⟩
  have small := card_le_card selected
  rw [card_image_of_injective T inj,sz] at small
  have spend : N ⊆ DistanceTwo G z := by
    intro a ha
    obtain ⟨aA,b,bS,ba⟩ := mem_filter.mp ha
    have az : ¬G.Adj z a := fun e => zb (boundary a aA z za e.symm)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => za (e.symm ▸ aA)) az (mem_filter.mp bS).2 ba)
  have paid : Disjoint N (DistanceTwo G z \ A) := disjoint_left.mpr
    (fun _ hn hr => (mem_sdiff.mp hr).2 (mem_filter.mp hn).1)
  have total := card_le_card (union_subset spend (sdiff_subset : DistanceTwo G z \ A ⊆ DistanceTwo G z))
  rw [card_union_of_disjoint paid] at total
  exact ⟨small,total.trans (distanceTwo_le_of_even d z cap)⟩

omit [Fintype V] in
/-- Tight Hall is not a dead end: the neighbors of the tight port set
can replace those ports in another exact cut. -/
theorem switch_tight_ports (k : Nat) (A B S : Finset V)
    (dis : Disjoint A B) (exactB : B.card=k) (sub : S⊆B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (tight : (shoreNeighbors G A S).card=S.card) :
    let N := shoreNeighbors G A S
    let A' := A\N
    let B' := (B\S)∪N
    B'.card=k ∧ Disjoint A' B' ∧
      (∀ x∈A',∀ y∉A',G.Adj x y → y∈B') := by
  classical
  dsimp only
  let N := shoreNeighbors G A S
  let C := (B\S)∪N
  have dn : Disjoint (B\S) N := disjoint_left.mpr
    (fun _ hb hn => (disjoint_left.mp dis (mem_filter.mp hn).1 (mem_sdiff.mp hb).1))
  have c : C.card=k := by
    change ((B\S)∪N).card=k
    have eq := card_sdiff_add_card_eq_card sub
    rw [card_union_of_disjoint dn]
    change N.card=S.card at tight
    omega
  refine ⟨c,disjoint_left.mpr (fun _ hu hv => (mem_union.mp hv).elim
    (fun h => disjoint_left.mp dis (mem_sdiff.mp hu).1 (mem_sdiff.mp h).1)
    (mem_sdiff.mp hu).2),?_⟩
  intro u hu v hv e
  by_cases va : v∈A
  · exact mem_union.mpr (Or.inr (Classical.byContradiction (fun h => hv (mem_sdiff.mpr ⟨va,h⟩))))
  have vb := boundary u (mem_sdiff.mp hu).1 v va e
  have vs : v∉S := fun h => (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,v,h,e.symm⟩)
  exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨vb,vs⟩))

#print axioms opposite_port_budget
#print axioms switch_tight_ports


/-- A vertex seeing sufficiently many cut ports has no complementary
shore vertex at distance three or more. The missing ports, together
with the remaining even-distance budget, would otherwise be a smaller cut. -/
theorem majority_port_radius (hc : G.Connected) (d k : Nat) (A B : Finset V)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (dis : Disjoint A B) (exactB : B.card=k) (large : k≤A.card)
    {z : V} (za : z∉A) (zb : z∉B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (cap : (EvenFrom G z).card≤d+1)
    (many : d < 2*(B.filter (G.Adj z)).card) :
    (∀ w∉A,∀ _ : w∉B,G.dist z w≤2) ∧
    ((univ.filter (fun w => w∉A ∧ w∉B ∧ w≠z ∧ ¬G.Adj z w)).card +
      (B.filter (G.Adj z)).card ≤ d) := by
  classical
  let S := B.filter (G.Adj z)
  let D := DistanceTwo G z \ A
  have cost := opposite_port_budget hc d k A B conn dis exactB large za zb boundary cap
  have paid : S.card + D.card ≤ d := by
    change S.card ≤ (shoreNeighbors G A S).card ∧
      (shoreNeighbors G A S).card+D.card≤d at cost
    omega
  have radius : ∀ w∉A,∀ _ : w∉B,G.dist z w≤2 := by
    intro w wa wb
    apply Nat.le_of_not_gt
    intro dist
    let Y := univ.filter (fun u => u∉A ∧ u∉B ∧ 2<G.dist z u)
    let C := (B\S)∪D
    have wy : w∈Y := mem_filter.mpr ⟨mem_univ _,wa,wb,dist⟩
    have zy : z∉Y := fun hz => by have h := (mem_filter.mp hz).2.2.2; rw [dist_self] at h; omega
    have zc : z∉C := by
      intro h
      rcases mem_union.mp h with h|h
      · exact zb (mem_sdiff.mp h).1
      · have dd := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp h).1
        rw [dist_self] at dd; omega
    have dc : Disjoint Y C := disjoint_left.mpr (by
      intro u hu hu'
      obtain ⟨ua,ub,ud⟩ := (mem_filter.mp hu).2
      rcases mem_union.mp hu' with h|h
      · exact ub (mem_sdiff.mp h).1
      · have e := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp h).1
        omega)
    have bound : ∀ u∈Y,∀ v∉Y,G.Adj u v → v∈C := by
      intro u hu v hv ed
      obtain ⟨ua,ub,ud⟩ := (mem_filter.mp hu).2
      have va : v∉A := fun h => ub (boundary v h u ua ed.symm)
      have tr := hc.dist_triangle (u:=z) (v:=v) (w:=u)
      have edd : G.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ed.symm
      by_cases vb : v∈B
      · have ns : v∉S := by
          intro hs
          have e := SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_filter.mp hs).2)
          omega
        exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨vb,ns⟩))
      · have vd : G.dist z v≤2 := Nat.le_of_not_gt (fun h => hv (mem_filter.mpr ⟨mem_univ _,va,vb,h⟩))
        exact mem_union.mpr (Or.inr (mem_sdiff.mpr
          ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (by omega),va⟩))
    have cb := Graffiti189LongestPath.boundary_card_of_connectivity k conn wy zy zc dc bound
    have u := card_union_le (B\S) D
    have s := card_sdiff_add_card_eq_card (filter_subset (G.Adj z) B)
    change k≤((B\S)∪D).card at cb
    change (B\S).card+S.card=B.card at s
    change d<2*S.card at many
    omega
  refine ⟨radius,?_⟩
  have cover : (univ.filter (fun w => w∉A ∧ w∉B ∧ w≠z ∧ ¬G.Adj z w)) ⊆ D := by
    intro v hv
    obtain ⟨va,vb,vz,vNA⟩ := (mem_filter.mp hv).2
    have hi := radius v va vb
    have lo := hc.one_lt_dist_of_ne_of_not_adj vz.symm vNA
    exact mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (by omega),va⟩
  have c := card_le_card cover
  change (univ.filter (fun w => w∉A ∧ w∉B ∧ w≠z ∧ ¬G.Adj z w)).card+S.card≤d
  omega

#print axioms majority_port_radius
end Graffiti189LongestPath.ForeignPorts
