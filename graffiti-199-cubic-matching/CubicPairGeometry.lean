import CubicEdgeCuts

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- The two degree-three ends of an edge, with disjoint outside
neighborhoods. The four outside vertices may have any degrees and edges. -/
structure CubicEdge (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  adjacent : G.Adj u v
  degree_u : G.degree u = 3
  degree_v : G.degree v = 3
  no_common : ∀ x, ¬ (G.Adj x u ∧ G.Adj x v)

namespace CubicEdge

variable (P Q : CubicEdge G)

def low (b : Bool) : V := if b then P.v else P.u

theorem low_adj (b : Bool) : G.Adj (P.low b) (P.low (!b)) := by
  cases b
  · exact P.adjacent
  · exact P.adjacent.symm

noncomputable def ports : Finset V := edgeBoundary G P.u P.v

theorem mem_ports {x : V} :
    x ∈ P.ports ↔ (∀ b : Bool, x ≠ P.low b) ∧ ∃ b : Bool, G.Adj x (P.low b) := by
  rw [ports,mem_edgeBoundary]
  constructor
  · rintro ⟨xu,xv,(u|v)⟩
    · exact ⟨fun b => by cases b; exact xu; exact xv, false,u⟩
    · exact ⟨fun b => by cases b; exact xu; exact xv, true,v⟩
  · rintro ⟨distinct,b,edge⟩
    exact ⟨distinct false,distinct true,by cases b; exact Or.inl edge; exact Or.inr edge⟩

theorem low_not_port (b : Bool) : P.low b ∉ P.ports :=
  fun h => (P.mem_ports.mp h).1 b rfl

theorem neighbor_half {x : V} (hx : x ∈ P.ports) :
    ∃ b : Bool, G.Adj x (P.low b) ∧ ¬ G.Adj x (P.low (!b)) := by
  obtain ⟨_,b,e⟩ := P.mem_ports.mp hx
  refine ⟨b,e,?_⟩
  intro opp
  cases b
  · exact P.no_common x ⟨e,opp⟩
  · exact P.no_common x ⟨opp,e⟩

theorem ports_card : P.ports.card = 4 := by
  classical
  let A := (G.neighborFinset P.u).erase P.v
  let B := (G.neighborFinset P.v).erase P.u
  have ac : A.card = 2 := by
    change ((G.neighborFinset P.u).erase P.v).card = 2
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr P.adjacent),
      G.card_neighborFinset_eq_degree,P.degree_u]
  have bc : B.card = 2 := by
    change ((G.neighborFinset P.v).erase P.u).card = 2
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr P.adjacent.symm),
      G.card_neighborFinset_eq_degree,P.degree_v]
  have dis : Disjoint A B := Finset.disjoint_left.mpr fun x a b =>
    P.no_common x ⟨((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp a).2).symm,
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp b).2).symm⟩
  change (A ∪ B).card = 4
  rw [Finset.card_union_of_disjoint dis,ac,bc]

def region : Set V := {P.u,P.v} ∪ (↑P.ports : Set V)

theorem low_mem_region (b : Bool) : P.low b ∈ P.region := by
  cases b <;> simp [low,region]

theorem low_neighbor_mem_region {x : V} {b : Bool} (edge : G.Adj (P.low b) x) :
    x ∈ P.region := by
  by_cases off : ∀ i : Bool, x ≠ P.low i
  · exact Or.inr (P.mem_ports.mpr ⟨off,b,edge.symm⟩)
  · push_neg at off
    obtain ⟨i,rfl⟩ := off
    exact P.low_mem_region i

theorem not_mem_region {x : V} (p : x ∉ P.ports) (off : ∀ i : Bool, x ≠ P.low i) :
    x ∉ P.region := by
  rintro (h|h)
  · rcases (show x = P.u ∨ x = P.v from by simpa using h) with h|h
    · exact off false h
    · exact off true h
  · exact p h

/-- The two edges induce exactly a two-edge matching on their four lows. -/
structure Apart : Prop where
  distinct : ∀ a b : Bool, P.low a ≠ Q.low b
  no_cross : ∀ a b : Bool, ¬ G.Adj (P.low a) (Q.low b)

theorem Apart.no_low_in_other_port {P Q : CubicEdge G} (A : P.Apart Q) (b : Bool) :
    Q.low b ∉ P.ports := by
  intro h
  obtain ⟨_,a,edge⟩ := P.mem_ports.mp h
  exact A.no_cross a b edge.symm

theorem Apart.symm {P Q : CubicEdge G} (A : P.Apart Q) : Q.Apart P :=
  ⟨fun a b => (A.distinct b a).symm,fun a b edge => A.no_cross b a edge.symm⟩

theorem Apart.no_low_in_other_region {P Q : CubicEdge G} (A : P.Apart Q) (b : Bool) :
    Q.low b ∉ P.region :=
  P.not_mem_region (A.no_low_in_other_port b) (fun a => (A.distinct a b).symm)

theorem Apart.private_port_outside_other_region {P Q : CubicEdge G} (A : P.Apart Q)
    {x : V} (p : x ∈ P.ports) (q : x ∉ Q.ports) :
    x ∉ Q.region :=
  Q.not_mem_region q (fun b eq => A.no_low_in_other_port b (eq ▸ p))

noncomputable def regionFinset : Finset V := by
  classical
  exact insert P.u (insert P.v P.ports)

theorem mem_regionFinset {x : V} : x ∈ P.regionFinset ↔ x ∈ P.region := by
  classical
  simp [regionFinset,region,or_assoc]

theorem region_card_le : P.regionFinset.card ≤ 6 := by
  classical
  change (insert P.u (insert P.v P.ports)).card ≤ 6
  have h₁ := Finset.card_insert_le P.u (insert P.v P.ports)
  have h₂ := Finset.card_insert_le P.v P.ports
  have h₃ := P.ports_card
  omega

noncomputable def commonPorts : Finset V := by
  classical
  exact P.ports ∩ Q.ports

end CubicEdge

#print axioms CubicEdge.ports_card
#print axioms CubicEdge.Apart.no_low_in_other_region

end Graffiti199Depleted
