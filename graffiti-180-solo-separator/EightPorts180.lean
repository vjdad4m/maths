import FourPorts180
import EightResult180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals

noncomputable abbrev N0 : Finset V := {3,4,6,7}

theorem neighbors_port : ∀ x,x∈N0 ↔ G.Adj 0 x := by decide
theorem outer_port : outer (0:V) N0={1,2,5} := by decide

/-- Of the six possible distinct port pairs, exactly two pass the
component test, for every proper starting coloring of the outside. -/
theorem exact_port_pairs (c : V→Bool) (cp : ProperOn G (outer 0 N0) c) (u v : V)
    (un : u∈N0) (vn : v∈N0) (uv : u≠v) :
    PortsFit G (outer 0 N0) {u,v} c ↔ ({u,v}:Finset V)={3,6} ∨ ({u,v}:Finset V)={3,4} := by
  let W (i j : V) := insert (0:V) (outer 0 N0∪{i,j})
  have outside : ∀ x∈outer (0:V) N0,¬G.Adj 0 x := by decide
  have ports : ∀ x∈({u,v}:Finset V),G.Adj 0 x :=
    fun x xm => (neighbors_port x).mp ((insert_subset un (singleton_subset_iff.mpr vn)) xm)
  rw [←ports_iff G 0 _ _ c outside ports cp]
  change TwoColor G (W u v) ↔ _
  have two := (show ∀ i∈N0,∀ j∈N0,i≠j → (univ\W i j).card=2 by decide) u un v vn uv
  have eq : univ\(univ\W u v)=W u v := Finset.sdiff_sdiff_eq_self (subset_univ _)
  have law := exact_pairs.2 (univ\W u v) two
  rw [eq] at law
  rw [law]
  exact (show ∀ i∈N0,∀ j∈N0,i≠j → (univ\W i j∈pairs ↔
    ({i,j}:Finset V)={3,6} ∨ ({i,j}:Finset V)={3,4}) by decide) u un v vn uv

theorem four_port_regression :
    (∀ H⊆N0,Indep G H → H.card≤2) ∧ Protected G 2 false A ∧
    (∀ c : V→Bool,ProperOn G (univ\X) c → ∀ Z : Finset V,A⊆Z → 6≤Z.card →
      ∀ e : V→Bool,ProperOn G Z e → (5:V)∈Z ∧ c 1≠c 2 ∧ e 1=e 2) := by
  have cap (H : Finset V) (sub : H⊆N0) (hi : Indep G H) : H.card≤2 := by
    apply two_edges_cap G (3:V) 7 4 6 (by decide) (by decide) H _ hi
    exact sub.trans (by decide : N0⊆({3,7}∪{4,6}:Finset V))
  have ak : (0:V)∈A∩insert 2 (parity G 2 false) := by rw [data.2.1];decide
  refine ⟨cap,(four_ports_iff G data.1 (by decide) 2 false A data.2.2.1 0 ak N0 neighbors_port
    (by decide) budget_value cap).mpr ?_,recoloring_required⟩
  let c (v : V) := decide (v=5)
  have cp : ProperOn G (outer 0 N0) c := by unfold ProperOn;decide
  exact ⟨c,cp,3,by decide,6,by decide,by decide,(exact_port_pairs c cp 3 6 (by decide) (by decide)
    (by decide)).mpr (Or.inl rfl)⟩

#print axioms exact_port_pairs
#print axioms four_port_regression
end Minimal180.PairRepair.Eight
