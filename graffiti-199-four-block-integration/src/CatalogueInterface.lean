import OneSharedIntegration

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/- These predicates use the definitions in the public Proof199K13.lean.
   The separate namespace permits a replay without its low-connectivity proof. -/
def ConnectivityAtLeast [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected

noncomputable def vertexConnectivity [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.range (Fintype.card V)).filter (ConnectivityAtLeast G)).sup id

def Traceable (G : SimpleGraph V) : Prop :=
  ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ x, x ∈ p.support

theorem traceable_iff_hamiltonian_walk [DecidableEq V] :
    Traceable G ↔ ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  constructor
  · rintro ⟨u,v,p,path,all⟩
    exact ⟨u,v,p,path.isHamiltonian_of_mem all⟩
  · rintro ⟨u,v,p,ham⟩
    exact ⟨u,v,p,ham.isPath,ham.mem_support⟩

theorem connectivityAtLeast_vertexConnectivity [Fintype V] [Nonempty V] :
    ConnectivityAtLeast G (vertexConnectivity G) := by
  classical
  let orders := (Finset.range (Fintype.card V)).filter (ConnectivityAtLeast G)
  have hz : ConnectivityAtLeast G 0 := ⟨Fintype.card_pos,by simp⟩
  have h0 : 0 ∈ orders := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz.1,hz⟩
  obtain ⟨k,member,maximum⟩ := Finset.exists_mem_eq_sup orders ⟨0,h0⟩ id
  change ConnectivityAtLeast G (orders.sup id)
  rw [maximum]
  exact (Finset.mem_filter.mp member).2

/-- The recovered branch at the catalogue connectivity and nontraceability
interface. The cover and crossing data are the inputs from the upstream
minimum-counterexample reduction. -/
theorem excludes_four_forbidden_highs_at_connectivity_three
    [Fintype V] [DecidableRel G.Adj] (F : FourBlockPacking G)
    (connectivity : vertexConnectivity G = 3)
    (forbidden : Finset V) (count : forbidden.card = 4)
    (highOnly : ∀ v ∈ forbidden, v ∈ pairPorts F.depleted)
    (membership : ∀ v ∈ pairPorts F.depleted,
      v ∈ forbidden ↔ v ∈ singletonPorts F.first ∪ singletonPorts F.second)
    (order : 15 ≤ Fintype.card V)
    (cross : CrossingBetweenSurvivingEdges G) (nontraceable : ¬ Traceable G) : False := by
  classical
  letI : Nonempty V := ⟨F.first.f 0⟩
  have k3 : ConnectivityAtLeast G 3 := connectivity ▸ connectivityAtLeast_vertexConnectivity
  have below (D : Finset V) (h : D.card < 3) : (G.induce {v | v ∉ D}).Preconnected :=
    (k3.2 D h).preconnected
  exact F.excludes_four_forbidden_highs forbidden count highOnly membership order below cross
    (fun ham => nontraceable (traceable_iff_hamiltonian_walk.mpr ham))

#print axioms traceable_iff_hamiltonian_walk
#print axioms connectivityAtLeast_vertexConnectivity
#print axioms excludes_four_forbidden_highs_at_connectivity_three

end Graffiti199Depleted.Catalogue
