import CentralTwoPort
import CenteredCapExportZ5

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCyclicEquivalence
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A centered atom may send two leaves to disjoint core edges, provided
the rest of the core is itself factorable. An explicit instance of this
predicate is the two-companion repair on the Petersen quotient. -/
def CenteredGeometry (G : SimpleGraph V) (R : Finset V) (u v : V) : Prop :=
  ∃ a b, ({u,a}:Finset V)⊆R ∧ ({v,b}:Finset V)⊆R ∧
    Disjoint ({u,a}:Finset V) {v,b} ∧ G.Adj u a ∧ G.Adj v b ∧
    Closed G (R\({u,a}∪{v,b}))

/-- For a shore with three ports, two feasible core pairs share a pivot
port. Prescribe that port and keep both possible partners, rather than
assuming all three centered pairs are available in the atom. -/
theorem close_centered_core_at_pivot
    (promise : CyclicUniversal.{u}) {A R : Finset V} {x p y : V}
    (cap : CappedRegion G A x) (dvd : 6∣Fintype.card (↑(insert x A):Type u))
    (ar : Disjoint A R) (pp : cap.rootAdj p) (lp : G.Adj p y)
    (partners : ∀ q, q≠p → cap.rootAdj q →
      ∃ z, G.Adj q z ∧ CenteredGeometry G R y z) :
    Closed G (A∪R) := by
  obtain ⟨q,pq,hq,atom⟩ := cap.centered_export_at_port_z5 promise dvd pp
  obtain ⟨z,qz,a,b,ay,bz,sep,e1,e2,rest⟩ := partners q pq.symm hq
  exact join_two_singletons_to_two_edges pp.choose hq.choose pq ay bz sep ar lp e1 qz e2 atom rest

#print axioms close_centered_core_at_pivot
end KelmansCactus.AtomicBridge
