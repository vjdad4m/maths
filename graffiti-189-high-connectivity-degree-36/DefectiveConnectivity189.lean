import DefectiveWideCut189
import ShoreConnectivity189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.DefectiveWideCut Graffiti189LongestPath.ShoreConnectivity
set_option warningAsError true
namespace Graffiti189LongestPath.DefectiveConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem defective_universal_shore_stays_connected (hc : G.Connected) (k : Nat)
    (A B U X : Finset V) (x : V)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (exactB : B.card≤k+1) (ab : Disjoint A B) (ub : Disjoint U B)
    (au : Disjoint A U) (large : k≤U.card) (kp : 0<k)
    (closedA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B)
    (closedU : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B)
    (cap : ∀ v,(DistanceTwo G v).card≤k+2)
    (root : ∀ v∈A,v=x ∨ G.Adj x v)
    (xa : X⊆A) (small : 3*X.card+6<A.card) :
    (G.induce ((↑(A\X)):Set V)).Connected := by
  have h := card_sdiff_add_card_eq_card xa
  apply connected_of_no_partition _ (card_pos.mp (by omega))
  exact fun C E part dis no => defective_shore_cut_no_split hc k A B U X C E x conn
    exactB ab ub au large kp closedA closedU cap root xa part dis no small

#print axioms defective_universal_shore_stays_connected
end Graffiti189LongestPath.DefectiveConnectivity
