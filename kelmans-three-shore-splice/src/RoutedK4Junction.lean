import RoutedLeafJunction
import TriangleTerminalDomain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCutAux FourRingCyclicEquivalence
noncomputable section
universe u
variable {V : Type u} [DecidableEq V]

/-- All cap-domain data and the old internal edges, with an explicit
choice of label for the added cap root. -/
structure CappedRegion (G : SimpleGraph V) (S : Finset V) (x : V) where
  H : SimpleGraph (↑(insert x S) : Type u)
  dec : DecidableRel H.Adj
  cubic : letI := dec; ∀ v,H.degree v=3
  conn : KelmansStarter.ThreeConnected H
  small : SmallTrivial H
  keep : ∀ v w (hv : v∈S) (hw : w∈S),
    H.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w
  rootOut : x∉S

namespace CappedRegion
variable {G : SimpleGraph V} {S : Finset V} {x : V} (A : CappedRegion G S x)

/-- A precisely specified root adjacency in the cap. -/
def rootAdj (p : V) :=
  ∃ hp : p∈S,A.H.Adj ⟨x,mem_insert_self _ _⟩ ⟨p,mem_insert_of_mem hp⟩

include A in
theorem zero (promise : CyclicUniversal.{u}) (res : Fintype.card (↑(insert x S):Type u)%6=4) :
    Closed G S := by
  letI := A.dec
  exact closed_atom_without_root promise A.rootOut A.H A.cubic A.conn A.small res A.keep

theorem one (promise : CyclicUniversal.{u}) (res : Fintype.card (↑(insert x S):Type u)%6=2)
    {d : V} (port : A.rootAdj d) : Closed G (S.erase d) := by
  letI := A.dec
  obtain ⟨hd,xd⟩ := port
  exact closed_atom_without_root_and_port promise A.rootOut hd A.H A.cubic A.conn A.small res xd A.keep

theorem two (promise : CyclicUniversal.{u}) (dvd : 6∣Fintype.card (↑(insert x S):Type u))
    {p q z : V} (pq : p≠q) (xp : A.rootAdj p) (xq : A.rootAdj q) (gz : G.Adj x z)
    (only : ∀ v,A.rootAdj v→v=p ∨ v=q ∨ v=z) : Closed G (insert x S) := by
  letI := A.dec
  obtain ⟨ps,e1⟩ := xp
  obtain ⟨qs,e2⟩ := xq
  have dom : CyclicDomain A.H := ⟨⟨A.cubic,A.conn,dvd⟩,A.small⟩
  exact close_shore_using_prescribed_leaf promise A.rootOut ps qs pq A.H dom e1 e2
    (fun v hv e=>only v ⟨hv,e⟩) A.keep gz

end CappedRegion

/-- Full conditional factor, without a triangle assumption, in the
(0,0,2) shore-residue case of a singleton junction. -/
theorem cyclic4_singleton_zero_zero_two [Fintype V]
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V}
    {A B C : Finset V} {x p q z : V}
    (capA : CappedRegion G A x) (capB : CappedRegion G B x) (capC : CappedRegion G C x)
    (divA : 6∣Fintype.card (↑(insert x A):Type u))
    (resB : Fintype.card (↑(insert x B):Type u)%6=4)
    (resC : Fintype.card (↑(insert x C):Type u)%6=4)
    (pq : p≠q) (xp : capA.rootAdj p) (xq : capA.rootAdj q) (xz : G.Adj x z)
    (only : ∀ v,capA.rootAdj v→v=p ∨ v=q ∨ v=z)
    (ab : Disjoint (insert x A) B) (ac : Disjoint (insert x A) C) (bc : Disjoint B C)
    (whole : insert x A∪B∪C=univ) :
    KelmansStarter.HasP3Factor G :=
  junction_two_zero_shores_using_leaf (capA.two promise divA pq xp xq xz only)
    (capB.zero promise resB) (capC.zero promise resC) ab ac bc whole

/-- Full conditional factor in the (1,2,2) shore-residue case.
The singleton x completes one order-two shore and the free port d
of the order-one shore completes the other. -/
theorem cyclic4_singleton_one_two_two [Fintype V]
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V} {A B C : Finset V}
    {x d p q z p' q' z' : V}
    (capA : CappedRegion G A x) (capB : CappedRegion G B d) (capC : CappedRegion G C x)
    (divA : 6∣Fintype.card (↑(insert x A):Type u))
    (divB : 6∣Fintype.card (↑(insert d B):Type u))
    (resC : Fintype.card (↑(insert x C):Type u)%6=2)
    (pq : p≠q) (xp : capA.rootAdj p) (xq : capA.rootAdj q) (xz : G.Adj x z)
    (onlyA : ∀ v,capA.rootAdj v→v=p ∨ v=q ∨ v=z)
    (pq' : p'≠q') (dp : capB.rootAdj p') (dq : capB.rootAdj q') (dz : G.Adj d z')
    (onlyB : ∀ v,capB.rootAdj v→v=p' ∨ v=q' ∨ v=z')
    (dC : capC.rootAdj d)
    (ab : Disjoint (insert x A) (insert d B))
    (ac : Disjoint (insert x A) (C.erase d))
    (bc : Disjoint (insert d B) (C.erase d))
    (whole : insert x A∪insert d B∪C.erase d=univ) :
    KelmansStarter.HasP3Factor G :=
  junction_two_two_shores_using_leaf (capA.two promise divA pq xp xq xz onlyA)
    (capB.two promise divB pq' dp dq dz onlyB) (capC.one promise resC dC) ab ac bc whole

#print axioms cyclic4_singleton_zero_zero_two
#print axioms cyclic4_singleton_one_two_two
end
end KelmansCactus.AtomicBridge
