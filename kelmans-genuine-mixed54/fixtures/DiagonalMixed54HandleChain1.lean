import RemoteNumericHandleChecks
set_option maxRecDepth 12000
set_option maxHeartbeats 0

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
open RemoteCutCertificate (Table)
open SquareCap (SmallTrivial)
open RemoteNumericHandleChecks (fromList select relabel)
def T4 : Table 4 :=
  fromList [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] (by decide) (by decide)
theorem cert4 : (∀ x,T4.graph.degree x=3) ∧ SmallTrivial T4.graph :=
  ⟨by decide,T4.cyclic_four (order:=[1,2,3]) (root:=0) (by decide)⟩


def T6 : Table 6 :=
  fromList [(0,1),(1,2),(0,3),(2,3),(1,4),(3,4),(0,5),(2,5),(4,5)] (by decide) (by decide)
private def pick6 := select T4 1 3 0 2 (by decide) (by decide) (by decide)
theorem cert6 : (∀ x,T6.graph.degree x=3) ∧ SmallTrivial T6.graph :=
  RemoteNumericHandle.step T4 pick6 T6 (by rfl) cert4

def T8 : Table 8 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(2,5),(4,5),(1,6),(4,6),(0,7),(3,7),(6,7)] (by decide) (by decide)
private def pick8 := select T6 1 4 0 3 (by decide) (by decide) (by decide)
theorem cert8 : (∀ x,T8.graph.degree x=3) ∧ SmallTrivial T8.graph :=
  RemoteNumericHandle.step T6 pick8 T8 (by rfl) cert6

def T10 : Table 10 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(2,5),(4,6),(0,7),(3,7),(6,7),(1,8),(6,8),(4,9),(5,9),(8,9)] (by decide) (by decide)
private def pick10 := select T8 1 6 4 5 (by decide) (by decide) (by decide)
theorem cert10 : (∀ x,T10.graph.degree x=3) ∧ SmallTrivial T10.graph :=
  RemoteNumericHandle.step T8 pick10 T10 (by rfl) cert8

def T12 : Table 12 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(0,7),(3,7),(6,7),(6,8),(4,9),(5,9),(8,9),(1,10),(8,10),(2,11),(5,11),(10,11)] (by decide) (by decide)
private def pick12 := select T10 1 8 2 5 (by decide) (by decide) (by decide)
theorem cert12 : (∀ x,T12.graph.degree x=3) ∧ SmallTrivial T12.graph :=
  RemoteNumericHandle.step T10 pick12 T12 (by rfl) cert10

def T14 : Table 14 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(4,9),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(7,13),(12,13)] (by decide) (by decide)
private def pick14 := select T12 8 9 0 7 (by decide) (by decide) (by decide)
theorem cert14 : (∀ x,T14.graph.degree x=3) ∧ SmallTrivial T14.graph :=
  RemoteNumericHandle.step T12 pick14 T14 (by rfl) cert12

def T16 : Table 16 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(7,13),(12,14),(13,14),(4,15),(9,15),(14,15)] (by decide) (by decide)
private def pick16 := select T14 12 13 4 9 (by decide) (by decide) (by decide)
theorem cert16 : (∀ x,T16.graph.degree x=3) ∧ SmallTrivial T16.graph :=
  RemoteNumericHandle.step T14 pick16 T16 (by rfl) cert14

end KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
