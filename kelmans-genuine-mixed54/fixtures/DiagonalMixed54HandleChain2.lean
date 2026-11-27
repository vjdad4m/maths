import DiagonalMixed54HandleChain1
set_option maxRecDepth 12000
set_option maxHeartbeats 0

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
open RemoteCutCertificate (Table)
open SquareCap (SmallTrivial)
open RemoteNumericHandleChecks (fromList select relabel)

def T18 : Table 18 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(7,13),(12,14),(9,15),(14,15),(4,16),(15,16),(13,17),(14,17),(16,17)] (by decide) (by decide)
private def pick18 := select T16 4 15 13 14 (by decide) (by decide) (by decide)
theorem cert18 : (∀ x,T18.graph.degree x=3) ∧ SmallTrivial T18.graph :=
  RemoteNumericHandle.step T16 pick18 T18 (by rfl) cert16

def T20 : Table 20 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(7,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(13,18),(17,18),(4,19),(16,19),(18,19)] (by decide) (by decide)
private def pick20 := select T18 13 17 4 16 (by decide) (by decide) (by decide)
theorem cert20 : (∀ x,T20.graph.degree x=3) ∧ SmallTrivial T20.graph :=
  RemoteNumericHandle.step T18 pick20 T20 (by rfl) cert18

def T22 : Table 22 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(7,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(4,20),(19,20),(13,21),(18,21),(20,21)] (by decide) (by decide)
private def pick22 := select T20 4 19 13 18 (by decide) (by decide) (by decide)
theorem cert22 : (∀ x,T22.graph.degree x=3) ∧ SmallTrivial T22.graph :=
  RemoteNumericHandle.step T20 pick22 T22 (by rfl) cert20

def T24 : Table 24 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(4,22),(20,22),(7,23),(13,23),(22,23)] (by decide) (by decide)
private def pick24 := select T22 4 20 7 13 (by decide) (by decide) (by decide)
theorem cert24 : (∀ x,T24.graph.degree x=3) ∧ SmallTrivial T24.graph :=
  RemoteNumericHandle.step T22 pick24 T24 (by rfl) cert22

def T26 : Table 26 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(13,23),(22,23),(4,24),(22,24),(7,25),(23,25),(24,25)] (by decide) (by decide)
private def pick26 := select T24 4 22 7 23 (by decide) (by decide) (by decide)
theorem cert26 : (∀ x,T26.graph.degree x=3) ∧ SmallTrivial T26.graph :=
  RemoteNumericHandle.step T24 pick26 T26 (by rfl) cert24

def T28 : Table 28 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(13,26),(23,26),(7,27),(25,27),(26,27)] (by decide) (by decide)
private def pick28 := select T26 13 23 7 25 (by decide) (by decide) (by decide)
theorem cert28 : (∀ x,T28.graph.degree x=3) ∧ SmallTrivial T28.graph :=
  RemoteNumericHandle.step T26 pick28 T28 (by rfl) cert26

end KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
