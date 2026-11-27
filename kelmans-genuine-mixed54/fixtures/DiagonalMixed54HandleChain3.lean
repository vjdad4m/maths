import DiagonalMixed54HandleChain2
set_option maxRecDepth 12000
set_option maxHeartbeats 0

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
open RemoteCutCertificate (Table)
open SquareCap (SmallTrivial)
open RemoteNumericHandleChecks (fromList select relabel)

def T30 : Table 30 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(8,12),(9,12),(0,13),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29)] (by decide) (by decide)
private def pick30 := select T28 7 27 13 26 (by decide) (by decide) (by decide)
theorem cert30 : (∀ x,T30.graph.degree x=3) ∧ SmallTrivial T30.graph :=
  RemoteNumericHandle.step T28 pick30 T30 (by rfl) cert28

def T32 : Table 32 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(9,12),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29),(0,30),(13,30),(8,31),(12,31),(30,31)] (by decide) (by decide)
private def pick32 := select T30 0 13 8 12 (by decide) (by decide) (by decide)
theorem cert32 : (∀ x,T32.graph.degree x=3) ∧ SmallTrivial T32.graph :=
  RemoteNumericHandle.step T30 pick32 T32 (by rfl) cert30

def T34 : Table 34 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(9,12),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29),(13,30),(8,31),(30,31),(12,32),(31,32),(0,33),(30,33),(32,33)] (by decide) (by decide)
private def pick34 := select T32 12 31 0 30 (by decide) (by decide) (by decide)
theorem cert34 : (∀ x,T34.graph.degree x=3) ∧ SmallTrivial T34.graph :=
  RemoteNumericHandle.step T32 pick34 T34 (by rfl) cert32

def T36 : Table 36 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(9,12),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29),(13,30),(30,31),(12,32),(31,32),(30,33),(32,33),(0,34),(33,34),(8,35),(31,35),(34,35)] (by decide) (by decide)
private def pick36 := select T34 0 33 8 31 (by decide) (by decide) (by decide)
theorem cert36 : (∀ x,T36.graph.degree x=3) ∧ SmallTrivial T36.graph :=
  RemoteNumericHandle.step T34 pick36 T36 (by rfl) cert34

def T38 : Table 38 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(9,12),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29),(13,30),(30,31),(12,32),(31,32),(30,33),(32,33),(33,34),(8,35),(34,35),(31,36),(35,36),(0,37),(34,37),(36,37)] (by decide) (by decide)
private def pick38 := select T36 31 35 0 34 (by decide) (by decide) (by decide)
theorem cert38 : (∀ x,T38.graph.degree x=3) ∧ SmallTrivial T38.graph :=
  RemoteNumericHandle.step T36 pick38 T38 (by rfl) cert36

def T40 : Table 40 :=
  fromList [(0,1),(1,2),(2,3),(3,4),(0,5),(4,6),(3,7),(6,8),(5,9),(1,10),(8,10),(2,11),(5,11),(10,11),(9,12),(12,14),(9,15),(14,15),(15,16),(14,17),(16,17),(17,18),(16,19),(18,19),(19,20),(13,21),(18,21),(20,21),(20,22),(22,23),(4,24),(22,24),(23,25),(24,25),(23,26),(25,27),(26,27),(7,28),(27,28),(13,29),(26,29),(28,29),(13,30),(30,31),(31,32),(30,33),(32,33),(33,34),(8,35),(34,35),(31,36),(35,36),(0,37),(34,37),(36,37),(6,38),(7,38),(12,39),(32,39),(38,39)] (by decide) (by decide)
private def pick40 := select T38 6 7 12 32 (by decide) (by decide) (by decide)
theorem cert40 : (∀ x,T40.graph.degree x=3) ∧ SmallTrivial T40.graph :=
  RemoteNumericHandle.step T38 pick40 T40 (by rfl) cert38

end KelmansCactus.AtomicBridge.DiagonalMixed54HandleChain
