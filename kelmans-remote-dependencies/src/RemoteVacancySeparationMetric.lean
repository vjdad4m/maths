import RemoteVacancySeparation
import Mathlib.Combinatorics.SimpleGraph.Metric

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteVacancySeparationMetric
open RemoteVacancyReach (Packing Slides OneCleanup)
open RemoteVacancySeparation (holes UnitPotential one_cleanup_separation_bound)
variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem graph_dist_potential {G : SimpleGraph V} (conn : G.Connected) (a : V) :
    UnitPotential G (G.dist a) := by
  intro x y e
  have xy := dist_eq_one_iff_adj.mpr e
  have yx := dist_eq_one_iff_adj.mpr e.symm
  have one := conn.dist_triangle (u:=a) (v:=y) (w:=x)
  have two := conn.dist_triangle (u:=a) (v:=x) (w:=y)
  rw [yx] at one
  rw [xy] at two
  exact ⟨one,two⟩

/-- Direct graph-distance form: even nonmonotone one-tile transport
cannot bring a sufficiently isolated original vacancy into a completion
without spending linearly many slides. -/
theorem distance_requires_slides {G : SimpleGraph V} (conn : G.Connected)
    {P Q F : RemoteVacancySeparation.Fam V} (hp : Packing G P) (hf : Packing G F) (full : F.biUnion id=univ)
    {a : V} (ah : a∈holes P) (d : Nat)
    (far : ∀ x∈holes P,x≠a→d≤G.dist a x)
    {n : Nat} (steps : Slides n P Q) (clean : OneCleanup Q F) :
    d≤3*(n+1)+1 :=
  one_cleanup_separation_bound hp hf full (graph_dist_potential conn a)
    ah (dist_self) d far steps clean

#print axioms distance_requires_slides
end KelmansCactus.AtomicBridge.RemoteVacancySeparationMetric
