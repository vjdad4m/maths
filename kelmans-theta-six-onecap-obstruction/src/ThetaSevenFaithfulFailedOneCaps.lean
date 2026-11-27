import ThetaSevenFaithfulFixture
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulFailedOneCaps
open ThetaSevenFaithfulFixture (original)

abbrev CapX := Fin 10
abbrev P := Fin 5
def extEdges : List (CapX×CapX) :=
  [(0,6),(0,7),(1,6),(1,8),(2,5),(2,7),(3,5),(3,6),(4,5),(4,8),(7,8)]

def trip (k : Fin 6) : P×P×CapX :=
  if k=0 then (0,2,7) else if k=1 then (1,4,8) else if k=2 then (0,3,6)
  else if k=3 then (1,3,6) else if k=4 then (2,3,5) else (3,4,5)

def idx (j : P) : CapX := ⟨j.val,by have h:=j.isLt; omega⟩

def failedEdges (k : Fin 6) : List (CapX×CapX) :=
  extEdges ++ [(idx (trip k).1,idx (trip k).2.1)] ++
    ((List.finRange 5).filter
      (fun x=>x != (trip k).1 && x != (trip k).2.1)).map (fun x=>(idx x,9))

private theorem no_failed_loop : ∀ k x,(x,x)∉failedEdges k := by decide

def failed (k : Fin 6) : SimpleGraph CapX where
  Adj a b := (a,b)∈failedEdges k ∨ (b,a)∈failedEdges k
  symm := fun _ _ h=>h.elim Or.inr Or.inl
  loopless a h := no_failed_loop k a (h.elim id id)

instance (k : Fin 6) : DecidableRel (failed k).Adj := fun x y=>
  inferInstanceAs (Decidable ((x,y)∈failedEdges k ∨ (y,x)∈failedEdges k))

private theorem full_cubic : ∀ k x,(failed k).degree x=3 := by decide

theorem all_six_incident_onecaps_fail (k : Fin 6) :
    ¬SquareCap.SmallTrivial (failed k) := by
  intro h
  let a := idx (trip k).1
  let b := idx (trip k).2.1
  let c := (trip k).2.2
  have tri : (failed k).Adj a b ∧ (failed k).Adj b c ∧ (failed k).Adj c a := by
    have check : ∀ k : Fin 6,
      (failed k).Adj (idx (trip k).1) (idx (trip k).2.1) ∧
      (failed k).Adj (idx (trip k).2.1) (trip k).2.2 ∧
      (failed k).Adj (trip k).2.2 (idx (trip k).1) := by decide
    exact check k
  exact TwinObstruction.no_triangle h (by decide) tri.1 tri.2.1 tri.2.2
    (full_cubic k a).le (full_cubic k b).le (full_cubic k c).le

private def oldNum (i : Fin 9) : Fin 16 := ⟨i.val+7,by have h:=i.isLt; omega⟩
private def extNum (i : Fin 9) : CapX := i.castSucc

theorem enumerates_exact_exterior :
    ∀ a b : Fin 9,original.Adj (oldNum a) (oldNum b) ↔
      (extNum a,extNum b)∈extEdges ∨ (extNum b,extNum a)∈extEdges := by decide

#print axioms enumerates_exact_exterior
#print axioms all_six_incident_onecaps_fail
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulFailedOneCaps
