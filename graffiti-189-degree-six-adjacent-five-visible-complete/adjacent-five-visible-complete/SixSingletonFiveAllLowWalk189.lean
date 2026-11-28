import SixSingletonFiveAllLowCert189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow
open SimpleGraph SimpleGraph.Walk Finset
open private walk_of_chain from ArticulationClique189
set_option maxHeartbeats 9000000
set_option maxRecDepth 32768

def varEnds : Fin 18 → Fin 11 × Fin 11 := ![(0,1),(0,2),(1,2),
  (0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),
  (3,9),(3,10),(4,9),(4,10),(5,9),(5,10)]

def fixed : List (Fin 11 × Fin 11) := [(6,7),(6,8),(7,8),(6,9),(7,10),
  (0,6),(0,7),(1,6),(1,7),(2,6),(2,7)]

def good (r : Fin 49) (u v : Fin 11) : Prop :=
  (u,v)∈fixed ∨ (v,u)∈fixed ∨
    ∃ k : Fin 18,k.val∈requirement r ∧ (varEnds k=(u,v) ∨ varEnds k=(v,u))

instance (r : Fin 49) (u v : Fin 11) : Decidable (good r u v) := by unfold good; infer_instance

private theorem visits_valid : ∀ i : Fin 49,
    (visit i).Nodup ∧ (∀ j : Fin 11,j∈visit i) ∧
    (∃ j : Fin 11,(visit i).head?=some j ∧ (j=3 ∨ j=4 ∨ j=5)) ∧
    (visit i).Chain' (good i) := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def bitGraph (G : SimpleGraph V) [DecidableRel G.Adj] (f : Fin 11→V) (i : Nat) : Bool :=
  if h : i<18 then decide (G.Adj (f (varEnds ⟨i,h⟩).1) (f (varEnds ⟨i,h⟩).2)) else false

theorem bitGraph_var (f : Fin 11→V) (i : Fin 18) :
    bitGraph G f i.val=decide (G.Adj (f (varEnds i).1) (f (varEnds i).2)) := by
  unfold bitGraph
  rw [dif_pos i.isLt]

/-- The finite port certificate gives a certified walk on the actual support
of any injective eleven-position labeling with the required fixed edges. -/
theorem port_walk (f : Fin 11→V) (inj : Function.Injective f)
    (base : ∀ u v,(u,v)∈fixed → G.Adj (f u) (f v)) (M : PortModel (bitGraph G f)) :
    ∃ j : Fin 11, (j=3 ∨ j=4 ∨ j=5) ∧
      ∃ v,RouteOn G (univ.image f) (f j) v := by
  classical
  obtain ⟨r,req⟩ := has_template _ M
  obtain ⟨nd,cv,first,ch⟩ := visits_valid r
  obtain ⟨j,jh,jw⟩ := first
  have H (u v : Fin 11) (e : good r u v) : G.Adj (f u) (f v) := by
    rcases e with e|e|⟨k,km,e|e⟩
    · exact base _ _ e
    · exact (base _ _ e).symm
    · have h := req k.val km
      rw [bitGraph_var, e] at h
      exact of_decide_eq_true h
    have h := req k.val km
    rw [bitGraph_var,e] at h
    exact (of_decide_eq_true h : G.Adj (f v) (f u)).symm
  have cp : List.Chain' G.Adj ((visit r).map f) := (List.chain'_map f).mpr (ch.imp H)
  cases el : visit r with
  | nil => simp [el] at jh
  | cons i tail =>
    have eq : i=j := by simpa [el] using jh
    subst i
    have nn : (f j::tail.map f).Nodup := by
      rw [el] at nd
      exact nd.map inj
    have cp' : (f j::tail.map f).Chain' G.Adj := by simpa [el] using cp
    obtain ⟨v,p,sp⟩ := walk_of_chain (f j) (tail.map f) cp'
    refine ⟨j,jw,v,p,IsPath.mk' (sp.symm ▸ nn),?_⟩
    intro x
    rw [sp,←List.map_cons,←el,mem_image]
    constructor
    · intro m
      obtain ⟨u,mu,ux⟩ := List.mem_map.mp m
      exact ⟨u,mem_univ _,ux⟩
    rintro ⟨u,_,rfl⟩
    exact List.mem_map_of_mem (cv u)

#print axioms port_walk
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow
