import SquareCapFactor
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Nodup

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulPatch
open SquareCap (FactorOn IsTile factor_map)

abbrev Site := Fin 9
abbrev Triple := Site × Site × Site

def core : List (Site × Site) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(1,6)]

def separateEdges (mode : Fin 3) : List (Site × Site) :=
  core ++ if mode=0 then [(2,7),(5,8)] else if mode=1 then [(2,7),(7,8)]
    else [(5,7),(7,8)]

def separateTable (mode : Fin 3) : List (Triple) :=
  if mode=0 then [(4,5,8),(3,2,7),(0,1,6)] else if mode=1 then [(3,4,5),(2,7,8),(0,1,6)]
  else [(5,7,8),(2,3,4),(0,1,6)]

def patch (E : List (Site × Site))
    (loop : ∀ u,(u,u)∉E) : SimpleGraph (Site) where
  Adj a b := (a,b)∈E ∨ (b,a)∈E
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := loop a (h.elim id id)

instance (E : List (Site × Site)) (loop : ∀ u,(u,u)∉E) :
    DecidableRel (patch E loop).Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈E ∨ (b,a)∈E))

def nodes (t : Triple) : List (Site) := [t.1,t.2.1,t.2.2]
def nodeSet (t : Triple) : Finset (Site) := (nodes t).toFinset

def check (E : List (Site × Site)) (P : List (Triple)) : Bool :=
  decide (P.flatMap nodes).Nodup &&
  decide ((P.flatMap nodes).toFinset = (univ : Finset (Site))) &&
  P.all (fun t => decide ((t.1,t.2.1)∈E ∨ (t.2.1,t.1)∈E) &&
    decide ((t.2.1,t.2.2)∈E ∨ (t.2.2,t.2.1)∈E))

private theorem triple_is_tile {G : SimpleGraph (Site)} {t : Triple}
    (nodup : (nodes t).Nodup) (one : G.Adj t.1 t.2.1) (two : G.Adj t.2.1 t.2.2) :
    IsTile G (nodeSet t) := by
  rcases t with ⟨a,b,c⟩
  refine ⟨?_,b,by simp [nodeSet,nodes],?_⟩
  · rw [nodeSet,List.toFinset_card_of_nodup nodup]
    rfl
  · intro x hx ne
    simp only [nodeSet,nodes,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact one.symm
    · exact (ne rfl).elim
    · exact two

private theorem checked_factor {E : List (Site × Site)}
    (loop : ∀ u,(u,u)∉E) (P : List (Triple)) (data : check E P = true) :
    FactorOn (patch E loop) univ := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at data
  rcases data with ⟨⟨nd,cov⟩,edges⟩
  obtain ⟨each,disj⟩ := List.nodup_flatMap.mp nd
  refine ⟨(P.map nodeSet).toFinset,?_,?_,?_⟩
  · intro t ht
    obtain ⟨a,ha,h⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    obtain ⟨e,f⟩ := edges a ha
    exact h ▸ triple_is_tile (G:=patch E loop) (each a ha) e f
  · intro t ht u hu ne
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    have diff : a≠b := fun eq=>ne (congrArg nodeSet eq)
    have sep := disj.forall (fun _ _ h=>List.Disjoint.symm h) ha hb diff
    apply disjoint_left.mpr
    intro z za zb
    exact List.disjoint_left.mp sep (List.mem_toFinset.mp za) (List.mem_toFinset.mp zb)
  · rw [←cov]
    ext z
    simp only [mem_biUnion,List.mem_toFinset,List.mem_map,List.mem_flatMap]
    constructor
    · intro h
      obtain ⟨A,⟨t,ht,rfl⟩,za⟩ := h
      exact ⟨t,ht,List.mem_toFinset.mp za⟩
    · rintro ⟨t,ht,tz⟩
      exact ⟨nodeSet t,⟨t,ht,rfl⟩,List.mem_toFinset.mpr tz⟩

private theorem separate_loop : ∀ m v,(v,v)∉separateEdges m := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem separate_checked (m : Fin 3) : check (separateEdges m) (separateTable m) = true := by
  fin_cases m <;> decide

theorem lift {T : Type*} [DecidableEq T] {H : SimpleGraph T}
    (m : Fin 3) (f : Site ↪ T)
    (em : ∀ a b,(a,b)∈separateEdges m → H.Adj (f a) (f b)) :
    FactorOn H (univ.map f) := by
  refine factor_map f (fun a b edge=>?_)
    (checked_factor (separate_loop m) _ (separate_checked m))
  exact edge.elim (em a b) (fun d=>(em b a d).symm)

#print axioms lift
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulPatch
