import SquareCapFactor
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Nodup

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaErasedEarPatch
open SquareCap (FactorOn IsTile factor_map)

abbrev Site (n : ℕ) := Fin (8+n)
abbrev Triple (n : ℕ) := Site n × Site n × Site n

def core (n : ℕ) : List (Site n × Site n) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(2,6),(5,7)]

def middleSite {n : ℕ} (route : Fin 3) : Site n := if route=0 then 1 else 7
def firstSite {n : ℕ} (route : Fin 3) : Site n := if route=2 then 1 else 4
def lastSite {n : ℕ} (route : Fin 3) : Site n := if route=2 then 4 else 6

def sharedEdges (right : Bool) : List (Site 1 × Site 1) :=
  core 1 ++ [(if right then 4 else 1,8)]

def separateEdges (route : Fin 3) (mode : Fin 3) : List (Site 4 × Site 4) :=
  core 4 ++ [(middleSite route,8),(8,9)] ++
  if mode=0 then [(firstSite route,10),(lastSite route,11)]
  else if mode=1 then [(firstSite route,10),(10,11)]
  else [(lastSite route,10),(10,11)]

def sharedTable (right : Bool) : List (Triple 1) :=
  if right then [(3,4,8),(1,2,6),(0,5,7)] else [(4,5,7),(3,2,6),(0,1,8)]

def separateTable (route : Fin 3) (mode : Fin 3) : List (Triple 4) :=
  if route=0 then
    if mode=0 then [(3,4,10),(2,6,11),(1,8,9),(0,5,7)]
    else if mode=1 then [(4,10,11),(3,2,6),(1,8,9),(0,5,7)]
    else [(6,10,11),(2,3,4),(1,8,9),(0,5,7)]
  else if route=1 then
    if mode=0 then [(7,8,9),(3,4,10),(2,6,11),(1,0,5)]
    else if mode=1 then [(7,8,9),(4,10,11),(3,2,6),(1,0,5)]
    else [(7,8,9),(6,10,11),(2,3,4),(1,0,5)]
  else
    if mode=0 then [(7,8,9),(5,4,11),(3,2,6),(0,1,10)]
    else if mode=1 then [(7,8,9),(3,2,6),(1,10,11),(4,5,0)]
    else [(7,8,9),(4,10,11),(3,2,6),(1,0,5)]

def patch {n : ℕ} (E : List (Site n × Site n))
    (loop : ∀ u,(u,u)∉E) : SimpleGraph (Site n) where
  Adj a b := (a,b)∈E ∨ (b,a)∈E
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := loop a (h.elim id id)

instance {n : ℕ} (E : List (Site n × Site n)) (loop : ∀ u,(u,u)∉E) :
    DecidableRel (patch E loop).Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈E ∨ (b,a)∈E))

def nodes {n : ℕ} (t : Triple n) : List (Site n) := [t.1,t.2.1,t.2.2]
def nodeSet {n : ℕ} (t : Triple n) : Finset (Site n) := (nodes t).toFinset

def check {n : ℕ} (E : List (Site n × Site n)) (P : List (Triple n)) : Bool :=
  decide (P.flatMap nodes).Nodup &&
  decide ((P.flatMap nodes).toFinset = (univ : Finset (Site n))) &&
  P.all (fun t => decide ((t.1,t.2.1)∈E ∨ (t.2.1,t.1)∈E) &&
    decide ((t.2.1,t.2.2)∈E ∨ (t.2.2,t.2.1)∈E))

private theorem triple_is_tile {n : ℕ} {G : SimpleGraph (Site n)} {t : Triple n}
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

private theorem checked_factor {n : ℕ} {E : List (Site n × Site n)}
    (loop : ∀ u,(u,u)∉E) (P : List (Triple n)) (data : check E P = true) :
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

private theorem shared_loop : ∀ s v,(v,v)∉sharedEdges s := by decide
private theorem separate_loop : ∀ s m v,(v,v)∉separateEdges s m := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem shared_checked (s : Bool) :
    check (sharedEdges s) (sharedTable s) = true := by
  cases s <;> decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem separate_checked (s m : Fin 3) :
    check (separateEdges s m) (separateTable s m) = true := by
  fin_cases s <;> fin_cases m <;> decide

theorem lift_shared {T : Type*} [DecidableEq T] {H : SimpleGraph T}
    (s : Bool) (f : Site 1 ↪ T)
    (em : ∀ a b,(a,b)∈sharedEdges s → H.Adj (f a) (f b)) :
    FactorOn H (univ.map f) := by
  refine factor_map f (fun a b edge=>?_)
    (checked_factor (shared_loop s) _ (shared_checked s))
  exact edge.elim (em a b) (fun d=>(em b a d).symm)

theorem lift_separate {T : Type*} [DecidableEq T] {H : SimpleGraph T}
    (s m : Fin 3) (f : Site 4 ↪ T)
    (em : ∀ a b,(a,b)∈separateEdges s m → H.Adj (f a) (f b)) :
    FactorOn H (univ.map f) := by
  refine factor_map f (fun a b edge=>?_)
    (checked_factor (separate_loop s m) _ (separate_checked s m))
  exact edge.elim (em a b) (fun d=>(em b a d).symm)

#print axioms lift_shared
#print axioms lift_separate
end KelmansCactus.AtomicBridge.ThetaErasedEarPatch
