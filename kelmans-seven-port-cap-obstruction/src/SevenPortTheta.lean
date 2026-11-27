import SquareCapFactor
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Nodup

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.SevenPortTheta
open SquareCap (FactorOn IsTile)

abbrev Local := Fin 17
abbrev Layout := Fin 3
abbrev Case := Fin 4 ⊕ (Fin 3 × Fin 3)

def leftA (l : Layout) : Local := if l=2 then 11 else 8
def leftB (l : Layout) : Local := if l=0 then 11 else 12
def rightA : Local := 13
def rightB : Local := 14

def core : List (Local×Local) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(1,6),(6,7)]

def wireList : List (Local×Local) := [(2,8),(4,9),(5,11),(6,12),(7,13),(7,14)]

def additional (a b w : Local) (k : Fin 3) : List (Local×Local) :=
  if k=0 then [] else if k=1 then [(a,w)] else [(b,w)]

def edges (l : Layout) (k : Case) : List (Local×Local) :=
  core ++ wireList ++ match k with
  | .inl _ => []
  | .inr (s,t) => additional (leftA l) (leftB l) 15 s ++ additional rightA rightB 16 t

private theorem no_loop : ∀ l k v,(v,v) ∉ edges l k := by decide

def patch (l : Layout) (k : Case) : SimpleGraph Local where
  Adj a b := (a,b)∈edges l k ∨ (b,a)∈edges l k
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := no_loop l k a (h.elim id id)

instance (l : Layout) (k : Case) : DecidableRel (patch l k).Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈edges l k ∨ (b,a)∈edges l k))

instance (l : Layout) (k : Case) (t : Finset Local) : Decidable (IsTile (patch l k) t) := by
  unfold IsTile
  infer_instance

def used (a b w : Local) (k : Fin 3) : Finset Local :=
  if k=0 then {a,b} else if k=1 then {a,w} else {b,w}

def joint (l : Layout) (i : Fin 4) : Local :=
  if i=0 then leftA l else if i=1 then leftB l else if i=2 then rightA else rightB

def support (l : Layout) (k : Case) : Finset Local :=
  {0,1,2,3,4,5,6,7} ∪ match k with
  | .inl i => {joint l i}
  | .inr (s,t) => used (leftA l) (leftB l) 15 s ∪ used rightA rightB 16 t

private def idx : Case → Nat
  | .inl i => i.val
  | .inr (s,t) => 4+s.val*3+t.val


abbrev Triple := Local × Local × Local

def nodes (t : Triple) : List Local := [t.1,t.2.1,t.2.2]
def nodeSet (t : Triple) : Finset Local := (nodes t).toFinset

private def table (l : Layout) : Array (List Triple) :=
  if l=0 then #[
  [(0,5,4),(1,6,7),(3,2,8)],
  [(0,5,11),(1,6,7),(2,3,4)],
  [(0,1,2),(3,4,5),(6,7,13)],
  [(0,1,2),(3,4,5),(6,7,14)],
  [(0,1,6),(3,2,8),(4,5,11),(13,7,14)],
  [(0,1,6),(3,2,8),(4,5,11),(7,13,16)],
  [(0,1,6),(3,2,8),(4,5,11),(7,14,16)],
  [(0,1,6),(2,8,15),(3,4,5),(13,7,14)],
  [(0,1,6),(2,8,15),(3,4,5),(7,13,16)],
  [(0,1,6),(2,8,15),(3,4,5),(7,14,16)],
  [(0,1,6),(2,3,4),(5,11,15),(13,7,14)],
  [(0,1,6),(2,3,4),(5,11,15),(7,13,16)],
  [(0,1,6),(2,3,4),(5,11,15),(7,14,16)]
  ]
  else if l=1 then #[
  [(0,5,4),(1,6,7),(3,2,8)],
  [(0,1,2),(3,4,5),(7,6,12)],
  [(0,1,2),(3,4,5),(6,7,13)],
  [(0,1,2),(3,4,5),(6,7,14)],
  [(0,5,4),(1,6,12),(3,2,8),(13,7,14)],
  [(0,5,4),(1,6,12),(3,2,8),(7,13,16)],
  [(0,5,4),(1,6,12),(3,2,8),(7,14,16)],
  [(0,1,6),(2,8,15),(3,4,5),(13,7,14)],
  [(0,1,6),(2,8,15),(3,4,5),(7,13,16)],
  [(0,1,6),(2,8,15),(3,4,5),(7,14,16)],
  [(0,1,2),(3,4,5),(6,12,15),(13,7,14)],
  [(0,1,2),(3,4,5),(6,12,15),(7,13,16)],
  [(0,1,2),(3,4,5),(6,12,15),(7,14,16)]
  ]
  else #[
  [(0,5,11),(1,6,7),(2,3,4)],
  [(0,1,2),(3,4,5),(7,6,12)],
  [(0,1,2),(3,4,5),(6,7,13)],
  [(0,1,2),(3,4,5),(6,7,14)],
  [(0,5,11),(1,6,12),(2,3,4),(13,7,14)],
  [(0,5,11),(1,6,12),(2,3,4),(7,13,16)],
  [(0,5,11),(1,6,12),(2,3,4),(7,14,16)],
  [(0,1,6),(2,3,4),(5,11,15),(13,7,14)],
  [(0,1,6),(2,3,4),(5,11,15),(7,13,16)],
  [(0,1,6),(2,3,4),(5,11,15),(7,14,16)],
  [(0,1,2),(3,4,5),(6,12,15),(13,7,14)],
  [(0,1,2),(3,4,5),(6,12,15),(7,13,16)],
  [(0,1,2),(3,4,5),(6,12,15),(7,14,16)]
  ]

private def partition (l : Layout) (k : Case) : List Triple :=
  (table l)[idx k]?.getD []

private def check (l : Layout) (k : Case) : Bool :=
  let P := partition l k
  decide (P.flatMap nodes).Nodup &&
  decide ((P.flatMap nodes).toFinset = support l k) &&
  P.all (fun t => decide ((patch l k).Adj t.1 t.2.1) &&
    decide ((patch l k).Adj t.2.1 t.2.2))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem checked (l : Layout) (k : Case) : check l k = true := by
  fin_cases l
  all_goals
    rcases k with i|⟨s,t⟩
    · fin_cases i <;> decide
    · fin_cases s <;> fin_cases t <;> decide

private theorem triple_is_tile {G : SimpleGraph Local} {t : Triple}
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

/-- All four joint and nine separate edge-cap modes have exact tile
transfers on the surviving theta ring and absorbed exterior edge.
External neighbors 15 and 16 are abstract labels; a graph lift must
separately justify that all labels used in a selected mode are distinct. -/
theorem all_thirteen_modes (l : Layout) (k : Case) : FactorOn (patch l k) (support l k) := by
  let P := partition l k
  have data := checked l k
  change (decide (P.flatMap nodes).Nodup && decide ((P.flatMap nodes).toFinset=support l k) &&
    P.all (fun t => decide ((patch l k).Adj t.1 t.2.1) &&
      decide ((patch l k).Adj t.2.1 t.2.2))) = true at data
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at data
  rcases data with ⟨⟨nd,cov⟩,edges⟩
  obtain ⟨each,disj⟩ := List.nodup_flatMap.mp nd
  refine ⟨(P.map nodeSet).toFinset,?_,?_,?_⟩
  · intro t ht
    obtain ⟨a,ha,h⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    obtain ⟨e,f⟩ := edges a ha
    exact h ▸ triple_is_tile (each a ha) e f
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
    · rintro ⟨A,⟨t,ht,rfl⟩,za⟩
      exact ⟨t,ht,List.mem_toFinset.mp za⟩
    · rintro ⟨t,ht,tz⟩
      exact ⟨nodeSet t,⟨t,ht,rfl⟩,List.mem_toFinset.mpr tz⟩

#print axioms all_thirteen_modes
end KelmansCactus.AtomicBridge.SevenPortTheta
