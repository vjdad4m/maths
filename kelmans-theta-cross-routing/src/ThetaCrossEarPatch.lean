import SquareCapFactor
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Nodup

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarPatch
open SquareCap (FactorOn IsTile factor_map)

abbrev Local := Fin 12
abbrev Case := Fin 3 × Fin 3

def core : List (Local×Local) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(2,6),(5,7),(6,7)]

/-- A live leaf has three modes: it used both port wires, only its
first wire, or only its second wire. A single-wire mode also uses
the genuine exterior edge between its port and the fresh vertex. -/
def modeEdges (p q a b : Local) (m : Fin 3) : List (Local×Local) :=
  if m=0 then [(p,a),(q,b)] else if m=1 then [(p,a),(a,b)] else [(q,a),(a,b)]

/-- In each mode only directly used contacts are represented by
these labels; a fresh exterior neighbor is not presumed to be a port. -/
def usedPort (a b : Local) (m : Fin 3) (i : Bool) : Option Local :=
  if m=0 then some (if i then b else a)
  else if (i=false ∧ m=1) ∨ (i=true ∧ m=2) then some a else none

def cross (k : Case) (i : Bool) : List (Local×Local) :=
  match usedPort 8 9 k.1 i,usedPort 10 11 k.2 i with
  | some a,some b => [(a,b)]
  | _,_ => []

def edges (k : Case) : List (Local×Local) :=
  core ++ modeEdges 1 4 8 9 k.1 ++ modeEdges 7 6 10 11 k.2 ++
    cross k false ++ cross k true

private theorem no_loop : ∀ k v,(v,v)∉edges k := by decide

def patch (k : Case) : SimpleGraph Local where
  Adj a b := (a,b)∈edges k ∨ (b,a)∈edges k
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := no_loop k a (h.elim id id)

instance (k : Case) : DecidableRel (patch k).Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈edges k ∨ (b,a)∈edges k))

abbrev Triple := Local × Local × Local

def nodes (t : Triple) : List Local := [t.1,t.2.1,t.2.2]
def nodeSet (t : Triple) : Finset Local := (nodes t).toFinset

private def table : Array (List Triple) :=
  #[[(0,1,2),(3,4,5),(6,11,9),(7,10,8)],
  [(0,1,2),(3,4,9),(5,7,6),(8,10,11)],
  [(0,1,8),(2,3,4),(5,7,6),(9,10,11)],
  [(0,1,2),(3,4,5),(7,6,11),(9,8,10)],
  [(0,5,4),(1,8,9),(3,2,6),(7,10,11)],
  [(0,5,7),(1,8,9),(2,3,4),(6,10,11)],
  [(0,1,2),(3,4,5),(6,7,10),(9,8,11)],
  [(1,0,5),(3,2,6),(4,8,9),(7,10,11)],
  [(0,5,7),(1,2,3),(4,8,9),(6,10,11)]]

private def partition (k : Case) : List Triple :=
  table[k.1.val*3+k.2.val]?.getD []

private def check (k : Case) : Bool :=
  let P := partition k
  decide (P.flatMap nodes).Nodup &&
  decide ((P.flatMap nodes).toFinset = (univ : Finset Local)) &&
  P.all (fun t => decide ((patch k).Adj t.1 t.2.1) &&
    decide ((patch k).Adj t.2.1 t.2.2))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem checked (k : Case) : check k = true := by
  obtain ⟨a,b⟩ := k
  fin_cases a <;> fin_cases b <;> decide

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


/-- The nine exact adjacent-ear modes refill all twelve vertices,
when both cross-contact edges and the absorbed edge are retained. -/
theorem all_nine_modes (k : Case) : FactorOn (patch k) univ := by
  let P := partition k
  have data := checked k
  change (decide (P.flatMap nodes).Nodup && decide ((P.flatMap nodes).toFinset=(univ : Finset Local)) &&
    P.all (fun t => decide ((patch k).Adj t.1 t.2.1) &&
      decide ((patch k).Adj t.2.1 t.2.2))) = true at data
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


theorem mapped_mode {T : Type*} [DecidableEq T] {H : SimpleGraph T}
    (k : Case) (e : Local↪T)
    (em : ∀ a b,(a,b)∈edges k → H.Adj (e a) (e b)) :
    FactorOn H (univ.map e) := by
  refine factor_map e (fun a b edge=>?_) (all_nine_modes k)
  exact edge.elim (em a b) (fun v=>(em b a v).symm)

#print axioms all_nine_modes
#print axioms mapped_mode
end KelmansCactus.AtomicBridge.ThetaCrossEarPatch
