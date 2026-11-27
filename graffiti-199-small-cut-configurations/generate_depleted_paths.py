"""Emit local spanning paths for the two disjoint singleton neighborhoods."""
from itertools import combinations

high = (1, 2, 3, 5, 6, 7)
rows = []
for kept in combinations(high, 4):
    for first in combinations(kept, 2):
        rows.append((*first, *(v for v in kept if v not in first)))


def unordered(u, v):
    return tuple(sorted((u, v)))


def path_to(edges, endpoint):
    def visit(path, remaining):
        if not remaining:
            return path[::-1]
        for v in sorted(remaining):
            if unordered(path[-1], v) in edges:
                answer = visit(path + [v], remaining - {v})
                if answer:
                    return answer
        return []
    return visit([endpoint], set(range(10)) - {endpoint})


print('''import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases

namespace Graffiti199K2.NearPacking.Depleted

abbrev I := Fin 8
abbrev K := Fin 10
abbrev Row := Fin 90

def inside (x : I) : K := Fin.castAdd 2 x

def high (x : I) : Bool := x != 0 && x != 4

def halves (r : Row) : I × I × I × I :=''')
print('  ( #[' + ', '.join(str(row) for row in rows) + '] : Array (I × I × I × I)).getD r.val (0,0,0,0)')
print('''
def same (a b x y : I) : Prop := (a = x ∧ b = y) ∨ (a = y ∧ b = x)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem covered :
    ∀ a b c d : I, high a = true → high b = true → high c = true → high d = true →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ r : Row, same a b (halves r).1 (halves r).2.1 ∧ same c d (halves r).2.2.1 (halves r).2.2.2 := by
  unfold same
  intro a b
  fin_cases a <;> fin_cases b <;> decide

def edges (r : Row) (looseEdge : Bool) : List (K × K) :=
  let a := (halves r).1
  let b := (halves r).2.1
  let c := (halves r).2.2.1
  let d := (halves r).2.2.2
  [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(4,7),(5,6),
   (8,9),(inside a,inside b),(inside c,inside d),
   (8,inside a),(8,inside b),(9,inside c),(9,inside d)] ++
    (if looseEdge then [(3,7)] else [])

def forbidden : List (K × K) := [(1,3),(2,3),(5,7),(6,7)]

def has (E : List (K × K)) (a b : K) : Bool :=
  E.contains (a,b) || E.contains (b,a)

def possible (r : Row) : Bool :=
  forbidden.all (fun e => !has (edges r false) e.1 e.2)

def routeData : Array (Array (List K) × Array (List K)) := #[''')
for a,b,c,d in rows:
    outputs = []
    for loose_edge in (False, True):
        e = {unordered(u,v) for u,v in [
            (0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(4,7),(5,6),
            (8,9),(a,b),(c,d),(8,a),(8,b),(9,c),(9,d)]}
        if e & {(1,3),(2,3),(5,7),(6,7)}:
            outputs.append('#[]')
            continue
        if loose_edge:
            e.add((3,7))
        paths = [path_to(e,x) if x in high else [] for x in range(8)]
        outputs.append('#[' + ', '.join(str(p) for p in paths) + ']')
    print('  (' + ', '.join(outputs) + '),')
print(''']

def paths (r : Row) (looseEdge : Bool) (x : I) : List K :=
  let data := routeData.getD r.val (#[], #[])
  (if looseEdge then data.2 else data.1).getD x.val []

def valid (E : List (K × K)) (x : I) (path : List K) : Bool :=
  decide (path.Nodup) && (List.finRange 10).all (fun i => path.contains i) &&
    decide (path.Chain' fun a b => has E a b = true) &&
    path.getLast? == some (inside x)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem paths_valid :
    ∀ (r : Row) (looseEdge : Bool) (x : I),
      possible r = true → paths r looseEdge x ≠ [] →
      valid (edges r looseEdge) x (paths r looseEdge x) = true := by
  intro r
  fin_cases r <;> decide

def blocked (r : Row) (looseEdge : Bool) : Finset I :=
  Finset.univ.filter (fun x => high x = true ∧ paths r looseEdge x = [])

def chosenHighs (r : Row) : List I :=
  [(halves r).1,(halves r).2.1,(halves r).2.2.1,(halves r).2.2.2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem choices :
    ∀ (r : Row) (b : Bool), possible r = true →
      (blocked r b).card ≤ 3 ∨
        (b = false ∧ 3 ∉ chosenHighs r ∧ paths r b 3 ≠ []) := by
  intro r
  fin_cases r <;> decide

#print axioms covered
#print axioms paths_valid
#print axioms choices

end Graffiti199K2.NearPacking.Depleted''')
