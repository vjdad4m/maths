import GraphSpliceCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange

namespace Graffiti199Depleted

open SimpleGraph

def labelRegion {ι V : Type*} (f : ι ↪ V) : Set V := {v | ∃ i, f i = v}

private def validFull {n : ℕ} (E : List (Fin n × Fin n))
    (p : List (Fin n)) (i j : Fin n) : Bool :=
  decide p.Nodup && (List.finRange n).all (fun k => p.contains k) &&
    decide (p.Chain' fun a b => E.contains (a,b) || E.contains (b,a)) &&
    p.head? == some i && p.getLast? == some j

private theorem lift_full_cert {n : ℕ} {V : Type*} {G : SimpleGraph V}
    (f : Fin n ↪ V) (E : List (Fin n × Fin n))
    (adj : ∀ a b, (a,b) ∈ E → G.Adj (f a) (f b))
    {p : List (Fin n)} {i j : Fin n} (check : validFull E p i j = true) :
    ∃ q : PathOn G (labelRegion f), q.first = f i ∧ q.last = f j := by
  simp only [validFull,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at check
  obtain ⟨⟨⟨⟨nd,all⟩,chain⟩,head⟩,last⟩ := check
  have ch := chain.imp (fun a b h => by
    simp only [Bool.or_eq_true,List.contains_iff_mem] at h
    exact h.elim (adj a b) (fun e => (adj b a e).symm))
  let q : PathOn G (labelRegion f) :=
    ⟨p.map f,by intro e; simp [List.map_eq_nil_iff.mp e] at head,
      (List.chain'_map _).mpr ch,nd.map f.injective,fun _ => by
        simp only [List.mem_map,labelRegion,Set.mem_setOf_eq]
        exact ⟨fun ⟨k,_,h⟩ => ⟨k,h⟩,fun ⟨k,h⟩ => ⟨k,
          List.contains_iff_mem.mp (List.all_eq_true.mp all k (List.mem_finRange _)),h⟩⟩⟩
  refine ⟨q,?_ ,?_⟩
  · apply Option.some.inj
    change some (q.vertices.head q.nonempty) = some (f i)
    rw [← List.head?_eq_head q.nonempty]
    change (p.map f).head? = _
    simp [head]
  · apply Option.some.inj
    change some (q.vertices.getLast q.nonempty) = some (f j)
    rw [← List.getLast?_eq_getLast q.nonempty]
    change (p.map f).getLast? = _
    simp [last]

/-- Labels 1 and 2 are the two triangle tips of the singleton.
They were reassigned from different halves of the paired block. -/
def splitTipsEdges : List (Fin 8 × Fin 8) :=
  [(0,1),(0,2),(0,3),(1,2),(4,5),(4,1),(4,6),(1,6),(5,2),(5,7),(2,7)]

def splitTipsHigh (i : Fin 8) : Bool := i != 0 && i != 4 && i != 5

def splitTipsPath (i : Fin 8) : List (Fin 8) :=
  match i with
  | 1 => [3,0,2,7,5,4,6,1]
  | 2 => [3,0,1,6,4,5,7,2]
  | 3 => [1,6,4,5,7,2,0,3]
  | 6 => [3,0,1,2,7,5,4,6]
  | 7 => [3,0,1,6,4,5,2,7]
  | _ => []

private theorem split_tip_cert : ∀ i : Fin 8, splitTipsHigh i = true →
    ∃ a : Fin 8, validFull splitTipsEdges (splitTipsPath i) a i = true := by decide

/-- Every high vertex is an available endpoint in the same-type split-half
subcase. Extra edges in the host graph are allowed. -/
theorem split_tips_path_ending_at_high {V : Type*} {G : SimpleGraph V}
    (f : Fin 8 ↪ V) (edges : ∀ a b, (a,b) ∈ splitTipsEdges → G.Adj (f a) (f b))
    {i : Fin 8} (high : splitTipsHigh i = true) :
    ∃ p : PathOn G (labelRegion f), p.last = f i := by
  obtain ⟨_,ok⟩ := split_tip_cert i high
  obtain ⟨p,_,last⟩ := lift_full_cert f splitTipsEdges edges ok
  exact ⟨p,last⟩

def singletonEdges : List (Fin 4 × Fin 4) := [(0,1),(0,2),(0,3),(1,2)]

def singletonHigh (i : Fin 4) : Bool := i != 0

def singletonLoose (i : Fin 4) : Bool := i == 3

def singletonPath (i j : Fin 4) : List (Fin 4) :=
  match (i,j) with
  | (1,3) => [1,2,0,3]
  | (2,3) => [2,1,0,3]
  | (3,1) => [3,0,2,1]
  | (3,2) => [3,0,1,2]
  | _ => []

private theorem singleton_cert : ∀ i j : Fin 4,
    singletonHigh i = true → singletonHigh j = true → singletonLoose i ≠ singletonLoose j →
    validFull singletonEdges (singletonPath i j) i j = true := by decide

theorem singleton_between_types {V : Type*} {G : SimpleGraph V}
    (f : Fin 4 ↪ V) (edges : ∀ a b, (a,b) ∈ singletonEdges → G.Adj (f a) (f b))
    {i j : Fin 4} (hi : singletonHigh i = true) (hj : singletonHigh j = true)
    (different : singletonLoose i ≠ singletonLoose j) :
    ∃ p : PathOn G (labelRegion f), p.first = f i ∧ p.last = f j :=
  lift_full_cert f singletonEdges edges (singleton_cert i j hi hj different)

private theorem other_type : ∀ i : Fin 4, singletonHigh i = true →
    ∃ j : Fin 4, singletonHigh j = true ∧ singletonLoose i ≠ singletonLoose j := by decide

theorem singleton_start_at_high {V : Type*} {G : SimpleGraph V}
    (f : Fin 4 ↪ V) (edges : ∀ a b, (a,b) ∈ singletonEdges → G.Adj (f a) (f b))
    {i : Fin 4} (hi : singletonHigh i = true) :
    ∃ p : PathOn G (labelRegion f), p.first = f i := by
  obtain ⟨j,hj,different⟩ := other_type i hi
  obtain ⟨p,first,_⟩ := singleton_between_types f edges hi hj different
  exact ⟨p,first⟩

#print axioms split_tips_path_ending_at_high
#print axioms singleton_between_types
#print axioms singleton_start_at_high

end Graffiti199Depleted
