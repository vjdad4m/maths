import RemoteNumericHandle
import Mathlib.Data.List.Chain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteNumericHandleChecks
open HandleExtension (Edges)
open RemoteCutCertificate (Table)
open SquareCap (SmallTrivial)

def code {n : Nat} (e : Fin n×Fin n) : Nat := 48*e.2.val+e.1.val

def fromList {n : Nat} (E : List (Fin n×Fin n))
    (r : E.all (fun e=>decide (e.1<e.2))=true)
    (o : (E.map code).Chain' (fun a b : Nat=>a<b)) : Table n where
  edges := E
  sorted := fun a b m=>of_decide_eq_true (List.all_eq_true.mp r (a,b) m)
  nodup := List.Nodup.of_map code ((List.chain'_iff_pairwise.mp o).imp Nat.ne_of_lt)

def select {n : Nat} (T : Table n) (a b c d : Fin n)
    (ab : T.graph.Adj a b) (cd : T.graph.Adj c d)
    (separate : a≠c ∧ a≠d ∧ b≠c ∧ b≠d) : Edges T.graph where
  a s := if s then c else a
  b s := if s then d else b
  edge s := by cases s <;> assumption
  separated := by
    intro s t x hx hy
    cases s <;> cases t <;> try rfl
    all_goals
      simp at hx hy ⊢
      rcases hx with q|q <;> rcases hy with p|p <;> subst x
      all_goals first
      | exact separate.1 p
      | exact separate.2.1 p
      | exact separate.2.2.1 p
      | exact separate.2.2.2 p
      | exact separate.1 p.symm
      | exact separate.2.1 p.symm
      | exact separate.2.2.1 p.symm
      | exact separate.2.2.2 p.symm

def relabel {n : Nat} (T U : Table n) (f : Fin n ≃ Fin n)
    (there : ∀ e∈T.edges,U.graph.Adj (f e.1) (f e.2))
    (back : ∀ e∈U.edges,T.graph.Adj (f.symm e.1) (f.symm e.2)) :
    T.graph ≃g U.graph where
  toEquiv := f
  map_rel_iff' := by
    intro x y
    constructor
    · rintro (ed|ed)
      · simpa using back (f x,f y) ed
      · simpa using (back (f y,f x) ed).symm
    · rintro (ed|ed)
      · exact there (x,y) ed
      · exact (there (y,x) ed).symm

#print axioms select
#print axioms relabel
end KelmansCactus.AtomicBridge.RemoteNumericHandleChecks
