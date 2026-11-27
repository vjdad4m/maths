import BicycleHoleLift133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive
set_option linter.unusedSectionVars false

def edgesAlong (p : List Nat) (x y : Nat) : Bool :=
  (p.zip (p.drop 1)).any fun ab => ((ab.1==x) && (ab.2==y)) || ((ab.1==y) && (ab.2==x))

def thetaPaths (a b c : Nat) : List (List Nat) :=
  [[0]++List.range' 2 (a-1)++[1],
   [0]++List.range' (2+(a-1)) (b-1)++[1],
   [0]++List.range' (2+(a-1)+(b-1)) (c-1)++[1]]

def thetaRelation (a b c : Nat) (i j : Nat) : Bool :=
  (thetaPaths a b c).any fun p => edgesAlong p i j

def dumbPaths (a b d : Nat) : List (List Nat) :=
  let end₂ := if d=0 then 0 else a+d-1
  [List.range a++[0], [end₂]++List.range' (a+d) (b-1)++[end₂],
    if d=0 then [] else [0]++List.range' a d]

def dumbRelation (a b d : Nat) (i j : Nat) : Bool :=
  (dumbPaths a b d).any fun p => edgesAlong p i j

def relabel (L : List Nat) {n : Nat} (hn : 1≤n) (i : Fin n) : Fin n :=
  ⟨(L.getD i.val 0)%n, Nat.mod_lt _ (by omega)⟩

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem hole_canonical_shape_has_nine {rows d2 : List Nat} {n : Nat}
    (hn : 1≤n) (h4 : FourCycleFree G) (H : Hole G 7) (f : Fin n → V)
    (f_inj : Function.Injective f) (outer : ∀ i, Outside H.c (f i))
    (site : Fin n → Fin 7) (attach : ∀ i j, G.Adj (f i) (H.c j) ↔ site i=j)
    (canonical : Nat → Nat → Bool)
    (edges : ∀ i j, G.Adj (f i) (f j) ↔ canonical i.val j.val=true)
    (L : List Nat) (labels : Function.Injective (relabel L hn))
    (shape : ∀ i j : Fin n, bit rows i.val j.val =
      canonical (relabel L hn i).val (relabel L hn j).val)
    (dist2 : ∀ i j : Fin n, bit d2 i.val j.val=true →
      ∃ k : Fin n, bit rows i.val k.val=true ∧ bit rows j.val k.val=true)
    {data : List (List Nat)} (ok : verify rows d2 data (n-1) 0 [0]=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  apply hole_singleton_extension_has_nine hn h4 H (f ∘ relabel L hn) (f_inj.comp labels)
    (fun i=>outer (relabel L hn i)) (site ∘ relabel L hn)
    (fun i j => attach (relabel L hn i) j) ?_ dist2 ok
  intro i j
  rw [shape i j]
  exact edges (relabel L hn i) (relabel L hn j)

#print axioms hole_canonical_shape_has_nine
end Graffiti133Bicycle
