import HandleCuts
import RemoteFourCutTransport
import RemoteCutCertificate
import Mathlib.Logic.Equiv.Fin.Basic

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteNumericHandle
open HandleExtension (Edges)
open RemoteCutCertificate (Table)
open SquareCap (SmallTrivial)

def numbered (n : Nat) : Fin n ⊕ Bool ≃ Fin (n+2) :=
  (Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans finSumFinEquiv

def old {n : Nat} (x : Fin n) : Fin (n+2) := numbered n (.inl x)
def fresh (n : Nat) (b : Bool) : Fin (n+2) := numbered n (.inr b)

@[simp] theorem old_eq {n : Nat} (x y : Fin n) : old x=old y ↔ x=y :=
  ⟨fun h=>Sum.inl.inj ((numbered n).injective h),congrArg old⟩
@[simp] theorem fresh_eq (n : Nat) (s t : Bool) : fresh n s=fresh n t ↔ s=t :=
  ⟨fun h=>Sum.inr.inj ((numbered n).injective h),congrArg (fresh n)⟩
@[simp] theorem old_ne_fresh {n : Nat} (x : Fin n) (s : Bool) : old x ≠ fresh n s := by
  intro h
  exact Sum.noConfusion ((numbered n).injective h)
@[simp] theorem fresh_ne_old {n : Nat} (x : Fin n) (s : Bool) : fresh n s ≠ old x :=
  (old_ne_fresh x s).symm

variable {n : Nat} (T : Table n) (E : Edges T.graph)

private instance (s : Bool) (x y : Fin n) : Decidable (E.PairFor s x y) := by
  unfold Edges.PairFor
  infer_instance
private instance (x y : Fin n) : Decidable (E.Removed x y) := by
  unfold Edges.Removed
  infer_instance

private def kept : List (Fin n×Fin n) :=
  T.edges.filter (fun e=>decide (¬E.Removed e.1 e.2))
private def liftEdge (e : Fin n×Fin n) : Fin (n+2)×Fin (n+2) := (old e.1, old e.2)

def tailEdges : List (Fin (n+2)×Fin (n+2)) :=
  [(old (E.a false),fresh n false),(old (E.b false),fresh n false),
   (old (E.a true),fresh n true),(old (E.b true),fresh n true),(fresh n false,fresh n true)]

def expected : List (Fin (n+2)×Fin (n+2)) :=
  (kept T E).map liftEdge ++ tailEdges T E

private theorem old_old (x y : Fin n) :
    (old x,old y) ∈ expected T E ↔ (x,y)∈T.edges ∧ ¬E.Removed x y := by
  rw [expected,List.mem_append]
  constructor
  · rintro (h|h)
    · obtain ⟨⟨u,v⟩,p,e⟩:=List.mem_map.mp h
      have uv : u=x ∧ v=y := by simpa [liftEdge] using e
      rcases uv with ⟨rfl,rfl⟩
      simpa [kept] using p
    · simp [tailEdges] at h
  · intro h
    exact Or.inl (List.mem_map.mpr ⟨(x,y),by simpa [kept] using h,rfl⟩)

private theorem old_fresh (x : Fin n) (s : Bool) :
    (old x,fresh n s)∈expected T E ↔ E.Ends s x := by
  rw [expected,List.mem_append]
  constructor
  · rintro (h|h)
    · obtain ⟨⟨u,v⟩,_,e⟩ := List.mem_map.mp h
      exact (old_ne_fresh v s (congrArg Prod.snd e)).elim
    · cases s <;> simpa [tailEdges,Edges.Ends] using h
  · intro h
    right
    cases s <;> simpa [tailEdges,Edges.Ends] using h

private theorem not_fresh_old (s : Bool) (x : Fin n) :
    (fresh n s,old x)∉expected T E := by
  rw [expected,List.mem_append]
  rintro (h|h)
  · obtain ⟨⟨u,v⟩,_,e⟩:=List.mem_map.mp h
    exact (old_ne_fresh u s (congrArg Prod.fst e)).elim
  · simp [tailEdges] at h

private theorem fresh_fresh (s t : Bool) :
    (fresh n s,fresh n t) ∈ expected T E ↔ s=false ∧ t=true := by
  rw [expected,List.mem_append]
  constructor
  · rintro (h|h)
    · obtain ⟨⟨u,v⟩,_,e⟩ := List.mem_map.mp h
      exact (old_ne_fresh u s (congrArg Prod.fst e)).elim
    · simpa [tailEdges,Eq.comm] using h
  · rintro ⟨rfl,rfl⟩
    exact Or.inr (by simp [tailEdges])

/-- Compact construction certificate: a numeric graph is one handle
extension of the previous graph when its edge list is exactly updated.
No enumeration of the larger vertex cuts is needed. -/
def updated_iso (F : Table (n+2)) (eq : F.edges = expected T E) :
    E.host ≃g F.graph where
  toEquiv := numbered n
  map_rel_iff' := by
    rintro (u|s) (v|t)
    · change ((old u,old v)∈F.edges ∨ (old v,old u)∈F.edges) ↔
        (T.graph.Adj u v ∧ ¬E.Removed u v)
      have swap : E.Removed v u ↔ E.Removed u v :=
        ⟨fun ⟨i,h⟩=>⟨i,E.pair_symm h⟩,fun ⟨i,h⟩=>⟨i,E.pair_symm h⟩⟩
      rw [eq,old_old,old_old,swap]
      change (_ ∨ _) ↔ (((u,v)∈T.edges ∨ (v,u)∈T.edges) ∧ _)
      tauto
    · change ((old u,fresh n t)∈F.edges ∨ (fresh n t,old u)∈F.edges) ↔ E.Ends t u
      rw [eq,old_fresh]
      exact or_iff_left (not_fresh_old T E t u)
    · change ((fresh n s,old v)∈F.edges ∨ (old v,fresh n s)∈F.edges) ↔ E.Ends s v
      rw [eq,old_fresh]
      exact or_iff_right (not_fresh_old T E s v)
    · change ((fresh n s,fresh n t)∈F.edges ∨ (fresh n t,fresh n s)∈F.edges) ↔ s≠t
      rw [eq,fresh_fresh,fresh_fresh]
      cases s <;> cases t <;> simp

private theorem cube_map (F : Table (n+2)) (eq : F.edges = expected T E)
    (cub : ∀ x,T.graph.degree x=3) : ∀ x,F.graph.degree x=3 := by
  intro x
  let i := updated_iso T E F eq
  exact (RemoteFourCutTransport.transfer_degree i.symm x).trans (E.cubic cub (i.symm x))

theorem step (F : Table (n+2)) (eq : F.edges = expected T E)
    (hyp : (∀ x,T.graph.degree x=3) ∧ SmallTrivial T.graph) :
    (∀ x,F.graph.degree x=3) ∧ SmallTrivial F.graph :=
  ⟨cube_map T E F eq hyp.1,
    RemoteFourCutTransport.transfer_small (updated_iso T E F eq).symm
      (E.preserves_small_trivial hyp.1 hyp.2)⟩

#print axioms step
end KelmansCactus.AtomicBridge.RemoteNumericHandle
