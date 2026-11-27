import ThetaAdjacentEarStitch
import EarCase
import FiveCapCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAdjacentEarCap
open SquareCap (boundary FactorOn SmallTrivial omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach SmallFourTrivial pathCap pathRoot path3 path_cap_cubic)
open ThetaFiveModes (Lane mid leaf)
open ThetaAdjacentEarRefill (Shape In Out firstSite nextSite)
open ThetaAdjacentEarLeafModes (WeakLayout)
noncomputable section
universe u

variable {V : Type u}

def place (i : Port) : Fin 9 :=
  if i=0 then 1 else if i=1 then 7 else if i=2 then 4 else if i=3 then 6 else 8

def capIndex (i : Port) : Port :=
  if i=0 then 3 else if i=1 then 2 else if i=2 then 0 else if i=3 then 4 else 1

def capPerm : Equiv.Perm Port :=
  Equiv.ofBijective capIndex
    ⟨by
        have test : ∀ a b : Port,capIndex a=capIndex b→a=b := by decide
        exact test,
     by
        have test : ∀ a : Port,∃ b : Port,capIndex b=a := by decide
        exact test⟩

def ports (q : Port↪V) : Port↪V := capPerm.toEmbedding.trans q

def laneIndex (s i : Bool) : Port :=
  if s then if i then 1 else 2 else if i then 4 else 0

def lanes (q : Port↪V) : Lane↪V :=
  ⟨fun k=>q (laneIndex k.1 k.2),fun a b h=>
    (by decide : ∀ a b : Lane,laneIndex a.1 a.2=laneIndex b.1 b.2 → a=b) _ _ (q.injective h)⟩

private theorem wire_site : ∀ s i : Bool,
  place (laneIndex s i) = if i then nextSite s else firstSite s := by decide

private theorem path_0 : ∀ i : Port,pathRoot i=0 ↔ i=2∨i=3 := by decide
private theorem path_2 : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide

private theorem inside_leaf : ∀ s : Bool,∀ j : Fin 3,
    path3.Adj (if s then 2 else 0) j → j=1 := by decide

@[simp] theorem ports0 (q : Port↪V) : ports q 0=q 3 := congrArg q (by decide : capIndex 0=3)
@[simp] theorem ports1 (q : Port↪V) : ports q 1=q 2 := congrArg q (by decide : capIndex 1=2)
@[simp] theorem ports2 (q : Port↪V) : ports q 2=q 0 := congrArg q (by decide : capIndex 2=0)
@[simp] theorem ports3 (q : Port↪V) : ports q 3=q 4 := congrArg q (by decide : capIndex 3=4)
@[simp] theorem ports4 (q : Port↪V) : ports q 4=q 1 := congrArg q (by decide : capIndex 4=1)

inductive Omission (V : Type*)
  | old (a b : V)
  | first
  | fourth

namespace Omission
def originalEnds : Omission V → (Port↪V) → (V⊕Fin 9)×(V⊕Fin 9)
  | .old a b,_ => (Out a,Out b)
  | .first,q => (In 7,Out (q 1))
  | .fourth,q => (In 8,Out (q 4))

def capEnds : Omission V → (Port↪V) → (V⊕Fin 3)×(V⊕Fin 3)
  | .old a b,_ => (.inl a,.inl b)
  | .first,q => (leaf true,.inl (q 1))
  | .fourth,q => (leaf false,.inl (q 4))
end Omission

def released (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V) :=
  attach B K q place

def target (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V) (e : Omission V) :=
  omitEdge (released B K q) (e.originalEnds q).1 (e.originalEnds q).2

def capped (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :=
  omitEdge (pathCap B (ports q)) (e.capEnds q).1 (e.capEnds q).2

theorem cap_layout (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :
    WeakLayout (capped B q e) (lanes q) := by
  constructor
  intro s x ed
  have E := ed.1
  cases x with
  | inr j =>
    have adj : path3.Adj (if s then 2 else 0) j := E
    exact Or.inl (congrArg Sum.inr (inside_leaf s j adj))
  | inl a =>
    obtain ⟨i,ai,ri⟩ : ∃ i,ports q i=a ∧ pathRoot i=(if s then 2 else 0) := E
    right
    cases s
    · rcases (path_0 i).mp ri with rfl|rfl
      · exact Or.inl (congrArg Sum.inl ((ports2 q).symm.trans ai).symm)
      · exact Or.inr (congrArg Sum.inl ((ports3 q).symm.trans ai).symm)
    · rcases (path_2 i).mp ri with rfl|rfl
      · exact Or.inl (congrArg Sum.inl ((ports1 q).symm.trans ai).symm)
      · exact Or.inr (congrArg Sum.inl ((ports4 q).symm.trans ai).symm)

theorem old_adjs (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (e : Omission V) :
    ∀ a b,(capped B q e).Adj (.inl a) (.inl b) → (target B K q e).Adj (Out a) (Out b) := by
  intro a b E
  refine ⟨E.1,?_⟩
  cases e
  · simpa [Omission.capEnds,Omission.originalEnds] using E.2
  · simp [Omission.originalEnds]
  · simp [Omission.originalEnds]

theorem wire_adjs (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (e : Omission V) (s i : Bool)
    (ed : (capped B q e).Adj (leaf s) (.inl (lanes q (s,i)))) :
    (target B K q e).Adj (In (if i then nextSite s else firstSite s))
      (Out (lanes q (s,i))) := by
  refine ⟨⟨laneIndex s i,rfl,wire_site s i⟩,?_⟩
  cases e
  · simp [Omission.originalEnds]
  · cases s <;> cases i
    all_goals simp [Omission.originalEnds,nextSite,firstSite,lanes,laneIndex]
    exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim
  · cases s <;> cases i
    all_goals simp [Omission.originalEnds,nextSite,firstSite,lanes,laneIndex]
    exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim

theorem kept_shape (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (e : Omission V)
    (ring : K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧ K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (a : K.Adj 2 7) (b : K.Adj 5 8) :
    Shape (target B K q e) := by
  have keep (u v : Fin 9) (edge : K.Adj u v) : (target B K q e).Adj (In u) (In v) := by
    refine ⟨edge,?_⟩
    cases e <;> simp [Omission.originalEnds]
  exact ⟨keep _ _ ring.1,keep _ _ ring.2.1,keep _ _ ring.2.2.1,
    keep _ _ ring.2.2.2.1,keep _ _ ring.2.2.2.2.1,keep _ _ ring.2.2.2.2.2,
    keep _ _ a,keep _ _ b⟩

variable [Fintype V] [DecidableEq V]

private theorem same_degree {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

/-- All three exact omission kinds on the released patch reduce
to smaller F2 if the new leaf pairs are nonadjacent. -/
theorem released_reduction
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (safe04 : ¬B.Adj (q 0) (q 4)) (safe21 : ¬B.Adj (q 2) (q 1))
    (e : Omission V)
    (real : (released B K q).Adj (e.originalEnds q).1 (e.originalEnds q).2)
    (sh : Shape (target B K q e)) :
    FactorOn (target B K q e) (univ.erase (Sum.inr 6)) := by
  let A := attach B K (ports q) (place ∘ capPerm)
  have same : A=released B K q := EarCase.reindex_attachment q place capPerm
  letI : DecidableRel A.Adj := fun a b=>by rw [same]; infer_instance
  have cubA (v) : A.degree v=3 := (same_degree same v).trans (cub _)
  have smallA : SmallTrivial A := same.symm ▸ small
  have small4A : SmallFourTrivial A := same.symm ▸ small4
  let C := pathCap B (ports q)
  classical
  let t3 : Fin 3↪Fin 9 :=
    ⟨fun i=>⟨i.val,by have h:=i.isLt; omega⟩,
        fun _ _ z=>Fin.ext (congrArg (fun w : Fin 9=>w.val) z)⟩
  have csmall : SmallTrivial C :=
    FiveCapCut.five_cap_of_nonadjacent_pairs t3 smallA small4A cubA
      (by simpa using safe21) (by simpa using safe04)
  have ccub : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=B) (P:=K) (p:=ports q) (r:=place ∘ capPerm) (fun v=>cubA (.inl v))
  have big : 5≤Fintype.card V := by
    simpa using (Fintype.card_le_of_injective q q.injective)
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have conn := three_connected_of_small_trivial C ccub (by omega) csmall
  have rim : C.Adj (e.capEnds q).1 (e.capEnds q).2 := by
    cases e
    · exact real
    · exact ⟨4,ports4 q,by decide⟩
    · exact ⟨3,ports3 q,by decide⟩
  have f := smaller (V⊕Fin 3) C (by omega) ccub conn csmall (by omega)
    mid (e.capEnds q).1 (e.capEnds q).2 rim
  exact ThetaAdjacentEarStitch.factor_of_two_leaves (cap_layout B q e) sh
    (old_adjs B K q e) (wire_adjs B K q e) f

#print axioms released_reduction
end
end KelmansCactus.AtomicBridge.ThetaAdjacentEarCap
