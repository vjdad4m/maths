import ThetaAdjacentEarCap
import ThetaCrossEarStitch
import EarCase
import FiveCapCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarCap
open SquareCap (boundary FactorOn SmallTrivial omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach SmallFourTrivial pathCap pathRoot path3 path_cap_cubic)
open ThetaFiveModes (Lane mid leaf)
open ThetaAdjacentEarRefill (Shape In Out)
open ThetaCrossEarRefill (firstSite nextSite)
open ThetaAdjacentEarCap (Omission released target place)
open ThetaAdjacentEarLeafModes (WeakLayout)
noncomputable section
universe u

variable {V : Type u}

def capIndex (i : Port) : Port :=
  if i=0 then 3 else if i=1 then 4 else if i=2 then 0 else if i=3 then 2 else 1

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
  if s then if i then 1 else 4 else if i then 2 else 0

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
@[simp] theorem ports1 (q : Port↪V) : ports q 1=q 4 := congrArg q (by decide : capIndex 1=4)
@[simp] theorem ports2 (q : Port↪V) : ports q 2=q 0 := congrArg q (by decide : capIndex 2=0)
@[simp] theorem ports3 (q : Port↪V) : ports q 3=q 2 := congrArg q (by decide : capIndex 3=2)
@[simp] theorem ports4 (q : Port↪V) : ports q 4=q 1 := congrArg q (by decide : capIndex 4=1)

def capEnds : Omission V → (Port↪V) → (V⊕Fin 3)×(V⊕Fin 3)
  | .old a b,_ => (.inl a,.inl b)
  | .first,q => (leaf true,.inl (q 1))
  | .fourth,q => (leaf true,.inl (q 4))

def capped (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :=
  omitEdge (pathCap B (ports q)) (capEnds e q).1 (capEnds e q).2

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
  · simpa [capEnds,Omission.originalEnds] using E.2
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

variable [Fintype V] [DecidableEq V]

private theorem same_degree {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

/-- All three omission kinds reduce to a cyclic-four F2 instance six
vertices smaller when the two alternate leaf pairs are nonedges
and both genuine cross edges are preserved. -/
theorem released_reduction
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (safe02 : ¬B.Adj (q 0) (q 2)) (safe41 : ¬B.Adj (q 4) (q 1))
    (e : Omission V)
    (real : (released B K q).Adj (e.originalEnds q).1 (e.originalEnds q).2)
    (sh : Shape (target B K q e)) (ear : K.Adj 7 8)
    (cross04 : (target B K q e).Adj (Out (q 0)) (Out (q 4)))
    (cross21 : (target B K q e).Adj (Out (q 2)) (Out (q 1))) :
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
      (by simpa using safe41) (by simpa using safe02)
  have ccub : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=B) (P:=K) (p:=ports q) (r:=place ∘ capPerm) (fun v=>cubA (.inl v))
  have big : 5≤Fintype.card V := by
    simpa using (Fintype.card_le_of_injective q q.injective)
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have conn := three_connected_of_small_trivial C ccub (by omega) csmall
  have rim : C.Adj (capEnds e q).1 (capEnds e q).2 := by
    cases e
    · exact real
    · exact ⟨4,ports4 q,by decide⟩
    · exact ⟨1,ports1 q,by decide⟩
  have f := smaller (V⊕Fin 3) C (by omega) ccub conn csmall (by omega)
    mid (capEnds e q).1 (capEnds e q).2 rim
  have keepEar : (target B K q e).Adj (In 7) (In 8) := by
    refine ⟨ear,?_⟩
    cases e <;> simp [Omission.originalEnds]
  have cross (i : Bool) : (target B K q e).Adj (Out (lanes q (false,i))) (Out (lanes q (true,i))) := by
    cases i
    · exact cross04
    · exact cross21
  exact ThetaCrossEarStitch.factor_of_two_leaves (cap_layout B q e) sh keepEar cross
    (old_adjs B K q e) (wire_adjs B K q e) f

#print axioms released_reduction
end
end KelmansCactus.AtomicBridge.ThetaCrossEarCap
