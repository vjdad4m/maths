import ThetaAdjacentEarCap
import ThetaDeadLeafStitch
import TwinObstruction
import EarCase
import FiveCapCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaDeadLeafCap
open SquareCap (boundary FactorOn SmallTrivial omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach SmallFourTrivial pathCap pathRoot path3 path_cap_cubic)
open ThetaFiveModes (Lane mid leaf)
open ThetaAdjacentEarRefill (Shape In Out)
open ThetaDeadLeafRefill (midSite)
open ThetaDeadLeafProfiles (MidLayout)
open ThetaAdjacentEarCap (Omission released target place)
open ThetaAdjacentEarLeafModes (WeakLayout)
noncomputable section
universe u

variable {V : Type u}

def midIndex (s : Bool) : Port := if s then 4 else 0
def deadIndex (s : Bool) : Port := if s then 0 else 4

def capIndex (s : Bool) (i : Port) : Port :=
  if i=0 then midIndex s else if i=1 then 3 else if i=2 then 2
  else if i=3 then 1 else deadIndex s

def capPerm (s : Bool) : Equiv.Perm Port :=
  Equiv.ofBijective (capIndex s)
    ⟨by
        have test : ∀ s,∀ a b : Port,capIndex s a=capIndex s b→a=b := by decide
        exact test s,
     by
        have test : ∀ s,∀ a : Port,∃ b : Port,capIndex s b=a := by decide
        exact test s⟩

def ports (s : Bool) (q : Port↪V) : Port↪V := (capPerm s).toEmbedding.trans q

def laneIndex (s j i : Bool) : Port :=
  if j then if i then deadIndex s else 3 else if i then 1 else 2

def lanes (s : Bool) (q : Port↪V) : Lane↪V :=
  ⟨fun k=>q (laneIndex s k.1 k.2),fun a b h=>
    (by decide : ∀ s,∀ a b : Lane,laneIndex s a.1 a.2=laneIndex s b.1 b.2 → a=b)
      s _ _ (q.injective h)⟩

private theorem wire_m : ∀ s : Bool, place (midIndex s)=midSite s := by decide
private theorem wire_l : ∀ s i : Bool, place (laneIndex s false i)=if i then 7 else 4 := by decide

private theorem path_0 : ∀ i : Port,pathRoot i=0 ↔ i=2∨i=3 := by decide
private theorem path_1 : ∀ i : Port,pathRoot i=1 ↔ i=0 := by decide
private theorem path_2 : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide

private theorem inside_leaf : ∀ s : Bool,∀ j : Fin 3,
    path3.Adj (if s then 2 else 0) j → j=1 := by decide

private theorem inside_mid : ∀ j : Fin 3,path3.Adj 1 j → j=0∨j=2 := by decide

@[simp] theorem ports0 (s : Bool) (q : Port↪V) : ports s q 0=q (midIndex s) := rfl
@[simp] theorem ports1 (s : Bool) (q : Port↪V) : ports s q 1=q 3 := rfl
@[simp] theorem ports2 (s : Bool) (q : Port↪V) : ports s q 2=q 2 := rfl
@[simp] theorem ports3 (s : Bool) (q : Port↪V) : ports s q 3=q 1 := rfl
@[simp] theorem ports4 (s : Bool) (q : Port↪V) : ports s q 4=q (deadIndex s) := rfl

def capEnds (s : Bool) : Omission V → (Port↪V) → (V⊕Fin 3)×(V⊕Fin 3)
  | .old a b,_ => (.inl a,.inl b)
  | .first,q => (leaf false,.inl (q 1))
  | .fourth,q => (if s then mid else leaf true,.inl (q 4))

def capped (s : Bool) (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :=
  omitEdge (pathCap B (ports s q)) (capEnds s e q).1 (capEnds s e q).2

theorem cap_layout (s : Bool) (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :
    WeakLayout (capped s B q e) (lanes s q) := by
  constructor
  intro j x ed
  have E := ed.1
  cases x with
  | inr k =>
    have a : path3.Adj (if j then 2 else 0) k := E
    exact Or.inl (congrArg Sum.inr (inside_leaf j k a))
  | inl a =>
    obtain ⟨i,ai,ri⟩ : ∃ i,ports s q i=a ∧ pathRoot i=(if j then 2 else 0) := E
    right
    cases j
    · rcases (path_0 i).mp ri with rfl|rfl
      · exact Or.inl (congrArg Sum.inl ((ports2 s q).symm.trans ai).symm)
      · exact Or.inr (congrArg Sum.inl ((ports3 s q).symm.trans ai).symm)
    · rcases (path_2 i).mp ri with rfl|rfl
      · exact Or.inl (congrArg Sum.inl ((ports1 s q).symm.trans ai).symm)
      · exact Or.inr (congrArg Sum.inl ((ports4 s q).symm.trans ai).symm)

theorem mid_layout (s : Bool) (B : SimpleGraph V) (q : Port↪V) (e : Omission V) :
    MidLayout (capped s B q e) (q (midIndex s)) := by
  intro x ed
  have E := ed.1
  cases x with
  | inr k =>
    have a : path3.Adj 1 k := E
    rcases inside_mid k a with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | inl a =>
    obtain ⟨i,ai,ri⟩ : ∃ i,ports s q i=a ∧ pathRoot i=1 := E
    have he := (path_1 i).mp ri
    subst i
    exact Or.inr (Or.inr (congrArg Sum.inl ((ports0 s q).symm.trans ai).symm))

theorem old_adjs (s : Bool) (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (e : Omission V) :
    ∀ a b,(capped s B q e).Adj (.inl a) (.inl b) → (target B K q e).Adj (Out a) (Out b) := by
  intro a b E
  refine ⟨E.1,?_⟩
  cases e
  · simpa [capEnds,Omission.originalEnds] using E.2
  · simp [Omission.originalEnds]
  · simp [Omission.originalEnds]

theorem wire_middle (s : Bool) (B : SimpleGraph V) (K : SimpleGraph (Fin 9))
    (q : Port↪V) (e : Omission V)
    (ed : (capped s B q e).Adj mid (.inl (q (midIndex s)))) :
    (target B K q e).Adj (In (midSite s)) (Out (q (midIndex s))) := by
  refine ⟨⟨midIndex s,rfl,wire_m s⟩,?_⟩
  cases e
  · simp [Omission.originalEnds]
  · cases s <;> simp [Omission.originalEnds,midSite]
  · cases s
    · simp [Omission.originalEnds,midSite]
    · exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim

theorem wire_leaf (s : Bool) (B : SimpleGraph V) (K : SimpleGraph (Fin 9))
    (q : Port↪V) (e : Omission V) (i : Bool)
    (ed : (capped s B q e).Adj (leaf false) (.inl (lanes s q (false,i)))) :
    (target B K q e).Adj (In (if i then 7 else 4))
      (Out (lanes s q (false,i))) := by
  refine ⟨⟨laneIndex s false i,rfl,wire_l s i⟩,?_⟩
  cases e
  · simp [Omission.originalEnds]
  · cases i
    · simp [Omission.originalEnds]
    · exact (ed.2 (Or.inl ⟨rfl,rfl⟩)).elim
  · cases i <;> simp [Omission.originalEnds]

variable [Fintype V] [DecidableEq V]

private theorem same_degree {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

/-- In the new routing, delete the dead cap leaf. The cap is cubic,
cyclic-four and three-connected, and is exactly six vertices smaller. -/
theorem released_reduction
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4) (s : Bool)
    (safe21 : ¬B.Adj (q 2) (q 1)) (safeDead : ¬B.Adj (q 3) (q (deadIndex s)))
    (e : Omission V)
    (real : (released B K q).Adj (e.originalEnds q).1 (e.originalEnds q).2)
    (sh : Shape (target B K q e)) (ear : K.Adj 7 8) :
    FactorOn (target B K q e) (univ.erase (Sum.inr 6)) := by
  let A := attach B K (ports s q) (place ∘ capPerm s)
  have same : A=released B K q := EarCase.reindex_attachment q place (capPerm s)
  letI : DecidableRel A.Adj := fun a b=>by rw [same]; infer_instance
  have cubA (v) : A.degree v=3 := (same_degree same v).trans (cub _)
  have smallA : SmallTrivial A := same.symm ▸ small
  have small4A : SmallFourTrivial A := same.symm ▸ small4
  let C := pathCap B (ports s q)
  classical
  let t3 : Fin 3↪Fin 9 :=
    ⟨fun i=>⟨i.val,by have h:=i.isLt; omega⟩,
        fun _ _ z=>Fin.ext (congrArg (fun w : Fin 9=>w.val) z)⟩
  have csmall : SmallTrivial C :=
    FiveCapCut.five_cap_of_nonadjacent_pairs t3 smallA small4A cubA
      (by simpa using safeDead) (by simpa using safe21)
  have ccub : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=B) (P:=K) (p:=ports s q) (r:=place ∘ capPerm s) (fun v=>cubA (.inl v))
  have big : 5≤Fintype.card V := by
    simpa using (Fintype.card_le_of_injective q q.injective)
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have conn := three_connected_of_small_trivial C ccub (by omega) csmall
  have rim : C.Adj (capEnds s e q).1 (capEnds s e q).2 := by
    cases e
    · exact real
    · exact ⟨3,ports3 s q,by decide⟩
    · cases s
      · exact ⟨4,ports4 false q,by decide⟩
      · exact ⟨0,ports0 true q,by decide⟩
  have f := smaller (V⊕Fin 3) C (by omega) ccub conn csmall (by omega)
    (leaf true) (capEnds s e q).1 (capEnds s e q).2 rim
  have keepEar : (target B K q e).Adj (In 7) (In 8) := by
    refine ⟨ear,?_⟩
    cases e <;> simp [Omission.originalEnds]
  have distinct (i : Bool) : q (midIndex s)≠lanes s q (false,i) := by
    intro h
    have diff : ∀ s i : Bool,midIndex s≠laneIndex s false i := by decide
    exact diff s i (q.injective h)
  exact ThetaDeadLeafStitch.factor_of_dead_leaf (cap_layout s B q e) (mid_layout s B q e)
    distinct sh keepEar s (old_adjs s B K q e) (wire_middle s B K q e)
    (wire_leaf s B K q e) f

/-- At least one choice of dead cap pair is safe: the surviving
known exterior edge prevents its two endpoints both joining the
original root contact, since the original host has no triangle. -/
theorem released_choice
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (real04 : B.Adj (q 0) (q 4)) (safe21 : ¬B.Adj (q 2) (q 1))
    (e : Omission V)
    (real : (released B K q).Adj (e.originalEnds q).1 (e.originalEnds q).2)
    (sh : Shape (target B K q e)) (ear : K.Adj 7 8) :
    FactorOn (target B K q e) (univ.erase (Sum.inr 6)) := by
  by_cases n : B.Adj (q 3) (q 4)
  · have no : ¬B.Adj (q 3) (q 0) := by
      intro yes
      have large : 5≤Fintype.card (V⊕Fin 9) := by simp
      exact TwinObstruction.no_triangle small large
        (a:=Out (q 0)) (b:=Out (q 4)) (c:=Out (q 3))
        real04 n.symm yes (le_of_eq (cub _)) (le_of_eq (cub _)) (le_of_eq (cub _))
    exact released_reduction smaller cub small small4 order true safe21 no e real sh ear
  · exact released_reduction smaller cub small small4 order false safe21 n e real sh ear

#print axioms released_reduction
#print axioms released_choice
end
end KelmansCactus.AtomicBridge.ThetaDeadLeafCap
