import EarCase
import ThetaCase
import ThetaFiveAssemble

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFiveExterior
open SquareCap (SmallTrivial ThreeConnected FactorOn omitEdge three_connected_of_small_trivial)
open PentagonCap (attach path3 pathRoot pathCap path_cap_cubic SmallFourTrivial)
open PentagonProfile (Port)
open ThetaFiveModes (Lane Layout mid leaf)
open ThetaFiveRing (Shape site ring outer)
noncomputable section
universe u

/-- Canonical order-zero two-edge avoidance. The two designated
edges may share an endpoint. -/
def CyclicAvoid2 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (C : SimpleGraph W) [DecidableRel C.Adj],
    (∀ v,C.degree v=3) → ThreeConnected C → SmallTrivial C →
    6 ∣ Fintype.card W →
    ∀ a b c d,C.Adj a b → C.Adj c d →
      FactorOn (omitEdge (omitEdge C a b) c d) univ

private def perm : Equiv.Perm Port := (Equiv.swap 0 2).trans (Equiv.swap 2 3)

def capPorts {V : Type*} (p : Port↪V) : Port↪V := perm.toEmbedding.trans p

def liveIdx (s i : Bool) : Port :=
  if s then if i then 4 else 1 else if i then 2 else 0

def live {V : Type*} (p : Port↪V) : Lane↪V :=
  ⟨fun t => p (liveIdx t.1 t.2),fun a b h =>
    (by decide : ∀ a b : Lane,liveIdx a.1 a.2=liveIdx b.1 b.2 → a=b) _ _ (p.injective h)⟩

private theorem ring_wire : ∀ s i : Bool,
    ThetaCase.arm (liveIdx s i) = (site s i).castSucc := by decide

private theorem stem : pathRoot 0=1 := by decide

private theorem internal_path : ∀ a b : Fin 3,path3.Adj a b ↔
    (a=1 ∧ (b=0∨b=2)) ∨ (b=1 ∧ (a=0∨a=2)) := by decide

private theorem stem_only : ∀ i : Port,pathRoot i=1 ↔ i=0 := by decide
private theorem left_ends : ∀ i : Port,pathRoot i=0 ↔ i=2∨i=3 := by decide
private theorem right_ends : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide

private theorem route0 : perm 0=3 := by decide
private theorem route1 : perm 1=1 := by decide
private theorem route2 : perm 2=0 := by decide
private theorem route3 : perm 3=2 := by decide
private theorem route4 : perm 4=4 := by decide

private theorem cap0 {V : Type*} (p : Port↪V) : capPorts p 0=p 3 := congrArg p route0
private theorem cap1 {V : Type*} (p : Port↪V) : capPorts p 1=p 1 := congrArg p route1
private theorem cap2 {V : Type*} (p : Port↪V) : capPorts p 2=p 0 := congrArg p route2
private theorem cap3 {V : Type*} (p : Port↪V) : capPorts p 3=p 2 := congrArg p route3
private theorem cap4 {V : Type*} (p : Port↪V) : capPorts p 4=p 4 := congrArg p route4

def restricted {V : Type*} (G : SimpleGraph V) (p : Port↪V) (x y : V) :
    SimpleGraph (V⊕Fin 3) :=
  omitEdge (omitEdge (pathCap G (capPorts p)) (Sum.inl x) (Sum.inl y))
    (Sum.inr 1) (Sum.inl (p 3))

theorem restricted_layout {V : Type*} {G : SimpleGraph V} (p : Port↪V) (x y : V) :
    Layout (restricted G p x y) (live p) := by
  constructor
  · intro v
    cases v with
    | inl a =>
      constructor
      · intro h
        change (((∃ i : Port,capPorts p i=a ∧ pathRoot i=1) ∧ _) ∧ _) at h
        obtain ⟨⟨⟨i,ea,ri⟩,_⟩,bad⟩ := h
        have e : p 3=a := (cap0 p).symm.trans ((stem_only i).mp ri ▸ ea)
        exact (bad (Or.inl ⟨rfl,congrArg Sum.inl e.symm⟩)).elim
      · simp [leaf]
    | inr b =>
      change ((path3.Adj 1 b ∧ _) ∧ _) ↔ _
      simp [internal_path,mid,leaf]
  · intro s v
    cases s <;> cases v
    all_goals
      first
      | change (((∃ i : Port,capPorts p i=_ ∧ pathRoot i=_) ∧ _) ∧ _) ↔ _
        simp [left_ends,right_ends,cap2,cap3,cap1,cap4,leaf,mid,live,liveIdx]
      | change ((path3.Adj _ _ ∧ _) ∧ _) ↔ _
        simp [internal_path,leaf,mid,live]
    · constructor
      · rintro ⟨i,e,h|h⟩
        · rw [h,cap2] at e
          exact Or.inl e.symm
        · rw [h,cap3] at e
          exact Or.inr e.symm
      · rintro (e|e)
        · exact ⟨2,(cap2 p).trans e.symm,Or.inl rfl⟩
        · exact ⟨3,(cap3 p).trans e.symm,Or.inr rfl⟩
    · constructor
      · rintro ⟨i,e,h|h⟩
        · rw [h,cap1] at e
          exact Or.inl e.symm
        · rw [h,cap4] at e
          exact Or.inr e.symm
      · rintro (e|e)
        · exact ⟨1,(cap1 p).trans e.symm,Or.inl rfl⟩
        · exact ⟨4,(cap4 p).trans e.symm,Or.inr rfl⟩

private theorem ringAdj : ∀ a b : Fin 6, a+1=b ∨ b+1=a →
    ThetaCase.theta.Adj a.castSucc b.castSucc := by decide

theorem target_shape {V : Type*} {G : SimpleGraph V} (p : Port↪V) (x y : V) :
    Shape (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y)) (live p) := by
  constructor
  · intro a b h
    exact ⟨ringAdj a b h,by simp [ring]⟩
  · intro s i
    refine ⟨?_,by simp [ring,outer]⟩
    exact ⟨liveIdx s i,rfl,ring_wire s i⟩

/-- A factor of this exact restricted cap always lifts, even if it
was obtained from an ambient handle instead of direct edge avoidance. -/
theorem target_from_restricted_factor {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (p : Port↪V) (x y : V)
    (f : FactorOn (restricted G p x y) univ) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  apply ThetaFiveAssemble.factor_of_blocked_cap (restricted_layout (G:=G) p x y)
    (target_shape (G:=G) p x y) _ f
  intro a b edge
  exact ⟨edge.1.1,by simpa using edge.1.2⟩

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem degree_same {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

/-- Exact full exterior edge omission at the theta with the two
opposite port pairs nonadjacent. It needs only cyclic two-edge
avoidance at order zero, not a smaller F2 promise. -/
theorem exterior_of_cyclic_two_avoid
    (avoid : CyclicAvoid2.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (safe02 : ¬G.Adj (p 0) (p 2)) (safe14 : ¬G.Adj (p 1) (p 4))
    {x y : V} (ext : G.Adj x y) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  let q := capPorts p
  let R := ThetaCase.arm ∘ perm
  let A := attach G ThetaCase.theta q R
  have eq : A=ThetaCase.ambient G p := EarCase.reindex_attachment p ThetaCase.arm perm
  letI : DecidableRel A.Adj := fun a b => by
    rw [eq]
    infer_instance
  have cubA (v) : A.degree v=3 := (degree_same eq v).trans (cub v)
  let C := pathCap G q
  classical
  have safeL : ¬G.Adj (q 1) (q 4) := by simpa [q,cap1,cap4] using safe14
  have safeR : ¬G.Adj (q 2) (q 3) := by simpa [q,cap2,cap3] using safe02
  let take3 : Fin 3↪Fin 7 := ⟨fun i=>⟨i.val,by have hi:=i.isLt; omega⟩,
    fun _ _ e=>Fin.ext (congrArg (fun z : Fin 7=>z.val) e)⟩
  have hcut : SmallTrivial A := eq.symm ▸ small
  have hcut4 : SmallFourTrivial A := eq.symm ▸ small4
  have cSmall : SmallTrivial C :=
    FiveCapCut.five_cap_of_nonadjacent_pairs take3 hcut hcut4 cubA safeL safeR
  have cCub : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=G) (P:=ThetaCase.theta) (p:=q) (r:=R) (fun v=>cubA (.inl v))
  have n : 5≤Fintype.card V := by
    simpa using (Fintype.card_le_of_injective p p.injective)
  have nC : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have nOrig : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have conn := three_connected_of_small_trivial C cCub (by omega) cSmall
  have dvd : 6 ∣ Fintype.card (V⊕Fin 3) := by omega
  have middle : C.Adj (Sum.inr 1) (Sum.inl (p 3)) := ⟨0,cap0 p,stem⟩
  have f := avoid (V⊕Fin 3) C cCub conn cSmall dvd (Sum.inl x) (Sum.inl y)
    (Sum.inr 1) (Sum.inl (p 3)) ext middle
  exact target_from_restricted_factor p x y f

#print axioms restricted_layout
#print axioms target_from_restricted_factor
#print axioms exterior_of_cyclic_two_avoid
end
end KelmansCactus.AtomicBridge.ThetaFiveExterior
