import ThetaErasedEarOriginal
import ThetaFiveExterior

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaExteriorReduction
open SquareCap (SmallTrivial ThreeConnected FactorOn omitEdge three_connected_of_small_trivial)
open PentagonCap (attach path3 pathRoot pathCap path_cap_cubic SmallFourTrivial)
open PentagonProfile (Port)
open ThetaFiveExterior (capPorts target_from_restricted_factor)
noncomputable section
universe u

/-- Exact two-edge avoidance only on SMALLER cubic cyclic-four instances
of order zero. The designated omissions may share an endpoint. -/
def CyclicAvoid2Below (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (C : SimpleGraph W) [DecidableRel C.Adj],
    Fintype.card W<n → (∀ v,C.degree v=3) → ThreeConnected C → SmallTrivial C →
    6 ∣ Fintype.card W → ∀ a b c d,C.Adj a b → C.Adj c d →
      FactorOn (omitEdge (omitEdge C a b) c d) univ

private def perm : Equiv.Perm Port := (Equiv.swap 0 2).trans (Equiv.swap 2 3)
private theorem cap0 {V : Type*} (p : Port↪V) : capPorts p 0=p 3 :=
  congrArg p (by decide : perm 0=3)
private theorem cap1 {V : Type*} (p : Port↪V) : capPorts p 1=p 1 :=
  congrArg p (by decide : perm 1=1)
private theorem cap2 {V : Type*} (p : Port↪V) : capPorts p 2=p 0 :=
  congrArg p (by decide : perm 2=0)
private theorem cap3 {V : Type*} (p : Port↪V) : capPorts p 3=p 2 :=
  congrArg p (by decide : perm 3=2)
private theorem cap4 {V : Type*} (p : Port↪V) : capPorts p 4=p 4 :=
  congrArg p (by decide : perm 4=4)

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
theorem absent_pairs
    (avoid : CyclicAvoid2Below.{u} (Fintype.card (V⊕Fin 7)))
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
  have middle : C.Adj (Sum.inr 1) (Sum.inl (p 3)) := ⟨0,cap0 p,by decide⟩
  have f := avoid (V⊕Fin 3) C (by omega) cCub conn cSmall dvd (Sum.inl x) (Sum.inl y)
    (Sum.inr 1) (Sum.inl (p 3)) ext middle
  exact target_from_restricted_factor p x y f

/-- Every real exterior omission of this exact theta uses smaller
instances only: F2 at order n-6 when an original opposite edge
exists, and two-edge avoidance at order n-4 otherwise. -/
theorem every_exterior_omission
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    (avoid : CyclicAvoid2Below.{u} (Fintype.card (V⊕Fin 7)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    {x y : V} (edge : G.Adj x y) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl x) (Sum.inl y))
      (univ.erase (Sum.inr 6)) := by
  by_cases a : G.Adj (p 1) (p 4)
  · exact ThetaErasedEarOriginal.any_exterior_with_one_ear smaller cub
      small small4 order (Or.inl a) edge
  · by_cases b : G.Adj (p 0) (p 2)
    · exact ThetaErasedEarOriginal.any_exterior_with_one_ear smaller cub
        small small4 order (Or.inr b) edge
    · exact absent_pairs avoid cub small small4 order b a edge

#print axioms absent_pairs
#print axioms every_exterior_omission
end
end KelmansCactus.AtomicBridge.ThetaExteriorReduction
