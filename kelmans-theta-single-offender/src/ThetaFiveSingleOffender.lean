import PathCapBadTriangle
import ThetaFiveExterior

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFiveSingleOffender
open SquareCap (boundary SmallTrivial NontrivialSide FactorOn omitEdge)
open PentagonProfile (Port)
open PentagonCap (attach pathCap pathRoot path_cap_cubic SmallFourTrivial)
open ThetaFiveExterior (capPorts restricted target_from_restricted_factor)
noncomputable section

universe u

/-- Two specified independent edges hit every nontrivial low cut
in opposite shores. The conclusion uses the exact two deletions. -/
def HitsPairs {W : Type*} [Fintype W] (G : SimpleGraph W) (a b c d : W) : Prop :=
  ∀ f : W→Bool, (boundary G f).card≤3 →
    (∀ k,NontrivialSide f k) →
    ∃ k : Bool,3≤(boundary G f).card ∧ f a=k ∧ f b=k ∧ f c= !k ∧ f d= !k

/-- The published handle-plus-T2 conclusion, phrased in the
same support and omission language as the theta proof. -/
def HittingAvoidance : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (C : SimpleGraph W) [DecidableRel C.Adj],
    (∀ v,C.degree v=3) → 6∣Fintype.card W →
    ∀ a b c d : W,C.Adj a b → C.Adj c d →
      (∀ v,(v=a∨v=b) → (v=c∨v=d) → False) → HitsPairs C a b c d →
      FactorOn (omitEdge (omitEdge C a b) c d) univ

def iPort (side : Bool) : Port := if side then 1 else 2
def jPort (side : Bool) : Port := if side then 4 else 3

private theorem where_port {V : Type*} (q : Port↪V) (side : Bool) (k : Port)
    (h : k=0) : q k≠q (iPort side) ∧ q k≠q (jPort side) := by
  subst k
  have a : (0:Port)≠iPort side := by cases side <;> decide
  have b : (0:Port)≠jPort side := by cases side <;> decide
  exact ⟨fun e=>a (q.injective e),fun e=>b (q.injective e)⟩

theorem ends_disjoint {V : Type*} (q : Port↪V) (side : Bool) :
    ∀ v : V⊕Fin 3,(v=Sum.inl (q (iPort side)) ∨ v=Sum.inl (q (jPort side))) →
      (v=Sum.inr 1 ∨ v=Sum.inl (q 0)) → False := by
  intro v exterior virtual
  obtain ⟨x,y⟩ := where_port q side 0 rfl
  rcases exterior with rfl|rfl <;> rcases virtual with e|e
  · exact Sum.noConfusion e
  · exact x (Sum.inl_injective e).symm
  · exact Sum.noConfusion e
  · exact y (Sum.inl_injective e).symm

variable {V T : Type*} [Fintype V] [Fintype T] [DecidableEq V]

/-- If only one prescribed pair can be adjacent, the real pair
edge and the dead midpoint wire hit all bad cap cuts. -/
theorem same_pair_hits {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph T} {p : Port↪V} {r : Port→T} [DecidableRel (attach G P p r).Adj]
    (three : Fin 3↪T) (small : SmallTrivial (attach G P p r))
    (small4 : SmallFourTrivial (attach G P p r)) (cub : ∀ x,(attach G P p r).degree x=3)
    (side : Bool) (safeOther : ¬G.Adj (p (iPort (!side))) (p (jPort (!side)))) :
    HitsPairs (pathCap G p) (Sum.inl (p (iPort side))) (Sum.inl (p (jPort side)))
      (Sum.inr 1) (Sum.inl (p 0)) := by
  intro f bound bign
  obtain ⟨b,threeCut,cut⟩ := PathCapBadTriangle.actual_cut_has_triangle
    three small small4 cub f bound bign
  have opp (v : V⊕Fin 3) (no : f v≠b) : f v= !b := by
    cases t : f v <;> cases b <;> simp_all
  refine ⟨b,threeCut.ge,?_⟩
  cases side
  · rcases cut with ⟨_,shore⟩|⟨wrong,_⟩
    · refine ⟨(shore _).mpr (Or.inr (Or.inl rfl)),(shore _).mpr (Or.inr (Or.inr rfl)),?_,?_⟩
      · apply opp
        intro h
        rcases (shore _).mp h with e|e|e
        · exact (by decide : (1:Fin 3)≠0) (Sum.inr_injective e)
        · exact Sum.noConfusion e
        · exact Sum.noConfusion e
      · apply opp
        intro h
        rcases (shore _).mp h with e|e|e
        · exact Sum.noConfusion e
        · exact (by decide : (0:Port)≠2) (p.injective (Sum.inl_injective e))
        · exact (by decide : (0:Port)≠3) (p.injective (Sum.inl_injective e))
    · exact (safeOther wrong).elim
  · rcases cut with ⟨wrong,_⟩|⟨_,shore⟩
    · exact (safeOther wrong).elim
    · refine ⟨(shore _).mpr (Or.inr (Or.inl rfl)),(shore _).mpr (Or.inr (Or.inr rfl)),?_,?_⟩
      · apply opp
        intro h
        rcases (shore _).mp h with e|e|e
        · exact (by decide : (1:Fin 3)≠2) (Sum.inr_injective e)
        · exact Sum.noConfusion e
        · exact Sum.noConfusion e
      · apply opp
        intro h
        rcases (shore _).mp h with e|e|e
        · exact Sum.noConfusion e
        · exact (by decide : (0:Port)≠1) (p.injective (Sum.inl_injective e))
        · exact (by decide : (0:Port)≠4) (p.injective (Sum.inl_injective e))

private def perm : Equiv.Perm Port := (Equiv.swap 0 2).trans (Equiv.swap 2 3)

private theorem cap0 {V : Type*} (p : Port↪V) : capPorts p 0=p 3 :=
  congrArg p (by decide : perm 0=3)

private theorem degree_same {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

omit [Fintype V] [DecidableEq V] in
/-- The requested actual exterior edge in the original numbering. -/
def badLeft (p : Port↪V) (side : Bool) : V := capPorts p (iPort side)

omit [Fintype V] [DecidableEq V] in
def badRight (p : Port↪V) (side : Bool) : V := capPorts p (jPort side)

/-- In the exact 7-theta, if one of the prescribed opposite contact
pairs is the actual omitted edge and the other pair is nonadjacent,
the hitting-handle plus cyclic T2 promise proves the desired factor. -/
theorem singly_offending_exterior_omission
    (avoid : HittingAvoidance.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small : SmallTrivial (ThetaCase.ambient G p))
    (small4 : SmallFourTrivial (ThetaCase.ambient G p))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (side : Bool) (omitted : G.Adj (badLeft p side) (badRight p side))
    (safeOther : ¬G.Adj (badLeft p (!side)) (badRight p (!side))) :
    FactorOn (omitEdge (ThetaCase.ambient G p) (Sum.inl (badLeft p side)) (Sum.inl (badRight p side)))
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
  have hcut : SmallTrivial A := eq.symm ▸ small
  have hcut4 : SmallFourTrivial A := eq.symm ▸ small4
  let take3 : Fin 3↪Fin 7 := ⟨fun i=>⟨i.val,by have hi:=i.isLt; omega⟩,
    fun _ _ e=>Fin.ext (congrArg (fun z : Fin 7=>z.val) e)⟩
  have hit := same_pair_hits take3 hcut hcut4 cubA side safeOther
  have cCub : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=G) (P:=ThetaCase.theta) (p:=q) (r:=R) (fun v=>cubA (.inl v))
  have nC : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have nOrig : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have dvd : 6 ∣ Fintype.card (V⊕Fin 3) := by omega
  have middle : C.Adj (Sum.inr 1) (Sum.inl (q 0)) := ⟨0,rfl,by decide⟩
  have f := avoid (V⊕Fin 3) C cCub dvd
    (Sum.inl (q (iPort side))) (Sum.inl (q (jPort side))) (Sum.inr 1) (Sum.inl (q 0))
    omitted middle (ends_disjoint q side) hit
  have phase : FactorOn (restricted G p (badLeft p side) (badRight p side)) univ := by
    change FactorOn (omitEdge
      (omitEdge C (Sum.inl (q (iPort side))) (Sum.inl (q (jPort side))))
      (Sum.inr 1) (Sum.inl (p 3))) univ
    rw [←cap0 p]
    exact f
  exact target_from_restricted_factor p _ _ phase

#print axioms same_pair_hits
#print axioms singly_offending_exterior_omission
end
end KelmansCactus.AtomicBridge.ThetaFiveSingleOffender
