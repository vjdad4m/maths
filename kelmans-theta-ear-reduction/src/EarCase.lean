import EarTransfer
import EarDecode
import FiveCapCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarCase
open SquareCap (FactorOn SmallTrivial ThreeConnected omitEdge three_connected_of_small_trivial)
open PentagonCap (attach pathCap pathRoot path_cap_cubic SmallFourTrivial)
open PentagonProfile (Port)
open EarDecode (restrictedCap decode_restricted_cap)
open EarTransfer (EarTarget close_after_absorbing_edge)
open FiveCapCut (five_cap_of_nonadjacent_pairs)
noncomputable section

universe u

/-- The exact smaller-order induction hypothesis, not an assumption of
ordinary cyclic-four factors alone. -/
def CyclicF2Below (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    Fintype.card W<n → (∀ x,G.degree x=3) → ThreeConnected G → SmallTrivial G →
    Fintype.card W%6=4 → ∀ root a b : W,G.Adj a b →
      FactorOn (omitEdge G a b) (univ.erase root)

variable {V : Type u} [Fintype V] [DecidableEq V]

private def sampleThree : Fin 3 ↪ Fin 9 :=
  ⟨fun i=>⟨i.val,by have b := i.isLt; omega⟩,
    fun _ _ h=>Fin.ext (congrArg (fun z : Fin 9=>z.val) h)⟩

/-- Smaller cyclic-four F2 suffices once the two safe pairs have
been routed on the released 9-vertex gadget. Its cap is strictly
smaller (six fewer vertices) and has the same order residue. -/
theorem ear_factor_of_smaller_f2_with_safe_pairs
    (smaller : CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph (Fin 9)} {r : Port→Fin 9} {p : Port↪V}
    [DecidableRel (attach G P p r).Adj]
    (cub : ∀ x,(attach G P p r).degree x=3)
    (small : SmallTrivial (attach G P p r)) (small4 : SmallFourTrivial (attach G P p r))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (safe14 : ¬G.Adj (p 1) (p 4)) (safe23 : ¬G.Adj (p 2) (p 3))
    (H : SimpleGraph (V⊕Fin 9)) (target : EarTarget G H)
    (wire1 : H.Adj (Sum.inl (p 1)) (Sum.inr 7))
    (wire4 : H.Adj (Sum.inl (p 4)) (Sum.inr 8)) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  classical
  let C := pathCap G p
  have sc := five_cap_of_nonadjacent_pairs sampleThree small small4 cub safe14 safe23
  have d : ∀ x,C.degree x=3 := path_cap_cubic (G:=G) (P:=P) (p:=p) (r:=r)
    (fun x => cub (Sum.inl x))
  have n3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have n9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have lower : Fintype.card (V⊕Fin 3)<Fintype.card (V⊕Fin 9) := by omega
  have bigV : 5≤Fintype.card V := by
    have e := Fintype.card_le_of_injective p p.injective
    simpa using e
  have conn := three_connected_of_small_trivial C d (by omega) sc
  have rem : Fintype.card (V⊕Fin 3)%6=4 := by omega
  have cut : C.Adj (Sum.inr 1) (Sum.inl (p 0)) := ⟨0,rfl,rfl⟩
  have fc := smaller (V⊕Fin 3) C lower d conn sc rem (Sum.inr 0) (Sum.inr 1) (Sum.inl (p 0)) cut
  obtain ⟨x,hx,yes⟩ := decode_restricted_cap (G:=G) (p:=p) fc
  exact close_after_absorbing_edge target x yes (hx.elim
    (fun h=>Or.inl (h.symm ▸ wire1)) (fun h=>Or.inr (h.symm ▸ wire4)))

omit [Fintype V] [DecidableEq V] in
/-- Reindexing the wires changes no edge of the original attachment. -/
theorem reindex_attachment {W : Type*} {G : SimpleGraph V} {P : SimpleGraph W}
    (p : Port ↪ V) (r : Port → W) (σ : Equiv.Perm Port) :
    attach G P (σ.toEmbedding.trans p) (r ∘ σ) = attach G P p r := by
  have wires (v : V) (w : W) :
      (∃ i,p (σ i)=v ∧ r (σ i)=w) ↔ ∃ i,p i=v ∧ r i=w := by
    constructor
    · rintro ⟨i,h,k⟩
      exact ⟨σ i,h,k⟩
    · rintro ⟨i,h,k⟩
      exact ⟨σ.symm i,by simpa using h,by simpa using k⟩
  ext x y
  cases x <;> cases y
  · rfl
  · exact wires _ _
  · exact wires _ _
  · rfl

private theorem same_degree {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

omit [Fintype V] [DecidableEq V] in
private theorem choose_pair {G : SimpleGraph V} (p : Port↪V)
    (triangle : ∀ a b c : V,G.Adj a b → G.Adj b c → G.Adj c a → False) :
    ∃ σ : Equiv.Perm Port, σ 1=1 ∧ σ 4=4 ∧ ¬G.Adj (p (σ 2)) (p (σ 3)) := by
  classical
  by_cases bc : G.Adj (p 2) (p 3)
  · by_cases ac : G.Adj (p 0) (p 3)
    · refine ⟨Equiv.swap 0 3,by decide,by decide,?_⟩
      change ¬G.Adj (p 2) (p 0)
      exact fun ba=>triangle (p 0) (p 3) (p 2) ac bc.symm ba
    · refine ⟨Equiv.swap 0 2,by decide,by decide,?_⟩
      change ¬G.Adj (p 0) (p 3)
      exact ac
  · exact ⟨Equiv.refl _,rfl,rfl,bc⟩

/-- Complete smaller-order bridge for the released 9-vertex layout.
The retained contact pair is automatically safe under no 4-cycles;
a safe pair for the discarded leaf can always be chosen among
the remaining three contacts in a triangle-free exterior. -/
theorem ear_factor_of_smaller_f2
    (smaller : CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph (Fin 9)} {r : Port→Fin 9} {p : Port↪V}
    [DecidableRel (attach G P p r).Adj]
    (cub : ∀ x,(attach G P p r).degree x=3)
    (small : SmallTrivial (attach G P p r)) (small4 : SmallFourTrivial (attach G P p r))
    (triangle : ∀ a b c : V,G.Adj a b → G.Adj b c → G.Adj c a → False)
    (clean : ∀ a b c d : V⊕Fin 9,
      (attach G P p r).Adj a b → (attach G P p r).Adj b c →
      (attach G P p r).Adj c d → (attach G P p r).Adj d a → a=c∨b=d)
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (r1 : r 1=7) (r4 : r 4=8) (earEdge : P.Adj 7 8)
    (H : SimpleGraph (V⊕Fin 9)) (target : EarTarget G H)
    (wire1 : H.Adj (Sum.inl (p 1)) (Sum.inr 7))
    (wire4 : H.Adj (Sum.inl (p 4)) (Sum.inr 8)) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  have safe14 : ¬G.Adj (p 1) (p 4) := by
    intro adj
    have problem := clean (Sum.inr 7) (Sum.inr 8) (Sum.inl (p 4)) (Sum.inl (p 1))
      earEdge ⟨4,rfl,r4⟩ adj.symm ⟨1,rfl,r1⟩
    simp at problem
  obtain ⟨σ,s1,s4,safe23⟩ := choose_pair p triangle
  let q := σ.toEmbedding.trans p
  let f := r ∘ σ
  have same : attach G P q f = attach G P p r := reindex_attachment p r σ
  letI : DecidableRel (attach G P q f).Adj := fun x y => by
    rw [same]
    infer_instance
  have newCub (v : V⊕Fin 9) : (attach G P q f).degree v=3 := (same_degree same v).trans (cub v)
  have e1 : q 1=p 1 := congrArg p s1
  have e4 : q 4=p 4 := congrArg p s4
  apply ear_factor_of_smaller_f2_with_safe_pairs smaller (p:=q) (r:=f) newCub
    (same.symm ▸ small) (same.symm ▸ small4) order
    (by simpa [e1,e4] using safe14) safe23 H target
  · simpa [e1] using wire1
  · simpa [e4] using wire4

#print axioms ear_factor_of_smaller_f2_with_safe_pairs
#print axioms ear_factor_of_smaller_f2

end
end KelmansCactus.AtomicBridge.EarCase
