import FiveCapCut
import PathCapCutPointwise

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PathCapBadTriangle
open SquareCap (boundary SmallTrivial NontrivialSide min_three_of_small_trivial)
open PentagonProfile (Port mismatch portCount)
open PentagonCap (attach attach_boundary pathRoot pathCap SmallFourTrivial outside_law_of_attachment)
noncomputable section
variable {V T : Type*} [Fintype V] [Fintype T]

private theorem boundary_const {W : Type*} [Fintype W] (G : SimpleGraph W) (b : Bool) :
    (boundary G (fun _ => b)).card = 0 := by
  classical
  cases b <;> simp [boundary]

omit [Fintype V] [Fintype T] in
private theorem mismatch_const (p : Port ↪ V) (r : Port → T) (c : V → Bool) (b : Bool) :
    mismatch p c ((fun _ => !b) ∘ r) = portCount p c b := by
  unfold mismatch portCount
  congr 1
  ext i
  cases b <;> cases h : c (p i) <;> simp [h]



private theorem outside_shore_is_pair {G : SimpleGraph V} {P : SimpleGraph T}
    {p : Port↪V} {r : Port→T} (three : Fin 3↪T)
    (strong : SmallFourTrivial (attach G P p r))
    (c : V→Bool) (b : Bool) {i j : Port} (ij : i≠j)
    (two : (boundary G c).card=2)
    (fit : ∀ a,c (p a)=b ↔ a=i∨a=j) :
    ∀ x,c x=b ↔ x=p i∨x=p j := by
  classical
  have uu := (fit i).mpr (Or.inl rfl)
  have vv := (fit j).mpr (Or.inr rfl)
  have uv : p i ≠ p j := fun h=>ij (p.injective h)
  have pn : portCount p c b=2 := by
    have eq : (univ : Finset Port).filter (fun a => c (p a)=b) = {i,j} := by
      ext a
      simp [fit]
    unfold portCount
    rw [eq]
    simp [card_insert_of_not_mem,ij]
  have mask :
      (boundary (attach G P p r) (Sum.elim c (fun _ => !b))).card=4 := by
    rw [attach_boundary,boundary_const,mismatch_const, two,pn]
  obtain ⟨k,small⟩ := strong (Sum.elim c (fun _ => !b)) mask.le
  have same : k = b := by
    by_contra ne
    have nk : (!b) = k := by
      cases b <;> cases k <;> first | rfl | exact (ne rfl).elim
    have impossible := small (Sum.inr (three 0)) (Sum.inr (three 1)) (Sum.inr (three 2)) nk nk nk
    rcases impossible with i|i|i
    · exact (by decide : (0:Fin 3)≠1) (three.injective (Sum.inr_injective i))
    · exact (by decide : (0:Fin 3)≠2) (three.injective (Sum.inr_injective i))
    · exact (by decide : (1:Fin 3)≠2) (three.injective (Sum.inr_injective i))
  have only (x : V) (hx : c x=b) : x=p i ∨ x=p j := by
    subst k
    rcases small (Sum.inl x) (Sum.inl (p i)) (Sum.inl (p j)) hx uu vv with h|h|h
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
    · exact (uv (Sum.inl_injective h)).elim
  intro x
  exact ⟨only x,fun h=>h.elim (fun eq=>eq.symm ▸ uu) (fun eq=>eq.symm ▸ vv)⟩


private theorem leaf_ports (t : Fin 3) (leaf : t≠1) :
    (t=0 ∧ ∀ i,pathRoot i=t ↔ i=2 ∨ i=3) ∨
    (t=2 ∧ ∀ i,pathRoot i=t ↔ i=1 ∨ i=4) := by
  revert t
  decide

/-- Exact sides of EVERY nontrivial cut of size at most three in the
path cap. One shore is a cap leaf and its adjacent pair of contacts. -/
theorem actual_cut_has_triangle [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph T} {p : Port↪V} {r : Port→T}
    [DecidableRel (attach G P p r).Adj] (three : Fin 3↪T)
    (normal : SmallTrivial (attach G P p r))
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (f : V⊕Fin 3→Bool) (budget : (boundary (pathCap G p) f).card≤3)
    (big : ∀ b : Bool,NontrivialSide f b) :
    ∃ b : Bool,(boundary (pathCap G p) f).card=3 ∧
      ((G.Adj (p 2) (p 3) ∧ ∀ z,f z=b ↔
          z=Sum.inr 0 ∨ z=Sum.inl (p 2) ∨ z=Sum.inl (p 3)) ∨
       (G.Adj (p 1) (p 4) ∧ ∀ z,f z=b ↔
          z=Sum.inr 2 ∨ z=Sum.inl (p 1) ∨ z=Sum.inl (p 4))) := by
  classical
  have n : 3≤Fintype.card T := by
    simpa using (Fintype.card_le_of_injective three three.injective)
  have law := outside_law_of_attachment (by omega : 1<Fintype.card T)
    normal (min_three_of_small_trivial cub normal)
  obtain ⟨t,b,notMid,two,threeEdges,internal,portFit⟩ :=
    PathCapCutPointwise.actual_path_cap_cut_profile law f budget big
  refine ⟨b,threeEdges,?_⟩
  have detail {t : Fin 3} {i j : Port} (ij : i≠j)
      (inner : ∀ z : Fin 3, f (Sum.inr z)=b ↔ z=t)
      (fit : ∀ a,f (Sum.inl (p a))=b ↔ a=i∨a=j) :
      G.Adj (p i) (p j) ∧
        ∀ z,f z=b ↔ z=Sum.inr t ∨ z=Sum.inl (p i) ∨ z=Sum.inl (p j) := by
    have exterior := outside_shore_is_pair (P:=P) (r:=r) three strong
      (f ∘ Sum.inl) b ij two fit
    refine ⟨FiveCapCut.five_bad_pair_requires_edge (P:=P) (r:=r) three strong
      (fun z=>cub (Sum.inl z)) _ _ ij two fit,?_⟩
    intro z
    cases z with
    | inl a => simpa using exterior a
    | inr a => simpa using inner a
  rcases leaf_ports t notMid with ⟨rfl,l⟩|⟨rfl,l⟩
  · exact Or.inl (detail (by decide) internal (fun a=>(portFit a).trans (l a)))
  · exact Or.inr (detail (by decide) internal (fun a=>(portFit a).trans (l a)))

#print axioms actual_cut_has_triangle
end
end KelmansCactus.AtomicBridge.PathCapBadTriangle
