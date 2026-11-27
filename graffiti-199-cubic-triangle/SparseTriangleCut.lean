import TrianglePlacement
import ConnectivitySplice

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (SixTree six_tree_absurd)

structure TriangleCutChecks {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool)
    (a cut mate : Fin (n+1)) where
  profiles : List ℕ
  mask : ℕ
  single : SingleChecks e mate profiles
  coreCut : ∀ i, e a i = true → i = cut
  outsideCut : ∀ m ∈ profiles, touch m a = true → m = mask
  edgeCut : ∀ m ∈ profiles, m ≠ mask → ∃ T, SixTree (pairEdge e mask m true) T

def cut_checks {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool} {a cut mate : Fin (n+1)}
    (P : List ℕ) (mask : ℕ) (single : SingleChecks e mate P)
    (core : ∀ i, e a i = true → i = cut)
    (outside : ∀ i : Fin P.length, touch (P.get i) a = true → P.get i = mask)
    {c : ℕ → Fin 6 → Fin ((n+1)+2)}
    (cross : ∀ i : Fin P.length, P.get i ≠ mask → SixTree (pairEdge e mask (P.get i) true) (c (P.get i))) :
    TriangleCutChecks e a cut mate where
  profiles := P
  mask := mask
  single := single
  coreCut := core
  outsideCut := by
    intro m mem h
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp mem
    exact outside i h
  edgeCut := by
    intro m mem h
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp mem
    exact ⟨_,cross i h⟩

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- The vertices with the trapped attachment profile can leave their side
only through the indicated core vertex. -/
theorem contradiction_of_triangle_cut {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool}
    {a cut mate : Fin (n+1)} (checks : TriangleCutChecks e a cut mate)
    (budget : Catalogue.treeNumber G ≤ 5)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    {f : Fin (n+1) ↪ V}
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (exterior : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate))
    (acut : a ≠ cut) (az : a ≠ Fin.last n) (zcut : Fin.last n ≠ cut)
    (only : ∀ i, touch checks.mask i = true → i = a ∨ i = cut) : False := by
  let U : Set V := {v | v = f a ∨ (∀ i, v ≠ f i) ∧ ProfileAt G f v checks.mask}
  have zOut : f (Fin.last n) ∉ U := by
    rintro (eq|⟨off,_⟩)
    · exact az (f.injective eq.symm)
    · exact off _ rfl
  obtain ⟨x,xU,y,yOut,xCut,yCut,xy⟩ := cross_after_fewer_than_three below
    (D := {f cut}) (by simp) (U := U) (a := f a) (c := f (Fin.last n))
    (Or.inl rfl) zOut (by simpa using f.injective.ne acut)
    (by simpa using f.injective.ne zcut)
  by_cases anchor : ∃ i, y = f i
  · obtain ⟨i,rfl⟩ := anchor
    have notCut : i ≠ cut := fun eq => yCut (by simp [eq])
    change x = f a ∨ (∀ i, x ≠ f i) ∧ ProfileAt G f x checks.mask at xU
    rcases xU with rfl|⟨_,xm⟩
    · exact notCut (checks.coreCut i ((chart _ _).mp xy))
    · rcases only i ((xm i).mp xy) with rfl|eq
      · exact yOut (Or.inl rfl)
      · exact notCut eq
  · have offY (i : Fin (n+1)) : y ≠ f i := fun eq => anchor ⟨i,eq⟩
    obtain ⟨m,hm,ym⟩ := external_from_check budget checks.single chart offY
      (exterior y offY).1 (exterior y offY).2
    change x = f a ∨ (∀ i, x ≠ f i) ∧ ProfileAt G f x checks.mask at xU
    rcases xU with rfl|⟨offX,xm⟩
    · have same := checks.outsideCut m hm ((ym a).mp xy.symm)
      exact yOut (Or.inr ⟨offY,same ▸ ym⟩)
    · have diff : m ≠ checks.mask := fun eq => yOut (Or.inr ⟨offY,eq ▸ ym⟩)
      obtain ⟨T,t⟩ := checks.edgeCut m hm diff
      have ne := xy.ne
      let ext : Fin 2 ↪ V := ⟨![x,y],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
      have dis (i : Fin (n+1)) (j : Fin 2) : ext j ≠ f i := by
        fin_cases j
        · exact offX i
        · exact offY i
      let g := extend f ext dis
      have same : ∀ i j, G.Adj (g i) (g j) ↔ pairEdge e checks.mask m true i j = true := by
        apply extension_chart chart
        · intro j
          fin_cases j
          · exact xm
          · exact ym
        · intro i j
          fin_cases i <;> fin_cases j <;> simp [ext,pairLinks,xy,xy.symm]
      exact six_tree_absurd budget same t

#print axioms contradiction_of_triangle_cut

end Graffiti199Depleted.WiderOmission
