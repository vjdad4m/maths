import HallRainbow

namespace HallRainbow1121
open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def IsVertexCover (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → v ∈ S ∨ w ∈ S

noncomputable def vertexCoverNumber : ℕ :=
  sInf {n | ∃ S : Finset V, S.card = n ∧ IsVertexCover G S}

/-- If an uncolored vertex has degree at most the palette size, all of
its neighbors must be colored. -/
theorem colored_neighbors [DecidableRel G.Adj] {k : ℕ} {f : V → Fin (k+1)}
    (hf : Rainbow G f) {v w : V} (hv : f v = 0) (hd : G.degree v ≤ k)
    (e : G.Adj v w) : f w ≠ 0 := by
  classical
  let A := (G.neighborFinset v).filter (fun u => f u ≠ 0)
  have witness (i : Fin k) := hf v hv i.succ (Fin.succ_ne_zero i)
  choose pick edge color using witness
  have inj : Function.Injective pick := by
    intro i j eq
    exact Fin.succ_injective _ ((color i).symm.trans ((congrArg f eq).trans (color j)))
  have low : k ≤ A.card := by
    rw [← Fintype.card_fin k, ← card_univ]
    apply card_le_card_of_injOn pick ?_ inj.injOn
    intro i _
    exact mem_filter.mpr ⟨(G.mem_neighborFinset v _).mpr (edge i),
      (color i).symm ▸ Fin.succ_ne_zero i⟩
  have same : A = G.neighborFinset v :=
    eq_of_subset_of_card_le (filter_subset _ _) (hd.trans low)
  have member : w ∈ A := by rw [same]; exact (G.mem_neighborFinset v w).mpr e
  exact (mem_filter.mp member).2

/-- Only the uncolored vertices need a degree bound. -/
theorem colored_is_vertex_cover [DecidableRel G.Adj] {k : ℕ} {f : V → Fin (k+1)}
    (hf : Rainbow G f) (degree : ∀ v, f v = 0 → G.degree v ≤ k) :
    IsVertexCover G (univ.filter (fun v => f v ≠ 0)) := by
  intro v w e
  by_cases hv : f v = 0
  · exact Or.inr (mem_filter.mpr ⟨mem_univ _, colored_neighbors G hf hv (degree v hv) e⟩)
  · exact Or.inl (mem_filter.mpr ⟨mem_univ _, hv⟩)

theorem vertex_cover_le_rainbow [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (degree : ∀ v, G.degree v ≤ k) : vertexCoverNumber G ≤ rainbowNumber G k := by
  let sizes := {n | ∃ f : V → Fin (k+1), weight f = n ∧ Rainbow G f}
  let label : Fin (k+1) := ⟨1,Nat.succ_lt_succ hk⟩
  have nz : label ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
  have feasible : sizes.Nonempty :=
    ⟨_,fun _ => label,rfl,fun _ hv => False.elim (nz hv)⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem feasible
  apply Nat.sInf_le
  exact ⟨_,cost,colored_is_vertex_cover G hf (fun v _ => degree v)⟩

theorem rows645_671 [DecidableRel G.Adj] (subcubic : ∀ v, G.degree v ≤ 3) :
    vertexCoverNumber G ≤ rainbowNumber G 3 := vertex_cover_le_rainbow G (by decide) subcubic

#print axioms colored_neighbors
#print axioms colored_is_vertex_cover
#print axioms vertex_cover_le_rainbow
#print axioms rows645_671
end HallRainbow1121
