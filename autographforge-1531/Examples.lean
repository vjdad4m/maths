import Equality

namespace EdgeCover1531
open SimpleGraph Finset BullCover1125 TriangleMatching1078

theorem path_classes (n : ℕ) : Free (pathGraph n) claw ∧ TriangleFree (pathGraph n) := by
  constructor
  · rintro ⟨f⟩
    have edge (i : Fin 4) (hi : claw.Adj 0 i) := pathGraph_adj.mp (f.map_rel_iff.mpr hi)
    have one := edge 1 (by decide)
    have two := edge 2 (by decide)
    have three := edge 3 (by decide)
    have sep (i j : Fin 4) (ne : i ≠ j) : (f i).val ≠ (f j).val := fun eq => ne (f.injective (Fin.ext eq))
    have ab := sep 1 2 (by decide)
    have ac := sep 1 3 (by decide)
    have bc := sep 2 3 (by decide)
    omega
  · intro i j k ij jk ki
    have a := pathGraph_adj.mp ij
    have b := pathGraph_adj.mp jk
    have c := pathGraph_adj.mp ki
    omega

theorem connected_cover_exact {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (cl : Free G claw) (tri : TriangleFree G) :
    edgeCoverValue G = some ((Fintype.card V + 1)/2) := by
  classical
  have iso : IsolateFree G := by
    intro v
    obtain ⟨w,hw⟩ := card_pos.mp (GraffitiDegrees.deg_pos G hc hn v)
    exact ⟨w,(Graffiti271.mem_nbr G).mp hw⟩
  have lower := vertices_le_twice_cover iso
  have upper := connected_cover_bound hn hc cl tri
  have eq : edgeCoverNumber G = (Fintype.card V+1)/2 := by omega
  simp [edgeCoverValue,iso,eq]

/-- The three connected sharp examples all lie in the catalogue domain, and
their two exact numerical values are (2,1), (2,1), and (4,2). -/
theorem sharp_paths {n : ℕ} (orders : n=3 ∨ n=4 ∨ n=7) :
    2 ≤ n ∧ (pathGraph n).Connected ∧ Free (pathGraph n) claw ∧ TriangleFree (pathGraph n) ∧
    edgeCoverValue (pathGraph n) = some ((n+1)/2) ∧ lineDomination (pathGraph n) = (n+1)/4 := by
  have hn : 2 ≤ n := by omega
  have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  have hc : (pathGraph n).Connected := by cases n with
    | zero => omega
    | succ m => exact pathGraph_connected m
  obtain ⟨cl,tri⟩ := path_classes n
  have cover := connected_cover_exact (pathGraph n) hcard hc cl tri
  rw [Fintype.card_fin] at cover
  refine ⟨hn,hc,cl,tri,cover,?_⟩
  have shapes : Nonempty ((pathGraph n) ≃g pathGraph 3) ∨ Nonempty ((pathGraph n) ≃g pathGraph 4) ∨
      Nonempty ((pathGraph n) ≃g pathGraph 7) := by
    rcases orders with rfl|rfl|rfl
    · exact Or.inl ⟨RelIso.refl _⟩
    · exact Or.inr (Or.inl ⟨RelIso.refl _⟩)
    · exact Or.inr (Or.inr ⟨RelIso.refl _⟩)
  have tight := (equality_iff hcard hc cl tri).mpr shapes
  classical
  by_cases iso : IsolateFree (pathGraph n)
  · have raw : edgeCoverNumber (pathGraph n) = (n+1)/2 := by simpa [edgeCoverValue,iso] using cover
    omega
  · simp [edgeCoverValue,iso] at cover

#print axioms connected_cover_exact
#print axioms sharp_paths
end EdgeCover1531
