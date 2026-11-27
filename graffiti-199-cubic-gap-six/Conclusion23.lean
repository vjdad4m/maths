import Flanks23
import EmbedPlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private theorem finish23 (m : Fin 3) (tag : ℕ) (hm : tag ∈ residues23 m) :
    (∃ P, CoreRoute ((family23 m).pattern.edge tag) P) ∨
      Nonempty (FlankRules 8 ((family23 m).pattern.edge tag) (layout23.port m)) := by
  fin_cases m
  · have choose : tag = 253 := by simpa [residues23] using hm
    subst tag
    exact Or.inr ⟨flanks23_0⟩
  · have choose : tag = 254 := by simpa [residues23] using hm
    subst tag
    exact Or.inr ⟨flanks23_1⟩
  · have choose : tag = 255 ∨ tag = 507 ∨ tag = 511 := by simpa [residues23] using hm
    rcases choose with rfl|rfl|rfl
    · exact Or.inl ⟨[0,4,5,1,2,3,8,6,7],by decide⟩
    · exact Or.inl ⟨[0,4,1,2,3,8,6,5,7],by decide⟩
    · exact Or.inl ⟨[0,4,1,2,3,8,6,5,7],by decide⟩

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem traceable_of_layout23 (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 9 ↪ V)
    (p : PathOn G {v | v ≠ f (Fin.last 8)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 8)) (f (layout23.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout23.port i)) (f (layout23.port j)))
    (dz : G.degree (f (Fin.last 8)) = 3)
    (cubic : ∃ i, G.degree (f (layout23.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  exact traceable_of_layout layout23 m (family23 m) (family23_consistent m)
    (residues23 m) (cover23 m) (cover23_valid m) (finish23 m)
    (by decide) (by decide) budget p split ports ind dz dm

end Graffiti199Depleted.WiderOmission
