import Rows33
import EmbedPlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private theorem finish33 (m : Fin 3) (tag : ℕ) (hm : tag ∈ residues33 m) :
    (∃ P, CoreRoute ((family33 m).pattern.edge tag) P) ∨
      Nonempty (FlankRules 9 ((family33 m).pattern.edge tag) (layout33.port m)) := by
  fin_cases m
  · have choose : tag = 16043 ∨ tag = 16058 ∨ tag = 16059 := by simpa [residues33] using hm
    rcases choose with rfl|rfl|rfl
    · exact Or.inl ⟨[0,1,9,4,5,6,7,2,3,8],by decide⟩
    · exact Or.inl ⟨[0,1,9,4,5,6,7,2,3,8],by decide⟩
    · exact Or.inl ⟨[0,1,9,4,5,6,7,2,3,8],by decide⟩
  · have choose : tag = 11260 ∨ tag = 12284 := by simpa [residues33] using hm
    rcases choose with rfl|rfl
    · exact Or.inl ⟨[0,1,3,2,6,5,4,9,7,8],by decide⟩
    · exact Or.inl ⟨[0,1,2,6,5,3,4,9,7,8],by decide⟩
  · have choose : tag = 12798 ∨ tag = 29174 ∨ tag = 29182 := by simpa [residues33] using hm
    rcases choose with rfl|rfl|rfl
    · exact Or.inl ⟨[0,5,6,1,2,3,4,9,7,8],by decide⟩
    · exact Or.inl ⟨[0,5,1,2,3,4,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,5,1,2,3,4,9,7,6,8],by decide⟩

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem traceable_of_layout33 (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 10 ↪ V)
    (p : PathOn G {v | v ≠ f (Fin.last 9)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 9)) (f (layout33.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout33.port i)) (f (layout33.port j)))
    (dz : G.degree (f (Fin.last 9)) = 3)
    (cubic : ∃ i, G.degree (f (layout33.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  exact traceable_of_layout_classified layout33 m (family33 m) (family33_consistent m)
    (residues33 m) (classification33 m) (finish33 m)
    (by decide) (by decide) budget p split ports ind dz dm

end Graffiti199Depleted.WiderOmission
