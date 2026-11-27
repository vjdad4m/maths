import Flanks24
import EmbedPlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private theorem finish24 (m : Fin 3) (tag : ℕ) (hm : tag ∈ residues24 m) :
    (∃ P, CoreRoute ((family24 m).pattern.edge tag) P) ∨
      Nonempty (FlankRules 9 ((family24 m).pattern.edge tag) (layout24.port m)) := by
  fin_cases m
  · have choose : tag = 8153 := by simpa [residues24] using hm
    subst tag
    exact Or.inr ⟨flanks24_0⟩
  · have choose : tag = 7932 ∨ tag = 8188 := by simpa [residues24] using hm
    rcases choose with rfl|rfl
    · exact Or.inr ⟨flanks24_1⟩
    · exact Or.inl ⟨[0,1,2,5,6,4,3,9,7,8],by decide⟩
  · have choose : tag = 7935 ∨ tag = 16127 ∨ tag = 20215 ∨ tag = 20223 ∨ tag = 24311 ∨ tag = 24319 ∨ tag = 24563 ∨ tag = 28407 ∨ tag = 28415 ∨ tag = 32503 ∨ tag = 32511 := by simpa [residues24] using hm
    rcases choose with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Or.inl ⟨[0,4,5,6,1,2,3,9,7,8],by decide⟩
    · exact Or.inl ⟨[0,1,2,3,9,7,6,4,5,8],by decide⟩
    · exact Or.inl ⟨[0,4,5,1,2,3,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,4,5,1,2,3,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,4,5,1,2,3,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,4,5,1,2,3,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,1,2,5,4,3,9,7,6,8],by decide⟩
    · exact Or.inl ⟨[0,4,1,2,3,9,7,6,5,8],by decide⟩
    · exact Or.inl ⟨[0,4,1,2,3,9,7,6,5,8],by decide⟩
    · exact Or.inl ⟨[0,1,2,3,9,7,6,4,5,8],by decide⟩
    · exact Or.inl ⟨[0,1,2,3,9,7,6,4,5,8],by decide⟩

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem traceable_of_layout24 (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 10 ↪ V)
    (p : PathOn G {v | v ≠ f (Fin.last 9)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 9)) (f (layout24.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout24.port i)) (f (layout24.port j)))
    (dz : G.degree (f (Fin.last 9)) = 3)
    (cubic : ∃ i, G.degree (f (layout24.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  exact traceable_of_layout_classified layout24 m (family24 m) (family24_consistent m)
    (residues24 m) (classification24 m) (finish24 m)
    (by decide) (by decide) budget p split ports ind dz dm

end Graffiti199Depleted.WiderOmission
