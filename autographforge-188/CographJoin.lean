import Proof137

namespace CographRadius
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Cograph (G : SimpleGraph V) := ¬ Graffiti137.InducedPath G 4
def Universal (G : SimpleGraph V) (x : V) := ∀ y, x ≠ y → G.Adj x y

omit [DecidableRel G.Adj] in
/-- The complement component of any specified vertex gives a join partition. -/
theorem join_at [Nontrivial V] (hc : G.Connected) (hp : Cograph G) (x : V) :
    ∃ (A : V → Prop) (y : V), A x ∧ ¬ A y ∧
      ∀ u v, A u → ¬ A v → G.Adj u v := by
  classical
  have disconnected : ¬ Gᶜ.Connected := fun h => hp (Graffiti137.four_of_connected_complement G hc h)
  have other : ∃ y, ¬ Gᶜ.Reachable x y := by
    by_contra! reach
    exact disconnected ⟨fun a b => (reach a).symm.trans (reach b)⟩
  obtain ⟨y,hy⟩ := other
  refine ⟨Gᶜ.Reachable x, y, .rfl, hy, ?_⟩
  intro u v hu hv
  by_contra missing
  have ne : u ≠ v := by rintro rfl; exact hv hu
  exact hv (hu.trans (((G.compl_adj u v).mpr ⟨ne,missing⟩).reachable))

end CographRadius
