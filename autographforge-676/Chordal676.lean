import Witness676
import ChordalBasis

namespace AutoGraphForge676
open SimpleGraph
set_option maxHeartbeats 0
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096

/-- Remove the pages, then remove the six hubs along their path. -/
def rank (x : V) : ℕ :=
  if Hub x then 6 - (2*x.1.val+x.2.val) else 7

private def earlier (x : V) : Finset V :=
  Finset.univ.filter (fun y => graph.Adj x y ∧ rank y ≤ rank x)

private theorem earlier_clique : ∀ x, graph.IsClique (earlier x : Set V) := by decide

theorem chordal : TriangleChain.Chordal graph := by
  apply TriangleChain.chordal_of_elimination _ rank
  intro x y z xy xz ne ry rz
  exact earlier_clique x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xy,ry⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xz,rz⟩) ne

private theorem earlier_bound : ∀ x, (earlier x).card ≤ 2 := by decide

theorem k4_free : graph.CliqueFree 4 := by
  intro S hS
  obtain ⟨hcl,hcard⟩ := graph.isNClique_iff.mp hS
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx,best⟩ := Finset.exists_max_image S rank hn
  have subset : S.erase x ⊆ earlier x := by
    intro y hy
    have ⟨ne,hy'⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcl hx hy' ne.symm,best y hy'⟩
  have le := (Finset.card_le_card subset).trans (earlier_bound x)
  rw [Finset.card_erase_of_mem hx,hcard] at le
  omega

theorem counterexample :
    2 ≤ Fintype.card V ∧ graph.Connected ∧ graph.CliqueFree 4 ∧
      TriangleChain.Chordal graph ∧ Graffiti324.residue graph < StarCone.forcing graph 2 :=
  ⟨by decide, connected, k4_free, chordal, by rw [residue_exact,forcing_exact]; decide⟩

theorem row676_false :
    ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj],
      2 ≤ Fintype.card U → G.CliqueFree 4 → TriangleChain.Chordal G →
      StarCone.forcing G 2 ≤ Graffiti324.residue G) := by
  intro h
  exact (not_le_of_gt counterexample.2.2.2.2) (h V graph counterexample.1 k4_free chordal)

#print axioms chordal
#print axioms k4_free
#print axioms counterexample
#print axioms row676_false
end AutoGraphForge676
