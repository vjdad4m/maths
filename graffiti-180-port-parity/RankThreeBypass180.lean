import OneBypass180
import ParitySeam180
import LayerCut180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordinary Graffiti.pc 180 on the rank-three, second-degree-at-least-two
branch if a single even chord reconnects the graph of crossing edges
after deletion of an odd vertex and one endpoint has two crossing
neighbors. All distances are original distances from a maximizing root. -/
theorem conjecture180_reconnecting_chord (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (rk : Fintype.card V≤bipartiteNum G+3) (deg : 2≤secondDegree G)
    (r : V) (mx : evenCount G r=maxEven G) (v a b : V) :
    let P := parity G r false
    let H := alternating G P
    v∉P → a∈P → b∈P → G.Adj a b → 2≤H.degree a →
    Con (H⊔SimpleGraph.edge a b) (univ.erase v) →
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  intro P H odd ap bp ab two survive
  rw [←mx]
  by_contra! bad
  have h := reconnecting_chord G hc hn r (by omega) bad v a b odd ap bp ab survive
  change H.degree a≤1 at h
  omega

/-- The restrictions refer to the same odd vertex of the same failed
ordinary root. Its private even child is measured in the original graph.
Every horizontal edge which alone reconnects its deleted vertical graph
has two endpoints of vertical degree exactly one. -/
theorem borderline_odd_vertex (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (v : V) (odd : v∉parity G r false) :
    let P := parity G r false
    let H := alternating G P
    ¬Con H (univ.erase v) ∧ (∃ w,Arc G r v w) ∧
    ∀ a∈P,∀ b∈P,G.Adj a b → Con (H⊔SimpleGraph.edge a b) (univ.erase v) →
      H.degree a=1 ∧ H.degree b=1 := by
  classical
  intro P H
  have cut := odd_is_cut G hc hn r rk bad v odd
  have vr : v≠r := fun e => odd (e ▸ (by simp [dist_self]))
  refine ⟨cut,cut_has_private_child G hc r v vr cut,?_⟩
  intro a ap b bp ab con
  have edge : SimpleGraph.edge b a=SimpleGraph.edge a b := by ext i j; rw [edge_adj,edge_adj]; tauto
  have aa := reconnecting_chord G hc hn r rk bad v a b odd ap bp ab con
  have bb := reconnecting_chord G hc hn r rk bad v b a odd bp ap ab.symm (by rwa [edge])
  have pos (u : V) : 0<H.degree u := (H.degree_pos_iff_exists_adj u).mpr
    (exists_adj H (alternating_parity G hc r false).1 hn u)
  change H.degree a≤1 at aa
  change H.degree b≤1 at bb
  exact ⟨by have := pos a; omega,by have := pos b; omega⟩

#print axioms conjecture180_reconnecting_chord
#print axioms borderline_odd_vertex
end Minimal180.PortParity
