import StableExchange180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Deleting a root-distance-dispensable edge in a minimum failed state
gives exact equality on the old independent set. The weighted tree
optimum stays fixed and the new independence choices are constrained. -/
theorem edge_tight (hc : G.Connected) (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A)
    (bad : let P := parity G r odd
           weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card)
    (smaller : ∀ a b, G.Adj a b → let J := G.deleteEdges {s(a,b)}
       J.Connected → localBound J r (parity J r odd))
    (a b : V) (e : G.Adj a b) (ab : ¬Arc G r a b) (ba : ¬Arc G r b a) :
    let J := G.deleteEdges {s(a,b)}
    let P := parity G r odd
    let U := eligible A P r
    bipartiteNum J=bipartiteNum G+1 ∧ weightedLeaves J U=weightedLeaves G U ∧
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ∧
    ∀ D, Indep J D → eligible D P r=U → D.card≤A.card := by
  dsimp only at *
  let J := G.deleteEdges {s(a,b)}
  let P := parity G r odd
  let U := eligible A P r
  obtain ⟨jc,dist⟩ := remove_edge_distances G hc r a b ab ba
  have eq : parity J r odd=P := by ext v; simp only [J,P,mem_parity,dist v]
  have valid := smaller a b e jc
  change localBound J r (parity J r odd) at valid
  rw [eq] at valid
  have sub : J≤G := G.deleteEdges_le _
  have low := valid A (fun x hx y hy ne e => ai x hx y hy ne (sub e))
  have mono := leaf_mono G sub U
  change weightedLeaves J U+bipartiteNum J≥1+A.card+P.card at low
  change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
  have up := (edge_witness G a b e (show bipartiteNum G<bipartiteNum J by omega)).1
  change bipartiteNum J=bipartiteNum G+1 at up
  change bipartiteNum J=bipartiteNum G+1 ∧ weightedLeaves J U=weightedLeaves G U ∧
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ∧ _
  refine ⟨up,by omega,by omega,?_⟩
  intro D di same
  have alt := valid D di
  change eligible D P r=U at same
  rw [same] at alt
  omega

/-- In a minimum failure the unique A-neighbor of an unchosen nonroot
vertex of P must be joined to it by a private predecessor edge. -/
theorem unique_neighbor_arc (hc : G.Connected) (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A)
    (bad : let P := parity G r odd
           weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card)
    (smaller : ∀ a b, G.Adj a b → let J := G.deleteEdges {s(a,b)}
       J.Connected → localBound J r (parity J r odd))
    (x y : V) (xr : x≠r) (xp : x∈parity G r odd) (xa : x∉A)
    (xy : G.Adj x y) (only : ∀ w∈A, G.Adj x w → w=y) :
    Arc G r x y ∨ Arc G r y x := by
  by_contra! no
  let J := G.deleteEdges {s(x,y)}
  have sub : J≤G := G.deleteEdges_le _
  have ind : Indep J A := fun u hu v hv ne e => ai u hu v hv ne (sub e)
  have maxA := (edge_tight G hc r odd A ai bad smaller x y xy no.1 no.2).2.2.2
  obtain ⟨w,aw,e⟩ := tight_domination J r (parity G r odd) A ind maxA x xp xr xa
  have eq := only w aw (sub e)
  subst w
  exact (show ¬J.Adj x y by simp [J]) e

#print axioms edge_tight
#print axioms unique_neighbor_arc
end Minimal180
