import MissingPath
import TerminalOreAdapter199
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X M : Set V} {z r a b : V}

/-- Apply the published two-terminal Ore closure inside the reserved set
M. Every degree and the order in the threshold are computed after restriction to M. -/
theorem SingletonCut.traceable_of_terminal_closure (F : SingletonCut G X z r a b)
    [Fintype M] [DecidableRel (G.induce M).Adj] (J : SimpleGraph M) [DecidableRel J.Adj]
    (sub : M ⊆ X) (on : ∀ v ∈ X \ M, G.Adj r v) (hc : (G.induce (X \ M)).Connected)
    (super : G.induce M ≤ J)
    (degree : ∀ i j : M, J.Adj i j → ¬ (G.induce M).Adj i j →
      Fintype.card M + 1 ≤ (G.induce M).degree i + (G.induce M).degree j)
    {s t : M} (walk : J.Walk s t) (simple : walk.IsPath) (spans : ∀ v, v ∈ walk.support)
    (entry : G.Adj a s.val) (exit : G.Adj b t.val) : Traceable G := by
  classical
  obtain ⟨w,path,cover⟩ := Graffiti189LongestPath.CrossSaturation.terminal_ore_closure
    super degree walk simple spans
  let L : PathOn G M := ⟨w.support.map Subtype.val,fun e => w.support_ne_nil (List.map_eq_nil_iff.mp e),
    (List.chain'_map _).mpr w.chain'_adj_support,path.support_nodup.map Subtype.val_injective,by
      intro v
      constructor
      · rintro m; obtain ⟨u,_,e⟩ := List.mem_map.mp m; exact e ▸ u.property
      · intro vm; exact List.mem_map.mpr ⟨⟨v,vm⟩,cover _,rfl⟩⟩
  apply F.traceable_of_routable_nonneighbors sub on hc (u := s.val) (v := t.val) ?_ entry exit
  exact ⟨L,by simp only [L,PathOn.first,List.head_map,Walk.head_support],
    by simp only [L,PathOn.last,List.getLast_map,Walk.getLast_support]⟩

#print axioms SingletonCut.traceable_of_terminal_closure
end Graffiti199Depleted.Catalogue.Incomplete
