import SparsePlacement
import SegmentSplice

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (SixTree six_tree_absurd)

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- Pass from a live sparse placement to its checked residual rows.
The trees in the certificate use genuine edges and nonedges only. -/
theorem resolve_sparse {n : ℕ} (b : Layout n) (m : Fin 3) {skipped : List ℕ}
    (d : Family n) (fixed : SparseConsistent b skipped m d) (good : List ℕ)
    (classify : ∀ row, (∃ T, SixTree (d.pattern.edge row) T) ∨
      ∃ tag ∈ good, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j)
    (budget : Catalogue.treeNumber G ≤ 5) {f : Fin (n+1) ↪ V}
    (p : PathOn G {v | v ≠ f (Fin.last n)})
    (real : ∀ i j : Fin (n+1), i.val+1=j.val → j.val<n → i.val∉skipped → G.Adj (f i) (f j))
    (around : ∀ i, ∃ L R : List V, p.vertices = L ++ f (b.prev i) :: f (b.port i) :: f (b.next i) :: R)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3)
    (close : ∀ tag ∈ good, (∀ i j, G.Adj (f i) (f j) ↔ d.pattern.edge tag i j = true) →
      Catalogue.Traceable G) : Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have must (i j) (h : SparseMust b skipped i j) : G.Adj (f i) (f j) := by
    rcases h with ⟨step,lt,off⟩|⟨rfl,jp⟩
    · exact real _ _ step lt off
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp jp
      exact za k
  obtain ⟨row,hrow⟩ := sparse_row fixed must (sparse_off b m p noTrace around za ind dz dm)
  rcases classify row with ⟨T,hT⟩|⟨tag,ok,eq⟩
  · exact six_tree_absurd budget hrow hT
  · exact noTrace (close tag ok (fun i j => (hrow i j).trans (by rw [eq i j])))

omit [DecidableRel G.Adj] [Fintype V] in
theorem splice_from_origin {n k : ℕ} {D : Seams n k} {I : Fin k → List V}
    {f : Fin (n+1) ↪ V} {e : Fin (n+1) → Fin (n+1) → Bool}
    (p : PathOn G {x | x ≠ f (Fin.last n)}) (O : List (SegmentToken n k))
    {L R : List V} (split : p.vertices = L ++ O.flatMap (SegmentToken.expand D I f) ++ R)
    (labels : O.flatMap (SegmentToken.labels D) = (List.finRange n).map Fin.castSucc)
    (seams : (O.filterMap SegmentToken.seam).Perm (List.finRange k))
    (first : O.head?.map (SegmentToken.start D) = some 0)
    (last : O.getLast?.map (SegmentToken.finish D) = some (rightEnd n))
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj)
    {P : List (SegmentToken n k)} (cert : SegmentRoute D e P) : Catalogue.Traceable G := by
  apply traceable_of_segment_route p split ?_ ?_ ?_ chart inside cert
  · have perm := expand_route_perm D I f O (List.Perm.of_eq labels) seams
    simpa [block,Function.comp_def] using perm
  · rw [head_expand_route,first]
    rfl
  · rw [last_expand_route,last]
    rfl

end Graffiti199Depleted.WiderOmission
