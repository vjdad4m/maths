import SparseTransfer
import FragmentFlankLift

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {W : Type*} {G : SimpleGraph W} [DecidableRel G.Adj]

def frame_of_origin {n k : ℕ} {D : Seams n k} {I : Fin k → List W}
    {f : Fin (n+1) ↪ W} {e : Fin (n+1) → Fin (n+1) → Bool}
    {b : Layout n} {mate : Fin (n+1)}
    (p : PathOn G {x | x ≠ f (Fin.last n)}) (O : List (SegmentToken n k))
    (labels : O.flatMap (SegmentToken.labels D) = (List.finRange n).map Fin.castSucc)
    (seams : (O.filterMap SegmentToken.seam).Perm (List.finRange k))
    (first : O.head?.map (SegmentToken.start D) = some 0)
    (last : O.getLast?.map (SegmentToken.finish D) = some (rightEnd n))
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj)
    (ext : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate))
    (pre : ∀ i, f (b.prev i) ∈ p.predecessors)
    (suc : ∀ i, f (b.next i) ∈ p.rev.predecessors) :
    FragmentFrame G b e D mate where
  f := f
  path := p
  B := O.flatMap (SegmentToken.expand D I f)
  I := I
  core := by
    have perm := expand_route_perm D I f O (List.Perm.of_eq labels) seams
    simpa [block,Function.comp_def] using perm
  chart := chart
  inside := inside
  first := by rw [head_expand_route,first]; rfl
  last := by rw [last_expand_route,last]; rfl
  exterior := ext
  pre := pre
  suc := suc

end Graffiti199Depleted.WiderOmission
