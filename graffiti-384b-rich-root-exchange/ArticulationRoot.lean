import RichLeafRoot
namespace Graffiti384b.RichRoot
open Finset SimpleGraph OddStars
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every nonempty union of components of the nonleaf core minus r has a neighbor of r. -/
private theorem root_contact (conn : G.Connected) {r : V} (rm : r∈nonleaves G)
    {B : Finset V} (insideS : B⊆rootPool G r) (has : B.Nonempty)
    (closed : ∀x∈B,∀y∈rootPool G r,G.Adj x y → y∈B) :
    ∃x∈B,G.Adj r x := by
  classical
  by_contra! none
  let H := G.induce (nonleaves G:Set V)
  obtain ⟨x,xm⟩ := has
  let start : (nonleaves G : Set V) := ⟨x,(mem_erase.mp (insideS xm)).2⟩
  let dest : (nonleaves G : Set V) := ⟨r,rm⟩
  have all := Prune.connected_core G conn Subset.rfl ⟨r,rm⟩
  have walk := (H.reachable_iff_reflTransGen start dest).mp (all.preconnected _ _)
  have reach {v : (nonleaves G : Set V)} (p : Relation.ReflTransGen H.Adj start v) : v.val∈B := by
    induction p with
    | refl => exact xm
    | @tail a b _ ab ih =>
      have adj : G.Adj a.val b.val := ab
      have br : b.val≠r := fun eq => none _ ih (eq ▸ adj.symm)
      exact closed _ ih _ (mem_erase.mpr ⟨br,b.property⟩) adj
  exact (mem_erase.mp (insideS (reach walk))).1 rfl

/-- A leaf at an articulation of the nonleaf core satisfies the catalogue
bound if the remaining components have positive triangle scores and at most one
score-one vertex in each triangle-edge component. -/
theorem articulation_root (conn : G.Connected) {r z : V} (rm : r∈nonleaves G)
    (rz : G.Adj r z) (leaf : G.degree z=1) (profile : HasResidualPalette G (rootPool G r))
    {u v : V} (um : u∈rootPool G r) (vm : v∈rootPool G r)
    (apart : ¬(inside G (rootPool G r)).Reachable u v) : gamma G≤bound G := by
  classical
  let S := rootPool G r
  let H := inside G S
  let C := S.filter (fun w => H.Reachable u w)
  have cm : u∈C := mem_filter.mpr ⟨um,Reachable.refl _⟩
  have vo : v∉C := fun m => apart (mem_filter.mp m).2
  have left (x : V) (xm : x∈C) (y : V) (ys : y∈S) (adj : G.Adj x y) : y∈C :=
    mem_filter.mpr ⟨ys,(mem_filter.mp xm).2.trans (show H.Adj x y from ⟨adj,(mem_filter.mp xm).1,ys⟩).reachable⟩
  have right (x : V) (xm : x∈S\C) (y : V) (ys : y∈S) (adj : G.Adj x y) : y∈S\C :=
    mem_sdiff.mpr ⟨ys,fun yc => (mem_sdiff.mp xm).2 (left y yc x (mem_sdiff.mp xm).1 adj.symm)⟩
  obtain ⟨a,ac,ra⟩ := root_contact G conn rm (filter_subset ..) ⟨u,cm⟩ left
  obtain ⟨b,bc,rb⟩ := root_contact G conn rm sdiff_subset ⟨v,mem_sdiff.mpr ⟨vm,vo⟩⟩ right
  apply root_exchange G rm rz leaf (Or.inl ⟨profile,Or.inr ?_⟩)
  refine ⟨C,?_,⟨b,mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp bc).1,rb⟩,(mem_sdiff.mp bc).2⟩⟩,
    Or.inl ⟨a,mem_inter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp ac).1,ra⟩,ac⟩⟩⟩
  intro x y xy
  exact ⟨fun h => left x h y xy.1.2.2 xy.1.1,fun h => left y h x xy.1.2.1 xy.1.1.symm⟩

end Graffiti384b.RichRoot
#print axioms Graffiti384b.RichRoot.articulation_root
