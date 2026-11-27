import MarkedPort180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A horizontal chord across a seam leaves the old root layers unchanged.
Both tips lie in the layer immediately beyond the middle. -/
theorem seam_layers {J : SimpleGraph V} (jc : J.Connected) {w x y : V} {S T : Finset V}
    (s : Split J w S T) (yt : y∈T) (wy : J.Adj w y) (old : ¬J.Adj x y) (r : ↥S)
    (flat : (J⊔edge x y).dist x r.val=(J⊔edge x y).dist y r.val) :
    (∀ a,(J⊔edge x y).dist a r.val=J.dist a r.val) ∧
      J.dist x r.val=J.dist w r.val+1 ∧ J.dist y r.val=J.dist w r.val+1 := by
  classical
  let G := J⊔edge x y
  have del : G.deleteEdges {s(x,y)}=J := by
    ext a b
    constructor
    · intro h
      obtain ⟨e,ne⟩ := deleteEdges_adj.mp h
      rcases e with e|e
      · exact e
      · exact (ne (Set.mem_singleton_iff.mpr (Sym2.eq_iff.mpr ((edge_adj ..).mp e).1))).elim
    · intro e
      apply deleteEdges_adj.mpr
      refine ⟨Or.inl e,?_⟩
      intro h
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact old e
      · exact old e.symm
  have down : ∀ a,G.dist a r.val=J.dist a r.val := by
    have same : G.dist x r.val=G.dist y r.val := flat
    have ab : ¬Arc G r.val x y := fun h => by have := h.2.1; omega
    have ba : ¬Arc G r.val y x := fun h => by have := h.2.1; omega
    have ds := (remove_edge_distances G (jc.mono le_sup_left) r.val x y ab ba).2
    rw [del] at ds
    exact fun a => (ds a).symm
  let z : ↥S := ⟨w,s.both.1⟩
  let t : ↥T := ⟨w,s.both.2⟩
  let b : ↥T := ⟨y,yt⟩
  have dist := s.distances jc r
  have step : (side J T).dist b t=1 := dist_eq_one_iff_adj.mpr wy.symm
  have far : J.dist y r.val=J.dist w r.val+1 := by
    rw [dist.2 b,step,dist.1 z,Nat.add_comm]
  refine ⟨down,?_,far⟩
  change G.dist x r.val=G.dist y r.val at flat
  rw [←down,flat,down,far]

/-- The doubly marked case of the actual horizontal cut branch. The only
inductive inputs are the ordinary rooted inequalities on its two sides. -/
theorem horizontal_double_gain {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T) (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S)
    (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (r : ↥S) (odd : Bool) (A : Finset V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    NoCut G → G.dist x r.val=G.dist y r.val → Indep G A → w∈A → w∈P →
    bipartiteNum J=bipartiteNum G+1 →
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
    (∀ p,localBound (side J S) r (parity (side J S) r p)) →
    (∀ p,localBound (side J T) ⟨w,s.both.2⟩ (parity (side J T) ⟨w,s.both.2⟩ p)) →
    weightedLeaves J U<weightedLeaves G U := by
  classical
  intro G P U block flat ind wa wp rank tight left right
  obtain ⟨eq,xs',ys'⟩ := seam_layers jc s yt wy old r flat
  change ∀ a,G.dist a r.val=J.dist a r.val at eq
  have opposite {a : V} (d : J.dist a r.val=J.dist w r.val+1) : a∉P := by
    intro marked
    have u := (mem_parity ..).mp marked
    have v := (mem_parity ..).mp wp
    change G.dist a r.val%2=odd.toNat at u
    change G.dist w r.val%2=odd.toNat at v
    rw [eq,d] at u
    rw [eq] at v
    omega
  have ai (Q : Finset V) : Indep (side J Q) (pull (fun v : ↥Q => v.val) A) := by
    intro a ha b hb ne e
    exact ind _ (mem_pull.mp ha) _ (mem_pull.mp hb) (fun h => ne (Subtype.ext h)) (Or.inl e)
  apply double_mark_gain jc hn s xs xt yt ys xy old xw wy (block w) (by change bipartiteNum G<bipartiteNum J; omega) r A P wa wp
    (fun h => ind x h w wa xw.ne (Or.inl xw)) (opposite xs')
    (fun h => ind w wa y h wy.ne (Or.inl wy)) (opposite ys') tight
  · have p : pull (fun v : ↥S => v.val) P=parity (side J S) r odd := by
      ext v
      simp only [mem_pull,P,mem_parity,eq,(s.distances jc r).1 v]
    simp only []
    rw [p]
    exact left odd _ (ai S)
  · let t : ↥T := ⟨w,s.both.2⟩
    let off := (side J S).dist ⟨w,s.both.1⟩ r
    let p := if off%2=0 then odd else !odd
    have b : pull (fun v : ↥T => v.val) P=parity (side J T) t p := by
      ext v
      simp only [mem_pull,P,mem_parity,eq,(s.distances jc r).2 v]
      change ((side J T).dist v t+off)%2=odd.toNat ↔ (side J T).dist v t%2=p.toNat
      cases odd <;> by_cases h : off%2=0 <;> simp [p,h] <;> omega
    simp only []
    rw [b]
    exact right p _ (ai T)

#print axioms seam_layers
#print axioms horizontal_double_gain
end Minimal180.CutGain
