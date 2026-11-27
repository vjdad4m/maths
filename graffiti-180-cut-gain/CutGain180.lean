import SpokePrune180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Restricting w to its two spokes preserves connectivity when the upper
graph is preconnected after deleting w. -/
theorem pruned_connected {J : SimpleGraph V} {x y w : V}
    (xw : J.Adj x w) (wy : J.Adj w y)
    (block : ((J⊔edge x y).induce ({w}ᶜ : Set V)).Preconnected) :
    (prune J w {x,y}).Connected := by
  classical
  let H := prune J w {x,y}
  let Z := ↥({w}ᶜ : Set V)
  let K := (J⊔edge x y).induce ({w}ᶜ : Set V)
  have wx : H.Adj w x := prune_spoke xw.symm (mem_insert_self ..)
  have wY : H.Adj w y := prune_spoke wy (mem_insert_of_mem (mem_singleton_self _))
  have route {a b : Z} (p : K.Walk a b) : H.Reachable a.val b.val := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b _ e _ ih =>
      apply Reachable.trans _ ih
      rcases (show (J⊔edge x y).Adj a.val b.val from e) with ab|ab
      · exact (prune_away a.property b.property ab : H.Adj _ _).reachable
      rcases ((edge_adj ..).mp ab).1 with ⟨ax,by'⟩|⟨ay,bx⟩
      · rw [ax,by']
        exact wx.symm.reachable.trans wY.reachable
      · rw [ay,bx]
        exact wY.symm.reachable.trans wx.reachable
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨w,fun a => ?_⟩
  by_cases aw : a=w
  · exact aw ▸ Reachable.refl _
  · exact wx.reachable.trans (route (block (⟨x,xw.ne⟩ : Z) ⟨a,aw⟩).some)

private theorem restricted_split {J H : SimpleGraph V} {S T : Finset V} {w : V}
    (s : Split J w S T) (hj : H≤J) : Split H w S T :=
  ⟨s.cover,s.meet,fun e => s.edges (hj e),s.smallL,s.smallR⟩

/-- On a split, a strict leaf gain is equivalent to eligibility of the
middle and exact preservation of the lower optimum by pruning its spokes. -/
theorem cut_gain_iff_prune {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T) (xt : x∉T) (ys : y∉S)
    (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (nc : ((J⊔edge x y).induce ({w}ᶜ : Set V)).Preconnected) (U : Finset V) :
    weightedLeaves J U<weightedLeaves (J⊔edge x y) U ↔
      w∈U ∧ weightedLeaves (prune J w {x,y}) U=weightedLeaves J U := by
  classical
  constructor
  · exact gain_preserves_pruned jc (by omega) xy old xw wy U
  rintro ⟨wu,eq⟩
  let H := prune J w {x,y}
  obtain ⟨M,mh,tr,opt⟩ := tree_opt H (pruned_connected xw wy nc) U
  have mj : M≤J := mh.trans (prune_le ..)
  have sm := restricted_split s mj
  have only {i : V} (e : M.Adj w i) : i=x ∨ i=y := by
    simpa only [mem_insert,mem_singleton] using (mh e).2.1 rfl
  obtain ⟨a,wa⟩ := exists_adj (side M S) (sm.connectedL tr.isConnected) sm.largeL ⟨w,sm.both.1⟩
  obtain ⟨b,wb⟩ := exists_adj (side M T) (sm.flip.connectedL tr.isConnected) sm.flip.largeL ⟨w,sm.both.2⟩
  have ax := (only (show M.Adj w a.val from wa)).resolve_right (fun h => ys (h ▸ a.property))
  have by' := (only (show M.Adj w b.val from wb)).resolve_left (fun h => xt (h ▸ b.property))
  apply optimal_middle_gain J M hn x y w xy tr mj U (opt.trans eq)
    (ax ▸ (show M.Adj w a.val from wa).symm) (by' ▸ (show M.Adj w b.val from wb).symm) wu
  rw [←card_neighborFinset_eq_degree,←card_pair xy]
  apply card_le_card
  intro i hi
  simpa only [mem_insert,mem_singleton] using only ((M.mem_neighborFinset ..).mp hi)

/-- A local wing passes the test when restricting its seam to its named tip
preserves the maximum count of the specified eligible leaves. -/
def Ready (B : SimpleGraph V) (w x : V) (U : Finset V) : Prop :=
  weightedLeaves (prune B w {x}) U=weightedLeaves B U

omit [Fintype V] in
private theorem side_prune {J : SimpleGraph V} {Q : Finset V} {w x y : V}
    (wq : w∈Q) (xq : x∈Q) (yq : y∉Q) :
    side (prune J w {x,y}) Q=prune (side J Q) ⟨w,wq⟩ {⟨x,xq⟩} := by
  ext a b
  change (J.Adj a.val b.val ∧ (a.val=w → b.val∈({x,y}:Finset V)) ∧ (b.val=w → a.val∈({x,y}:Finset V))) ↔ _
  have ay : a.val≠y := fun h => yq (h ▸ a.property)
  have by' : b.val≠y := fun h => yq (h ▸ b.property)
  simp only [prune,mem_insert,mem_singleton,Subtype.ext_iff,ay,by',or_false]
  rfl

/-- Exact unrestricted gain test on the cut branch. The two equalities use
only the individual lower wings and their old eligible sets with w erased. -/
theorem cut_gain_iff_wings {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T) (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S)
    (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (nc : ((J⊔edge x y).induce ({w}ᶜ : Set V)).Preconnected) (U : Finset V) :
    weightedLeaves J U<weightedLeaves (J⊔edge x y) U ↔
      w∈U ∧ Ready (side J S) ⟨w,s.both.1⟩ ⟨x,xs⟩ (pull (fun a : ↥S => a.val) (U.erase w)) ∧
      Ready (side J T) ⟨w,s.both.2⟩ ⟨y,yt⟩ (pull (fun a : ↥T => a.val) (U.erase w)) := by
  classical
  let H := prune J w {x,y}
  have h := seam_leaves (restricted_split s (prune_le J w {x,y})) (pruned_connected xw wy nc) U
  have a := side_prune (J:=J) s.both.1 xs ys
  have b : side H T=prune (side J T) ⟨w,s.both.2⟩ {⟨y,yt⟩} := by
    dsimp only [H]
    rw [Finset.pair_comm x y]
    exact side_prune s.both.2 yt xt
  rw [a,b] at h
  rw [cut_gain_iff_prune jc hn s xt ys xy old xw wy nc U,h,seam_leaves s jc U]
  let L := pull (fun a : ↥S => a.val) (U.erase w)
  let R := pull (fun a : ↥T => a.val) (U.erase w)
  have l := leaf_mono (side J S) (prune_le (side J S) ⟨w,s.both.1⟩ {⟨x,xs⟩}) L
  have r := leaf_mono (side J T) (prune_le (side J T) ⟨w,s.both.2⟩ {⟨y,yt⟩}) R
  have sums {a b c d : ℕ} (ab : a≤b) (cd : c≤d) : a+c=b+d ↔ a=b ∧ c=d := by omega
  exact and_congr_right (fun _ => sums l r)

#print axioms pruned_connected
#print axioms cut_gain_iff_prune
#print axioms cut_gain_iff_wings
end Minimal180.CutGain
