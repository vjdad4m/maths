import HighBasics28

namespace Graffiti384b.HighSquare28
open SimpleGraph Finset Thin28 JointRank EarFrame33
open private Repair.nbr_mono Repair.full_nbr Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Both sides of an internally protected four-vertex frame can be retained
in complementary trials when every exterior vertex sees at most one pin per side. -/
theorem paired_saving {L R : Finset V} (fr : Frame H L R) (ls : L.card=2) (rs : R.card=2)
    (ws : (L∪R)ᶜ.card=24) (free : H.CliqueFree 5) (fi : Function.Injective (trianglesAt H))
    (scores : ∀ v∈(L∪R)ᶜ,3≤trianglesAt H v)
    (one : ∀ v∈(L∪R)ᶜ,nbr H v L≤1 ∧ nbr H v R≤1) : gamma H≤13 := by
  classical
  let W := (L∪R)ᶜ
  let rk := rank W (trianglesAt H)
  let mass (v : V) := hit H W L 9 v+hit H W R 9 v
  change W.card=24 at ws
  have dl : Disjoint L W := disjoint_left.mpr (fun v vl vw => mem_compl.mp vw (mem_union_left _ vl))
  have dr : Disjoint R W := disjoint_left.mpr (fun v vr vw => mem_compl.mp vw (mem_union_right _ vr))
  have per (v : V) (vm : v∈W) : mass v≤pairedPrice (rk v) := by
    have ri := mem_image_of_mem (rank W (trianglesAt H)) vm
    rw [rank_range _ _ fi.injOn,ws,mem_range] at ri
    have lb := rank_lower W (trianglesAt H) fi.injOn 3 scores vm
    have cap : rk v+3≤RankTable.cap (H.degree v) 3 ∨ 10≤H.degree v :=
      (local_cap H free v).imp_left ((by simpa [rk,Nat.add_comm] using lb : rk v+3≤trianglesAt H v).trans)
    have deg := Repair.full_nbr H v W
    have cut : Wᶜ=L∪R := compl_compl _
    rw [cut,Repair.nbr_add H v fr.1] at deg
    have dg : nbr H v W+nbr H v L+nbr H v R=H.degree v := by omega
    have az := pool_degree H vm
    obtain ⟨xx,yy⟩ := one v vm
    have row := paired_rows ⟨rk v,ri⟩ ⟨nbr H v W,by omega⟩
      ⟨nbr H v L,by omega⟩ ⟨nbr H v R,by omega⟩ (by rw [dg]; exact cap)
    have lp := bill_bound H dl vm 9
    have rp := bill_bound H dr vm 9
    rw [ws] at lp rp
    have line : bill 24 9 (nbr H v W) (nbr H v L)+bill 24 9 (nbr H v W) (nbr H v R)≤pairedPrice (rk v) := by
      dsimp only at row
      have lineOne (c : ℕ) (small : c≤1) : bill 24 9 (nbr H v W) c =
          (if c=0 then FiniteRange.badCount 24 9 (nbr H v W) else (23-nbr H v W).choose 9) := by
        by_cases z : c=0
        · simp [bill,z]
        · have eq : c=1 := by omega
          simp [bill,eq]
      rw [lineOne _ xx,lineOne _ yy]
      exact row
    exact (Nat.add_le_add lp rp).trans line
  have total := sum_le_sum per
  have cost := sum_by_rank W (trianglesAt H) fi.injOn pairedPrice
  rw [ws,totals.1] at cost
  change (∑ w∈W,pairedPrice (rk w))=_ at cost
  rw [cost] at total
  have zero (v : V) (vm : v∉W) : mass v=0 := by
    have m : v∈L∪R := Classical.byContradiction (fun h => vm (mem_compl.mpr h))
    rcases mem_union.mp m with vl|vr
    · simp [mass,kept H vl,supported_zero H 9 (fr.2.1 v vl)]
    · simp [mass,kept H vr,supported_zero H 9 (fr.2.2 v vr)]
  have sumW : (∑ v∈W,mass v)=∑ v,mass v := sum_subset (subset_univ _) (fun v _ => zero v)
  rw [sumW] at total
  simp only [mass,sum_add_distrib] at total
  apply Nat.le_of_not_gt; intro fail
  have left := budget H W L 9
  have right := budget H W R 9
  rw [ws,ls] at left
  rw [ws,rs] at right
  have le := Nat.mul_le_mul_left ((24:ℕ).choose 9) (by omega : 3≤gamma H-2-9)
  have l := le.trans left; have r := le.trans right
  change 3922512≤_ at l r
  omega

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.paired_saving
