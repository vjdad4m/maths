import OddCutBudget180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An odd cut in the crossing graph has a child for which it is the
only shortest-path predecessor in the original graph. -/
theorem cut_has_private_child (G : SimpleGraph V) (gc : G.Connected) (r v : V)
    (vr : v≠r) (cut : ¬Con (alternating G (parity G r false)) (univ.erase v)) :
    ∃ w,Arc G r v w := by
  classical
  let H := alternating G (parity G r false)
  let D := univ.erase v
  let K := H.induce (D : Set V)
  by_contra! none
  apply cut
  have rr : r∈D := mem_erase.mpr ⟨vr.symm,mem_univ _⟩
  apply (connected_iff_exists_forall_reachable K).mpr
  refine ⟨⟨r,rr⟩,fun z => Reachable.symm ?_⟩
  induction h : G.dist z.val r using Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases zr : z.val=r
    · exact (Subtype.ext zr : z=⟨r,rr⟩) ▸ Reachable.refl _
    obtain ⟨u,zu,du⟩ := Graffiti169.exists_predecessor G gc r z.val zr
    have pick : ∃ y,y≠v ∧ G.Adj z.val y ∧ G.dist z.val r=G.dist y r+1 := by
      by_contra! no
      have uv : u=v := Classical.byContradiction (fun ne => (no u ne zu) du)
      subst u
      exact none z.val ⟨zu.symm,du,fun x xz dx => Classical.byContradiction (fun ne => (no x ne xz.symm) dx)⟩
    obtain ⟨y,yv,zy,dy⟩ := pick
    let w : ↥(D:Set V) := ⟨y,mem_erase.mpr ⟨yv,mem_univ _⟩⟩
    have edge : K.Adj z w := by
      refine ⟨zy,?_⟩
      change (z.val∈parity G r false ↔ y∉parity G r false)
      simp only [mem_parity,Bool.toNat_false]
      omega
    exact edge.reachable.trans (ih (G.dist y r) (by omega) w rfl)

/-- At a borderline failed root, if the original graph remains connected
after deleting an odd vertex, some horizontal even edge crosses two
different components left by that deletion in the crossing graph. -/
theorem odd_cut_bypass (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (v : V) (odd : v∉parity G r false) (survive : Con G (univ.erase v)) :
    let D := univ.erase v
    let P := parity G r false
    let H := alternating G P
    ∃ a b : ↥(D:Set V),G.Adj a.val b.val ∧ a.val∈P ∧ b.val∈P ∧
      G.dist a.val r=G.dist b.val r ∧ ¬(H.induce (D:Set V)).Reachable a b := by
  classical
  intro D P H
  let K := H.induce (D:Set V)
  have sep := odd_is_cut G gc hn r rank bad v odd
  have crossing : ∃ a b : ↥(D:Set V), G.Adj a.val b.val ∧ ¬K.Reachable a b := by
    by_contra! all
    apply sep
    letI := survive.nonempty
    refine ⟨fun a b => ?_⟩
    obtain ⟨p⟩ := survive a b
    induction p with
    | nil => exact Reachable.refl _
    | cons e _ ih => exact (all _ _ e).trans ih
  obtain ⟨a,b,adj,blocked⟩ := crossing
  have notCross : ¬(a.val∈P ↔ b.val∉P) := fun flip => blocked (show K.Adj a b from ⟨adj,flip⟩).reachable
  have oddmem (x : V) : x∈oddSet G r ↔ x∉P := by simp [oddSet,P,mem_parity]
  have oddInd := (saturated_counts G gc hn r rank bad).2.2.2
  have ap : a.val∈P := by
    by_contra no
    have bn : b.val∉P := by tauto
    exact oddInd _ ((oddmem _).mpr no) _ ((oddmem _).mpr bn) adj.ne adj
  have bp : b.val∈P := by tauto
  refine ⟨a,b,adj,ap,bp,?_,blocked⟩
  have x := gc.dist_triangle (u:=a.val) (v:=b.val) (w:=r)
  have y := gc.dist_triangle (u:=b.val) (v:=a.val) (w:=r)
  rw [dist_eq_one_iff_adj.mpr adj] at x
  rw [dist_eq_one_iff_adj.mpr adj.symm] at y
  simp only [P,mem_parity,Bool.toNat_false] at ap bp
  omega

#print axioms cut_has_private_child
#print axioms odd_cut_bypass
end Minimal180.PortParity
