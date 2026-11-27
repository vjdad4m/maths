import Bounds
import IsoCover

namespace EdgeCover1531
open Finset SimpleGraph TriangleMatching1078 BullCover1125 Graffiti271 GraffitiDegreeTwo
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem path_selection {n k : ℕ} (l r : Fin k → Fin n)
    (edges : ∀ i, (l i).val+1=(r i).val)
    (hit : ∀ x y : Fin n, x.val+1=y.val → ∃ i, x=l i ∨ x=r i ∨ y=l i ∨ y=r i) :
    lineDomination (pathGraph n) ≤ k := by
  classical
  let edge (i : Fin k) : (pathGraph n).edgeSet :=
    ⟨s(l i,r i),pathGraph_adj.mpr (Or.inl (edges i))⟩
  let D := univ.image edge
  have cost : D.card ≤ k := card_image_le.trans_eq (by simp)
  have dom : Dominates (pathGraph n).lineGraph D := by
    apply (dominates_iff _ _).mpr
    intro t
    let x := t.val.out.1
    let y := t.val.out.2
    have repr : s(x,y) = t.val := t.val.out_eq
    have adj : (pathGraph n).Adj x y := show s(x,y) ∈ (pathGraph n).edgeSet from repr ▸ t.property
    have h : ∃ i, x=l i ∨ x=r i ∨ y=l i ∨ y=r i := by
      rcases pathGraph_adj.mp adj with h|h
      · exact hit x y h
      · obtain ⟨i,hi⟩ := hit y x h
        exact ⟨i,by tauto⟩
    obtain ⟨i,hi⟩ := h
    refine ⟨edge i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,?_⟩
    rw [← repr]
    rcases hi with h|h|h|h
    · exact ⟨x,Sym2.mem_iff.mpr (Or.inl h),Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · exact ⟨x,Sym2.mem_iff.mpr (Or.inr h),Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · exact ⟨y,Sym2.mem_iff.mpr (Or.inl h),Sym2.mem_iff.mpr (Or.inr rfl)⟩
    · exact ⟨y,Sym2.mem_iff.mpr (Or.inr h),Sym2.mem_iff.mpr (Or.inr rfl)⟩
  exact (Nat.sInf_le (s:={n | ∃ D : Finset (pathGraph _).edgeSet, D.card=n ∧
    Dominates (pathGraph _).lineGraph D}) ⟨D,rfl,dom⟩).trans cost

private theorem paths_upper : lineDomination (pathGraph 3) ≤ 1 ∧
    lineDomination (pathGraph 4) ≤ 1 ∧ lineDomination (pathGraph 7) ≤ 2 :=
  ⟨path_selection (fun _ : Fin 1 => 0) (fun _ => 1) (by decide) (by decide),
   path_selection (fun _ : Fin 1 => 1) (fun _ => 2) (by decide) (by decide),
   path_selection ![1,4] ![2,5] (by decide) (by decide)⟩

private theorem cycle_counts : Nat.card (cycleGraph 4).edgeSet = 4 ∧
    Nat.card (cycleGraph 7).edgeSet = 7 := by
  simp only [Nat.card_eq_fintype_card]
  decide

private theorem not_cycle (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (cl : Free G claw)
    (tri : TriangleFree G) (tight : edgeCoverNumber G = 2 * lineDomination G)
    {n : ℕ} (f : G ≃g cycleGraph n) : False := by
  have size := Fintype.card_congr f.toEquiv
  rw [Fintype.card_fin] at size
  have o := equality_orders hn hc cl tri tight
  rw [size] at o
  have cap := edge_budget cl tri
  have count := Nat.card_congr f.mapEdgeSet
  have cover := connected_cover_bound hn hc cl tri
  rcases o with rfl|rfl|rfl
  · exact tri (f.symm 0) (f.symm 1) (f.symm 2) (f.symm.map_rel_iff.mpr (by decide))
      (f.symm.map_rel_iff.mpr (by decide)) (f.symm.map_rel_iff.mpr (by decide))
  · rw [cycle_counts.1] at count
    omega
  · rw [cycle_counts.2] at count
    omega

/-- The equality cases among connected graphs are exactly three paths. -/
theorem equality_iff (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (cl : Free G claw)
    (tri : TriangleFree G) :
    edgeCoverNumber G = 2 * lineDomination G ↔
      Nonempty (G ≃g pathGraph 3) ∨ Nonempty (G ≃g pathGraph 4) ∨ Nonempty (G ≃g pathGraph 7) := by
  constructor
  · intro tight
    obtain ⟨m,_,shape⟩ := degree_two_path_or_cycle G hc hn (two_neighbors cl tri)
    rcases shape with path|cycle
    · obtain ⟨f⟩ := path
      have size := Fintype.card_congr f.toEquiv
      rw [Fintype.card_fin] at size
      have orders := equality_orders hn hc cl tri tight
      have choices : m=2 ∨ m=3 ∨ m=6 := by omega
      rcases choices with rfl|rfl|rfl
      · exact Or.inl ⟨f⟩
      · exact Or.inr (Or.inl ⟨f⟩)
      · exact Or.inr (Or.inr ⟨f⟩)
    · exact (not_cycle hn hc cl tri tight cycle.some).elim
  · intro shape
    classical
    have iso : IsolateFree G := by
      intro v
      have h := GraffitiDegrees.deg_pos G hc hn v
      obtain ⟨w,hw⟩ := card_pos.mp h
      exact ⟨w,(mem_nbr G).mp hw⟩
    have upper := row1531 hn cl tri (r:=edgeCoverNumber G) (by simp [edgeCoverValue,iso])
    have lower := vertices_le_twice_cover iso
    have path_case {n k : ℕ} (f : G ≃g pathGraph n) (cost : lineDomination (pathGraph n) ≤ k)
        (arithmetic : 4*k ≤ n+1) : edgeCoverNumber G = 2 * lineDomination G := by
      have size := Fintype.card_congr f.toEquiv
      rw [Fintype.card_fin] at size
      have same := (iso_optimizers f).2
      omega
    rcases shape with f|f|f
    · exact path_case f.some paths_upper.1 (by decide)
    · exact path_case f.some paths_upper.2.1 (by decide)
    · exact path_case f.some paths_upper.2.2 (by decide)

#print axioms row1531
#print axioms count_dominated_edges
#print axioms connected_cover_bound
#print axioms equality_orders
#print axioms equality_iff
end EdgeCover1531
