import NestedCoreOneControlLongAtlas133
import C7MultiWeightedGlobal133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem site_one_far_geometry :
    ∀ j : Fin 7,j=0 ∨ j=3 ∨ j=5 ∨ (∃ k : Fin 7,(k=0 ∨ k=3) ∧ Cyclic j k) := by decide

theorem one_control_clean_zero
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G) (hr : 4≤radius G)
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (u : V) (uo : Outside H.c u) (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u)
    (up : ∀ j : Fin 7,G.Adj u (H.c j)↔j=0 ∨ j=3)
    (K : Finset V) (cy : ∀ j,H.c j∈K) (uk : u∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i)) :
    ((exteriorNeighbors (restrictedHole H K cy) ⟨u,uk⟩) \
      markedNeighbors (restrictedHole H K cy) ⟨u,uk⟩).card=0 := by
  classical
  let B := restrictedHole H K cy
  let U : (K : Set V) := ⟨u,uk⟩
  have sites : contactSet B U=({0,3} : Finset (Fin 7)) := by
    rw [restricted_contacts H K cy U]
    ext j
    exact (mem_contactSet H u j).trans ((up j).trans (by simp))
  have Uoff : Outside B.c U := fun i e=>uo i (congrArg Subtype.val e)
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z zm
  obtain ⟨ze,zclean⟩ := Finset.mem_sdiff.mp zm
  obtain ⟨_,zoff,uz⟩ := Finset.mem_filter.mp ze
  obtain ⟨j,zj⟩ := dom z zoff
  have allow := neighbor_sites_clean B (restricted_c4 h4 K) Uoff zoff uz j zj
  have no : j∉contactSet B U := fun e=>zclean (Finset.mem_filter.mpr ⟨ze,j,e,zj⟩)
  rw [sites] at allow no
  have j5 := far_control_complementary 0 j allow no
  have e5 : j=5 := j5
  have uz5 : G.Adj z.val (H.c 5) := e5 ▸ zj
  have uz' : G.Adj u z.val := uz
  have two {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) : G.dist a c≤2 := by
    have hd : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at hd
    exact hd
  have small := radius_three_from_core_cover hc D ddom u (by
    intro x xm
    rcases shape x xm with ⟨i,rfl⟩|rfl
    · rcases site_one_far_geometry i with rfl|rfl|rfl|⟨k,hit,ik⟩
      · rw [dist_eq_one_iff_adj.mpr ((up 0).mpr (Or.inl rfl))]
        decide
      · rw [dist_eq_one_iff_adj.mpr ((up 3).mpr (Or.inr rfl))]
        decide
      · exact two uz' uz5
      · exact two ((up k).mpr hit) ((H.adj i k).mpr ik).symm
    · rw [dist_self]
      decide)
  omega

#print axioms one_control_clean_zero
end Graffiti133NestedOneControl
