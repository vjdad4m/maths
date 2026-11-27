import NestedCorePrivateAdjacentSatSpec133
import NestedCorePrivateFarControlCharge133
import C7MultiP8AdjCharge133
import C7MultiRadius4Caps133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem adjacent_pair_successor_form (A : Finset (Fin 7)) (two : A.card=2)
    (adj : ∃ i∈A,∃ j∈A,Cyclic i j) :
    ∃ i : Fin 7,∀ j : Fin 7,j∈A↔j=i ∨ j=i+1 := by
  obtain ⟨x,y,d,rfl⟩ := Finset.card_eq_two.mp two
  obtain ⟨a,ha,b,hb,ab⟩ := adj
  have rule : ∀ (a b : Fin 7),Cyclic a b→a+1=b ∨ b+1=a := by decide
  have ne : ∀ (a : Fin 7),¬Cyclic a a := by decide
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact (ne _ ab).elim
  · rcases rule a b ab with s|s
    · exact ⟨a,fun j=>by simp [s]⟩
    · exact ⟨b,fun j=>by simp [s,or_comm]⟩
  · rcases rule a b ab with s|s
    · exact ⟨a,fun j=>by simp [s,or_comm]⟩
    · exact ⟨b,fun j=>by simp [s]⟩
  · exact (ne _ ab).elim

theorem adjacent_exact_clean_sites :
    ∀ i : Fin 7,∀ j : Fin 7,j∈cleanSites ({i,i+1} : Finset (Fin 7)) ↔
    ∃ d : Fin 3,j=satSite i d := by decide

theorem adjacent_exact_clean_card :
    ∀ i : Fin 7,(cleanSites ({i,i+1} : Finset (Fin 7))).card=3 := by decide

theorem complementary_adjacent_sites :
    ∀ i j : Fin 7,j=i ∨ j=i+1 ∨ (∃ k : Fin 7,(k=i ∨ k=i+1) ∧ Cyclic j k) ∨
      ∃ d : Fin 3,j=satSite i d := by decide

theorem far_control_complementary :
    ∀ c : Fin 2,∀ j : Fin 7,
      j∈cleanSites (if c=0 then ({0,3} : Finset (Fin 7)) else {1,4}) →
      j∉(if c=0 then ({0,3} : Finset (Fin 7)) else {1,4}) →
      j=farNeighborSite c := by decide

theorem far_complement_not_marked :
    ∀ c : Fin 2, farNeighborSite c∉(if c=0 then ({0,3} : Finset (Fin 7)) else {1,4}) := by decide

theorem radius_three_from_core_cover (hc : G.Connected)
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (c : V) (cover : ∀ x∈D,G.dist c x≤2) : radius G≤3 := by
  classical
  unfold radius
  have all (x : V) : G.dist c x≤3 := by
    rcases ddom x with h|⟨y,ym,xy⟩
    · exact (cover x h).trans (by decide)
    · have t : G.dist c x≤G.dist c y+G.dist y x := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xy.symm] at t
      have := cover y ym
      omega
  have hm : Finset.univ.sup (G.dist c) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist c) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>all w))

theorem saturated_adjacent_cycle_dist_le_two (H : Hole G 7) (hc : G.Connected)
    (x : V) (i : Fin 7) (z : Fin 3→V)
    (xi : ∀ j : Fin 7,G.Adj x (H.c j) ↔ j=i ∨ j=i+1)
    (xz : ∀ d,G.Adj x (z d))
    (zz : ∀ d,G.Adj (z d) (H.c (satSite i d))) :
    ∀ j,G.dist x (H.c j)≤2 := by
  have two {x y z : V} (xy : G.Adj x y) (yz : G.Adj y z) : G.dist x z≤2 := by
    have h : G.dist x z≤G.dist x y+G.dist y z := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr yz] at h
    exact h
  intro j
  rcases complementary_adjacent_sites i j with eq|eq|⟨k,ht,cyc⟩|⟨d,rfl⟩
  · subst j
    rw [dist_eq_one_iff_adj.mpr ((xi i).mpr (Or.inl rfl))]
    decide
  · subst j
    rw [dist_eq_one_iff_adj.mpr ((xi (i+1)).mpr (Or.inr rfl))]
    decide
  · exact two ((xi k).mpr ht) (((H.adj j k).mpr cyc).symm)
  · exact two (xz d) (zz d)

#print axioms radius_three_from_core_cover
#print axioms saturated_adjacent_cycle_dist_le_two
end Graffiti133NestedWeightedCore
