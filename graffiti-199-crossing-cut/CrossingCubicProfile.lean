import CrossingCutReduction
import CubicPortThreeShores
import TwoCliqueShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem exists_two_of_natCard {A : Set V} [Finite A] (large : 3 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have bound : 1 < Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    omega
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp bound
  obtain ⟨a,b,ne⟩ := exists_pair_ne A
  exact ⟨a.val,a.property,b.val,b.property,fun eq => ne (Subtype.ext eq)⟩

/-- If a surviving-edge crossing failure has a cubic port, the two
large components exhaust the deletion. In a nontraceable graph the
cubic port has no neighbor inside the cut and one shore is a clique. -/
theorem LargeCrossingFailure.cubic_port_profile [Fintype V] [DecidableRel G.Adj]
    (F : LargeCrossingFailure G) (conn : ConnectivityAtLeast G 3)
    (budget : treeNumber G ≤ 5) (no : ¬ Traceable G)
    {r : V} (rD : r ∈ F.cut) (degree : G.degree r = 3) :
    let A := componentShore F.cut F.first
    let B := componentShore F.cut F.second
    (∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ F.cut) ∧
      (∀ d ∈ F.cut, ¬ G.Adj r d) ∧
      (((∃! a : V, a ∈ A ∧ G.Adj r a) ∧ A.Pairwise G.Adj ∧ ¬ B.Pairwise G.Adj) ∨
        ((∃! b : V, b ∈ B ∧ G.Adj r b) ∧ B.Pairwise G.Adj ∧ ¬ A.Pairwise G.Adj)) := by
  classical
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have sizeA : 3 ≤ Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact F.first_large
  have sizeB : 3 ≤ Fintype.card B := by
    rw [← Nat.card_eq_fintype_card]
    exact F.second_large
  have apart : Disjoint A B := componentShore_disjoint F.different
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have boundA := componentShore_boundary F.cut F.first
  have boundB := componentShore_boundary F.cut F.second
  have connA := componentShore_connected F.cut F.first
  have connB := componentShore_connected F.cut F.second
  have twoA := exists_two_of_natCard F.first_large
  have twoB := exists_two_of_natCard F.second_large
  have cover (v : V) : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := by
    by_cases va : v ∈ A
    · exact Or.inl va
    · by_cases vb : v ∈ B
      · exact Or.inr (Or.inl vb)
      · by_cases vd : v ∈ F.cut
        · exact Or.inr (Or.inr vd)
        let c : Survives F.cut := ⟨v,vd⟩
        let K := (DeletionGraph G F.cut).connectedComponentMk c
        let C := componentShore F.cut K
        have cv : v ∈ C := ⟨c,rfl,rfl⟩
        have offFirst : F.first ≠ K := by
          intro e
          apply va
          change v ∈ componentShore F.cut F.first
          rwa [e]
        have offSecond : F.second ≠ K := by
          intro e
          apply vb
          change v ∈ componentShore F.cut F.second
          rwa [e]
        exact (cubic_port_three_shores_impossible conn budget F.size rD degree
          offA offB (componentShore_off_cut F.cut K) apart (componentShore_disjoint offFirst)
          (componentShore_disjoint offSecond) boundA boundB (componentShore_boundary F.cut K)
          connA.preconnected connB.preconnected twoA twoB ⟨v,cv⟩).elim
  have clique := clique_shore_of_cubic_port conn budget F.size rD degree
    sizeA sizeB offA offB apart boundA boundB connA connB
  have incompatible (left : A.Pairwise G.Adj) (right : B.Pairwise G.Adj) : False :=
    no (traceable_of_two_clique_shores conn F.size apart offA offB boundA boundB left right twoA twoB cover)
  refine ⟨cover,?_,?_⟩
  · intro d h e
    obtain ⟨left,right⟩ := clique.2 d (offA d h) (offB d h) e
    exact incompatible left right
  · rcases clique.1 with ⟨unique,left⟩|⟨unique,right⟩
    · exact Or.inl ⟨unique,left,incompatible left⟩
    · exact Or.inr ⟨unique,right,fun left => incompatible left right⟩

#print axioms LargeCrossingFailure.cubic_port_profile

end Graffiti199Depleted.Catalogue
