import NestedCoreLongGateRadius133
import NestedCorePrivateWeightedGeometry133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedSingleGate Graffiti133NestedLongGates Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def oneCoverage (p q r : Fin 14) (i : Fin 7) : Prop :=
  (∀ j : Fin 7,farSites i j →
    ((i∈profileContacts 0 ∧ j∈profileContacts 0) ∨ (i∈profileContacts p ∧ j∈profileContacts p) ∨
      (i∈profileContacts q ∧ j∈profileContacts q) ∨ (i∈profileContacts r ∧ j∈profileContacts r))) ∧
  (∃ j : Fin 7,j∈profileContacts 0 ∧ (j=i ∨ Cyclic i j))

instance (p q r : Fin 14) (i : Fin 7) : Decidable (oneCoverage p q r i) := by unfold oneCoverage; infer_instance

theorem four_long_cover_one_profile (p : Fin 14) : ∀ q r : Fin 14,
    Separate 0 p → Separate 0 q → Separate 0 r → Separate p q →
      Separate p r → Separate q r → ∃ i : Fin 7,oneCoverage p q r i := by
  fin_cases p <;> decide

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem two_steps (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have h : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at h
  exact h

private theorem separate_matches (H : Hole G 7) (h4 : FourCycleFree G)
    {x y : V} {p q : Fin 14} (ne : x≠y) (px : Matches H x p) (qy : Matches H y q) :
    Separate p q := by
  classical
  unfold Separate
  apply Finset.card_le_one.mpr
  intro a am b bm
  obtain ⟨ap,aq⟩ := Finset.mem_inter.mp am
  obtain ⟨bp,bq⟩ := Finset.mem_inter.mp bm
  exact H.inj (h4 x y (H.c a) (H.c b) ne ((px a).mpr ap) ((qy a).mpr aq)
    ((px b).mpr bp) ((qy b).mpr bq))

theorem radius_three_of_three_additional_long_gates
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (u a b c : V) (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u)
    (pu : Matches H u 0)
    (ua : u≠a) (ub : u≠b) (uc : u≠c) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ao : Outside H.c a) (bo : Outside H.c b) (co : Outside H.c c)
    (ah : (contactSet H a).Nonempty) (bh : (contactSet H b).Nonempty) (ch : (contactSet H c).Nonempty)
    (al : ¬VeryShortGate H a) (bl : ¬VeryShortGate H b) (cl : ¬VeryShortGate H c) : radius G≤3 := by
  obtain ⟨p,pa⟩ := match_long_gate H h4 a ao ah al
  obtain ⟨q,qb⟩ := match_long_gate H h4 b bo bh bl
  obtain ⟨r,rc⟩ := match_long_gate H h4 c co ch cl
  obtain ⟨i,far,iu⟩ := four_long_cover_one_profile p q r
    (separate_matches H h4 ua pu pa) (separate_matches H h4 ub pu qb)
    (separate_matches H h4 uc pu rc) (separate_matches H h4 ab pa qb)
    (separate_matches H h4 ac pa rc) (separate_matches H h4 bc qb rc)
  apply radius_three_from_core_cover hc D ddom (H.c i)
  intro x xm
  rcases shape x xm with ⟨j,rfl⟩|rfl
  · by_cases eq : i=j
    · rw [←eq,dist_self]
      decide
    by_cases near : Cyclic i j
    · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr near)]
      decide
    by_cases mid : ∃ k,Cyclic i k ∧ Cyclic j k
    · obtain ⟨k,ik,jk⟩ := mid
      exact two_steps hc ((H.adj i k).mpr ik) ((H.adj j k).mpr jk).symm
    · rcases far j ⟨eq,near,mid⟩ with ⟨u0,u1⟩|⟨a0,a1⟩|⟨b0,b1⟩|⟨c0,c1⟩
      · exact two_steps hc ((pu i).mpr u0).symm ((pu j).mpr u1)
      · exact two_steps hc ((pa i).mpr a0).symm ((pa j).mpr a1)
      · exact two_steps hc ((qb i).mpr b0).symm ((qb j).mpr b1)
      · exact two_steps hc ((rc i).mpr c0).symm ((rc j).mpr c1)
  · obtain ⟨j,jm,eq|adj⟩ := iu
    · subst j
      rw [dist_eq_one_iff_adj.mpr ((pu i).mpr jm).symm]
      decide
    · exact two_steps hc ((H.adj i j).mpr adj) ((pu j).mpr jm).symm

#print axioms four_long_cover_one_profile
#print axioms radius_three_of_three_additional_long_gates
end Graffiti133NestedOneControl
