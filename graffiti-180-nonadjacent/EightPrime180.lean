import EightBase180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals

/-- Every pair generates the whole graph under the module rule. The certificates
below give one distinguishing vertex at each step. -/
theorem prime : Prime G := by
  intro M hom big
  have force {x a b : V} (am : a∈M) (bm : b∈M) (ed : G.Adj x a) (no : ¬G.Adj x b) : x∈M := by
    by_contra out
    exact no ((hom x out a am b bm).mp ed)
  have h01 (m0 : (0:V)∈M) (m1 : (1:V)∈M) : M=univ := by
    have m3 : (3:V)∈M := force m0 m1 (by decide) (by decide)
    have m4 : (4:V)∈M := force m0 m3 (by decide) (by decide)
    have m5 : (5:V)∈M := force m1 m0 (by decide) (by decide)
    have m2 : (2:V)∈M := force m5 m0 (by decide) (by decide)
    have m6 : (6:V)∈M := force m0 m1 (by decide) (by decide)
    have m7 : (7:V)∈M := force m0 m4 (by decide) (by decide)
    apply eq_univ_of_forall
    intro x
    fin_cases x <;> assumption
  have h04 (m0 : (0:V)∈M) (m4 : (4:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m4 m0 (by decide) (by decide)
    exact h01 m0 mx
  have h05 (m0 : (0:V)∈M) (m5 : (5:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m5 m0 (by decide) (by decide)
    exact h01 m0 mx
  have h07 (m0 : (0:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m7 m0 (by decide) (by decide)
    exact h01 m0 mx
  have h13 (m1 : (1:V)∈M) (m3 : (3:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m3 m1 (by decide) (by decide)
    exact h01 mx m1
  have h14 (m1 : (1:V)∈M) (m4 : (4:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m4 m1 (by decide) (by decide)
    exact h01 mx m1
  have h15 (m1 : (1:V)∈M) (m5 : (5:V)∈M) : M=univ := by
    have mx : (4:V)∈M := force m1 m5 (by decide) (by decide)
    exact h14 m1 mx
  have h16 (m1 : (1:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m6 m1 (by decide) (by decide)
    exact h01 mx m1
  have h17 (m1 : (1:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m7 m1 (by decide) (by decide)
    exact h01 mx m1
  have h24 (m2 : (2:V)∈M) (m4 : (4:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m4 m2 (by decide) (by decide)
    exact h04 mx m4
  have h25 (m2 : (2:V)∈M) (m5 : (5:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m5 m2 (by decide) (by decide)
    exact h15 mx m5
  have h26 (m2 : (2:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (4:V)∈M := force m6 m2 (by decide) (by decide)
    exact h24 m2 mx
  have h27 (m2 : (2:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m7 m2 (by decide) (by decide)
    exact h07 mx m7
  have h34 (m3 : (3:V)∈M) (m4 : (4:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m4 m3 (by decide) (by decide)
    exact h13 mx m3
  have h35 (m3 : (3:V)∈M) (m5 : (5:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m3 m5 (by decide) (by decide)
    exact h05 mx m5
  have h36 (m3 : (3:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (2:V)∈M := force m6 m3 (by decide) (by decide)
    exact h26 mx m6
  have h37 (m3 : (3:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m7 m3 (by decide) (by decide)
    exact h13 mx m3
  have h45 (m4 : (4:V)∈M) (m5 : (5:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m4 m5 (by decide) (by decide)
    exact h04 mx m4
  have h46 (m4 : (4:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m4 m6 (by decide) (by decide)
    exact h14 mx m4
  have h47 (m4 : (4:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (3:V)∈M := force m7 m4 (by decide) (by decide)
    exact h34 mx m4
  have h56 (m5 : (5:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m6 m5 (by decide) (by decide)
    exact h05 mx m5
  have h57 (m5 : (5:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m7 m5 (by decide) (by decide)
    exact h05 mx m5
  have h67 (m6 : (6:V)∈M) (m7 : (7:V)∈M) : M=univ := by
    have mx : (1:V)∈M := force m7 m6 (by decide) (by decide)
    exact h16 mx m6
  have h02 (m0 : (0:V)∈M) (m2 : (2:V)∈M) : M=univ := by
    have mx : (4:V)∈M := force m0 m2 (by decide) (by decide)
    exact h04 m0 mx
  have h03 (m0 : (0:V)∈M) (m3 : (3:V)∈M) : M=univ := by
    have mx : (4:V)∈M := force m0 m3 (by decide) (by decide)
    exact h04 m0 mx
  have h06 (m0 : (0:V)∈M) (m6 : (6:V)∈M) : M=univ := by
    have mx : (2:V)∈M := force m6 m0 (by decide) (by decide)
    exact h02 m0 mx
  have h12 (m1 : (1:V)∈M) (m2 : (2:V)∈M) : M=univ := by
    have mx : (4:V)∈M := force m1 m2 (by decide) (by decide)
    exact h14 m1 mx
  have h23 (m2 : (2:V)∈M) (m3 : (3:V)∈M) : M=univ := by
    have mx : (0:V)∈M := force m3 m2 (by decide) (by decide)
    exact h02 mx m2
  obtain ⟨i,mi,j,mj,ne⟩ := Finset.one_lt_card.mp big
  fin_cases i <;> fin_cases j
  · exact (ne rfl).elim
  · exact h01 mi mj
  · exact h02 mi mj
  · exact h03 mi mj
  · exact h04 mi mj
  · exact h05 mi mj
  · exact h06 mi mj
  · exact h07 mi mj
  · exact h01 mj mi
  · exact (ne rfl).elim
  · exact h12 mi mj
  · exact h13 mi mj
  · exact h14 mi mj
  · exact h15 mi mj
  · exact h16 mi mj
  · exact h17 mi mj
  · exact h02 mj mi
  · exact h12 mj mi
  · exact (ne rfl).elim
  · exact h23 mi mj
  · exact h24 mi mj
  · exact h25 mi mj
  · exact h26 mi mj
  · exact h27 mi mj
  · exact h03 mj mi
  · exact h13 mj mi
  · exact h23 mj mi
  · exact (ne rfl).elim
  · exact h34 mi mj
  · exact h35 mi mj
  · exact h36 mi mj
  · exact h37 mi mj
  · exact h04 mj mi
  · exact h14 mj mi
  · exact h24 mj mi
  · exact h34 mj mi
  · exact (ne rfl).elim
  · exact h45 mi mj
  · exact h46 mi mj
  · exact h47 mi mj
  · exact h05 mj mi
  · exact h15 mj mi
  · exact h25 mj mi
  · exact h35 mj mi
  · exact h45 mj mi
  · exact (ne rfl).elim
  · exact h56 mi mj
  · exact h57 mi mj
  · exact h06 mj mi
  · exact h16 mj mi
  · exact h26 mj mi
  · exact h36 mj mi
  · exact h46 mj mi
  · exact h56 mj mi
  · exact (ne rfl).elim
  · exact h67 mi mj
  · exact h07 mj mi
  · exact h17 mj mi
  · exact h27 mj mi
  · exact h37 mj mi
  · exact h47 mj mi
  · exact h57 mj mi
  · exact h67 mj mi
  · exact (ne rfl).elim

#print axioms Eight.prime
end Minimal180.PairRepair.Eight
