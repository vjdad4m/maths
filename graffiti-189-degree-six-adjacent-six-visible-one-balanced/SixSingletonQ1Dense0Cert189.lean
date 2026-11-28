import SixSingletonFiveAllLowCert189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Dense0
open Sat AllLow
set_option maxRecDepth 32768
set_option maxHeartbeats 18000000

packed_rup exclusion
  (include_str "q1-templates/dense0.cnf")
  (include_str "q1-templates/dense0.lrat")

abbrev Bit := Nat→Bool
private def valuation (B : Bit) : Sat.Valuation := fun j=>B j=true
structure Model (B : Bit) : Prop where
  row0 : 1≤marks (B 0)+marks (B 1)+marks (B 2)+marks (B 3)+marks (B 4)
  inactive0 : (¬ B 15=true) → 5≤marks (B 0)+marks (B 1)+marks (B 2)+marks (B 3)+marks (B 4)
  row1 : 1≤marks (B 0)+marks (B 5)+marks (B 6)+marks (B 7)+marks (B 8)
  inactive1 : (¬ B 16=true) → 5≤marks (B 0)+marks (B 5)+marks (B 6)+marks (B 7)+marks (B 8)
  row2 : 1≤marks (B 1)+marks (B 5)+marks (B 9)+marks (B 10)+marks (B 11)
  inactive2 : (¬ B 17=true) → 5≤marks (B 1)+marks (B 5)+marks (B 9)+marks (B 10)+marks (B 11)
  row3 : 1≤marks (B 2)+marks (B 6)+marks (B 9)+marks (B 12)+marks (B 13)
  inactive3 : (¬ B 18=true) → 5≤marks (B 2)+marks (B 6)+marks (B 9)+marks (B 12)+marks (B 13)
  row4 : 3≤marks (B 3)+marks (B 7)+marks (B 10)+marks (B 12)+marks (B 14)
  inactive4 : (¬ B 19=true) → 4≤marks (B 3)+marks (B 7)+marks (B 10)+marks (B 12)+marks (B 14)
  row5 : 3≤marks (B 4)+marks (B 8)+marks (B 11)+marks (B 13)+marks (B 14)
  inactive5 : (¬ B 20=true) → 4≤marks (B 4)+marks (B 8)+marks (B 11)+marks (B 13)+marks (B 14)
  activeA : 1≤marks (B 15)+marks (B 16)
  activeB : 1≤marks (B 17)+marks (B 18)

def requirement : Fin 37 → List Nat := ![[7,8,10,13,15],[3,4,11,12,16],[3,8,12,13,17],[4,7,10,11,18],[5,8,12,14,15],[2,4,10,14,16],[3,9,11,14,15],[7,9,13,14,16],[1,4,7,14,17],[3,6,8,14,17],[4,10,12,13,15],[8,10,11,12,15],[3,10,11,13,15],[7,11,12,13,15],[8,9,10,14,15],[4,9,12,14,16],[2,7,11,14,15],[3,5,13,14,15],[1,10,13,14,15],[4,6,10,14,15],[7,8,11,12,15],[1,4,12,14,16],[0,10,13,14,15],[2,10,13,14,15],[6,7,11,14,15],[3,7,11,13,15],[4,8,10,12,15],[4,7,10,13,16],[0,11,12,14,15],[1,7,13,14,15],[3,8,10,13,15],[4,5,12,14,15],[2,3,8,14,17],[3,7,8,9,15],[3,6,11,12,15],[3,8,11,12,15],[4,7,11,12,15]]
def visit : Fin 37 → List (Fin 9) := ![[0,6,8,7,2,4,1,5,3],[1,6,8,7,2,5,0,4,3],[2,7,8,6,0,4,3,5,1],[3,7,8,6,0,5,2,4,1],[0,6,8,7,2,1,5,4,3],[1,6,8,7,2,4,5,0,3],[0,4,5,2,3,7,8,6,1],[1,4,5,3,2,7,8,6,0],[2,0,5,4,1,6,8,7,3],[2,7,8,6,0,4,5,1,3],[0,5,3,4,2,7,8,6,1],[0,6,8,7,3,4,2,5,1],[0,4,2,5,3,7,8,6,1],[0,6,8,7,2,5,3,4,1],[0,6,8,7,3,2,4,5,1],[1,6,8,7,2,3,4,5,0],[0,3,7,8,6,1,4,5,2],[0,4,5,3,7,8,6,1,2],[0,2,4,5,3,7,8,6,1],[0,5,4,2,7,8,6,1,3],[0,6,8,7,2,5,1,4,3],[1,6,8,7,2,0,5,4,3],[0,1,6,8,7,2,4,5,3],[0,3,5,4,2,7,8,6,1],[0,6,8,7,2,5,4,1,3],[0,4,1,6,8,7,2,5,3],[0,5,1,6,8,7,2,4,3],[1,4,2,7,8,6,0,5,3],[0,1,6,8,7,2,5,4,3],[0,2,7,8,6,1,4,5,3],[0,4,2,7,8,6,1,5,3],[0,5,4,3,7,8,6,1,2],[2,7,8,6,1,5,4,0,3],[0,4,1,5,6,8,7,2,3],[0,4,3,1,6,8,7,2,5],[0,4,3,7,8,6,1,5,2],[0,5,2,7,8,6,1,4,3]]
abbrev Found (B : Bit) := ∃ k,∀ j∈requirement k,B j=true
private theorem mark_le_one (a : Bool) : marks a≤1 := by cases a <;> decide
private theorem mark_zero (a : Bool) (h : ¬a=true) : marks a=0 := by cases a <;> simp_all [marks]

private theorem r0 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 2, .pos 3, .pos 4] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 2=true) → (¬ B 3=true) → (¬ B 4=true) → False
  intro h0 h1 h2 h3 h4
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h2, mark_zero _ h3, mark_zero _ h4] at N
  omega

private theorem r1 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 0] := by
  change (¬ B 15=true) → (¬ B 0=true) → False
  intro h15 h0
  have N := M.inactive0 h15
  rw [mark_zero _ h0] at N
  have u1 := mark_le_one (B 1)
  have u2 := mark_le_one (B 2)
  have u3 := mark_le_one (B 3)
  have u4 := mark_le_one (B 4)
  omega

private theorem r2 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 1] := by
  change (¬ B 15=true) → (¬ B 1=true) → False
  intro h15 h1
  have N := M.inactive0 h15
  rw [mark_zero _ h1] at N
  have u0 := mark_le_one (B 0)
  have u2 := mark_le_one (B 2)
  have u3 := mark_le_one (B 3)
  have u4 := mark_le_one (B 4)
  omega

private theorem r3 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 2] := by
  change (¬ B 15=true) → (¬ B 2=true) → False
  intro h15 h2
  have N := M.inactive0 h15
  rw [mark_zero _ h2] at N
  have u0 := mark_le_one (B 0)
  have u1 := mark_le_one (B 1)
  have u3 := mark_le_one (B 3)
  have u4 := mark_le_one (B 4)
  omega

private theorem r4 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 3] := by
  change (¬ B 15=true) → (¬ B 3=true) → False
  intro h15 h3
  have N := M.inactive0 h15
  rw [mark_zero _ h3] at N
  have u0 := mark_le_one (B 0)
  have u1 := mark_le_one (B 1)
  have u2 := mark_le_one (B 2)
  have u4 := mark_le_one (B 4)
  omega

private theorem r5 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 4] := by
  change (¬ B 15=true) → (¬ B 4=true) → False
  intro h15 h4
  have N := M.inactive0 h15
  rw [mark_zero _ h4] at N
  have u0 := mark_le_one (B 0)
  have u1 := mark_le_one (B 1)
  have u2 := mark_le_one (B 2)
  have u3 := mark_le_one (B 3)
  omega

private theorem r6 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 5, .pos 6, .pos 7, .pos 8] := by
  change (¬ B 0=true) → (¬ B 5=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → False
  intro h0 h5 h6 h7 h8
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h5, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8] at N
  omega

private theorem r7 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 0] := by
  change (¬ B 16=true) → (¬ B 0=true) → False
  intro h16 h0
  have N := M.inactive1 h16
  rw [mark_zero _ h0] at N
  have u5 := mark_le_one (B 5)
  have u6 := mark_le_one (B 6)
  have u7 := mark_le_one (B 7)
  have u8 := mark_le_one (B 8)
  omega

private theorem r8 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 5] := by
  change (¬ B 16=true) → (¬ B 5=true) → False
  intro h16 h5
  have N := M.inactive1 h16
  rw [mark_zero _ h5] at N
  have u0 := mark_le_one (B 0)
  have u6 := mark_le_one (B 6)
  have u7 := mark_le_one (B 7)
  have u8 := mark_le_one (B 8)
  omega

private theorem r9 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 6] := by
  change (¬ B 16=true) → (¬ B 6=true) → False
  intro h16 h6
  have N := M.inactive1 h16
  rw [mark_zero _ h6] at N
  have u0 := mark_le_one (B 0)
  have u5 := mark_le_one (B 5)
  have u7 := mark_le_one (B 7)
  have u8 := mark_le_one (B 8)
  omega

private theorem r10 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 7] := by
  change (¬ B 16=true) → (¬ B 7=true) → False
  intro h16 h7
  have N := M.inactive1 h16
  rw [mark_zero _ h7] at N
  have u0 := mark_le_one (B 0)
  have u5 := mark_le_one (B 5)
  have u6 := mark_le_one (B 6)
  have u8 := mark_le_one (B 8)
  omega

private theorem r11 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 8] := by
  change (¬ B 16=true) → (¬ B 8=true) → False
  intro h16 h8
  have N := M.inactive1 h16
  rw [mark_zero _ h8] at N
  have u0 := mark_le_one (B 0)
  have u5 := mark_le_one (B 5)
  have u6 := mark_le_one (B 6)
  have u7 := mark_le_one (B 7)
  omega

private theorem r12 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 5, .pos 9, .pos 10, .pos 11] := by
  change (¬ B 1=true) → (¬ B 5=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → False
  intro h1 h5 h9 h10 h11
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h5, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11] at N
  omega

private theorem r13 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 1] := by
  change (¬ B 17=true) → (¬ B 1=true) → False
  intro h17 h1
  have N := M.inactive2 h17
  rw [mark_zero _ h1] at N
  have u5 := mark_le_one (B 5)
  have u9 := mark_le_one (B 9)
  have u10 := mark_le_one (B 10)
  have u11 := mark_le_one (B 11)
  omega

private theorem r14 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 5] := by
  change (¬ B 17=true) → (¬ B 5=true) → False
  intro h17 h5
  have N := M.inactive2 h17
  rw [mark_zero _ h5] at N
  have u1 := mark_le_one (B 1)
  have u9 := mark_le_one (B 9)
  have u10 := mark_le_one (B 10)
  have u11 := mark_le_one (B 11)
  omega

private theorem r15 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 9] := by
  change (¬ B 17=true) → (¬ B 9=true) → False
  intro h17 h9
  have N := M.inactive2 h17
  rw [mark_zero _ h9] at N
  have u1 := mark_le_one (B 1)
  have u5 := mark_le_one (B 5)
  have u10 := mark_le_one (B 10)
  have u11 := mark_le_one (B 11)
  omega

private theorem r16 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 10] := by
  change (¬ B 17=true) → (¬ B 10=true) → False
  intro h17 h10
  have N := M.inactive2 h17
  rw [mark_zero _ h10] at N
  have u1 := mark_le_one (B 1)
  have u5 := mark_le_one (B 5)
  have u9 := mark_le_one (B 9)
  have u11 := mark_le_one (B 11)
  omega

private theorem r17 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 11] := by
  change (¬ B 17=true) → (¬ B 11=true) → False
  intro h17 h11
  have N := M.inactive2 h17
  rw [mark_zero _ h11] at N
  have u1 := mark_le_one (B 1)
  have u5 := mark_le_one (B 5)
  have u9 := mark_le_one (B 9)
  have u10 := mark_le_one (B 10)
  omega

private theorem r18 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 9, .pos 12, .pos 13] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 9=true) → (¬ B 12=true) → (¬ B 13=true) → False
  intro h2 h6 h9 h12 h13
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h9, mark_zero _ h12, mark_zero _ h13] at N
  omega

private theorem r19 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 18, .pos 2] := by
  change (¬ B 18=true) → (¬ B 2=true) → False
  intro h18 h2
  have N := M.inactive3 h18
  rw [mark_zero _ h2] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r20 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 18, .pos 6] := by
  change (¬ B 18=true) → (¬ B 6=true) → False
  intro h18 h6
  have N := M.inactive3 h18
  rw [mark_zero _ h6] at N
  have u2 := mark_le_one (B 2)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r21 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 18, .pos 9] := by
  change (¬ B 18=true) → (¬ B 9=true) → False
  intro h18 h9
  have N := M.inactive3 h18
  rw [mark_zero _ h9] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r22 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 18, .pos 12] := by
  change (¬ B 18=true) → (¬ B 12=true) → False
  intro h18 h12
  have N := M.inactive3 h18
  rw [mark_zero _ h12] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  omega

private theorem r23 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 18, .pos 13] := by
  change (¬ B 18=true) → (¬ B 13=true) → False
  intro h18 h13
  have N := M.inactive3 h18
  rw [mark_zero _ h13] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  omega

private theorem r24 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 10] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 10=true) → False
  intro h3 h7 h10
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h10] at N
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r25 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 12] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 12=true) → False
  intro h3 h7 h12
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h12] at N
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r26 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 14] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 14=true) → False
  intro h3 h7 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h14] at N
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  omega

private theorem r27 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 10, .pos 12] := by
  change (¬ B 3=true) → (¬ B 10=true) → (¬ B 12=true) → False
  intro h3 h10 h12
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h10, mark_zero _ h12] at N
  have u7 := mark_le_one (B 7)
  have u14 := mark_le_one (B 14)
  omega

private theorem r28 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 10, .pos 14] := by
  change (¬ B 3=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h3 h10 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h10, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  omega

private theorem r29 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 12, .pos 14] := by
  change (¬ B 3=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h3 h12 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h12, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  omega

private theorem r30 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 12] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 12=true) → False
  intro h7 h10 h12
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u14 := mark_le_one (B 14)
  omega

private theorem r31 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 14] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h7 h10 h14
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u12 := mark_le_one (B 12)
  omega

private theorem r32 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 12, .pos 14] := by
  change (¬ B 7=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h7 h12 h14
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h12, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  omega

private theorem r33 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 10, .pos 12, .pos 14] := by
  change (¬ B 10=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h10 h12 h14
  have N := M.row4
  rw [mark_zero _ h10, mark_zero _ h12, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  omega

private theorem r34 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 3, .pos 7] := by
  change (¬ B 19=true) → (¬ B 3=true) → (¬ B 7=true) → False
  intro h19 h3 h7
  have N := M.inactive4 h19
  rw [mark_zero _ h3, mark_zero _ h7] at N
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r35 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 3, .pos 10] := by
  change (¬ B 19=true) → (¬ B 3=true) → (¬ B 10=true) → False
  intro h19 h3 h10
  have N := M.inactive4 h19
  rw [mark_zero _ h3, mark_zero _ h10] at N
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r36 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 3, .pos 12] := by
  change (¬ B 19=true) → (¬ B 3=true) → (¬ B 12=true) → False
  intro h19 h3 h12
  have N := M.inactive4 h19
  rw [mark_zero _ h3, mark_zero _ h12] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r37 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 3, .pos 14] := by
  change (¬ B 19=true) → (¬ B 3=true) → (¬ B 14=true) → False
  intro h19 h3 h14
  have N := M.inactive4 h19
  rw [mark_zero _ h3, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  omega

private theorem r38 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 7, .pos 10] := by
  change (¬ B 19=true) → (¬ B 7=true) → (¬ B 10=true) → False
  intro h19 h7 h10
  have N := M.inactive4 h19
  rw [mark_zero _ h7, mark_zero _ h10] at N
  have u3 := mark_le_one (B 3)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r39 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 7, .pos 12] := by
  change (¬ B 19=true) → (¬ B 7=true) → (¬ B 12=true) → False
  intro h19 h7 h12
  have N := M.inactive4 h19
  rw [mark_zero _ h7, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r40 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 7, .pos 14] := by
  change (¬ B 19=true) → (¬ B 7=true) → (¬ B 14=true) → False
  intro h19 h7 h14
  have N := M.inactive4 h19
  rw [mark_zero _ h7, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  omega

private theorem r41 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 10, .pos 12] := by
  change (¬ B 19=true) → (¬ B 10=true) → (¬ B 12=true) → False
  intro h19 h10 h12
  have N := M.inactive4 h19
  rw [mark_zero _ h10, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u14 := mark_le_one (B 14)
  omega

private theorem r42 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 10, .pos 14] := by
  change (¬ B 19=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h19 h10 h14
  have N := M.inactive4 h19
  rw [mark_zero _ h10, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  omega

private theorem r43 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 19, .pos 12, .pos 14] := by
  change (¬ B 19=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h19 h12 h14
  have N := M.inactive4 h19
  rw [mark_zero _ h12, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  omega

private theorem r44 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 11] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 11=true) → False
  intro h4 h8 h11
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h11] at N
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r45 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 13] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 13=true) → False
  intro h4 h8 h13
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h13] at N
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  omega

private theorem r46 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 14] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 14=true) → False
  intro h4 h8 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h14] at N
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  omega

private theorem r47 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 11, .pos 13] := by
  change (¬ B 4=true) → (¬ B 11=true) → (¬ B 13=true) → False
  intro h4 h11 h13
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h11, mark_zero _ h13] at N
  have u8 := mark_le_one (B 8)
  have u14 := mark_le_one (B 14)
  omega

private theorem r48 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 11, .pos 14] := by
  change (¬ B 4=true) → (¬ B 11=true) → (¬ B 14=true) → False
  intro h4 h11 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h11, mark_zero _ h14] at N
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  omega

private theorem r49 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 13, .pos 14] := by
  change (¬ B 4=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h4 h13 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h13, mark_zero _ h14] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  omega

private theorem r50 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 13] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 13=true) → False
  intro h8 h11 h13
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h13] at N
  have u4 := mark_le_one (B 4)
  have u14 := mark_le_one (B 14)
  omega

private theorem r51 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 14] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 14=true) → False
  intro h8 h11 h14
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u13 := mark_le_one (B 13)
  omega

private theorem r52 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 13, .pos 14] := by
  change (¬ B 8=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h8 h13 h14
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h13, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  omega

private theorem r53 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 11, .pos 13, .pos 14] := by
  change (¬ B 11=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h11 h13 h14
  have N := M.row5
  rw [mark_zero _ h11, mark_zero _ h13, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  omega

private theorem r54 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 4, .pos 8] := by
  change (¬ B 20=true) → (¬ B 4=true) → (¬ B 8=true) → False
  intro h20 h4 h8
  have N := M.inactive5 h20
  rw [mark_zero _ h4, mark_zero _ h8] at N
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r55 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 4, .pos 11] := by
  change (¬ B 20=true) → (¬ B 4=true) → (¬ B 11=true) → False
  intro h20 h4 h11
  have N := M.inactive5 h20
  rw [mark_zero _ h4, mark_zero _ h11] at N
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r56 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 4, .pos 13] := by
  change (¬ B 20=true) → (¬ B 4=true) → (¬ B 13=true) → False
  intro h20 h4 h13
  have N := M.inactive5 h20
  rw [mark_zero _ h4, mark_zero _ h13] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  omega

private theorem r57 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 4, .pos 14] := by
  change (¬ B 20=true) → (¬ B 4=true) → (¬ B 14=true) → False
  intro h20 h4 h14
  have N := M.inactive5 h20
  rw [mark_zero _ h4, mark_zero _ h14] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  omega

private theorem r58 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 8, .pos 11] := by
  change (¬ B 20=true) → (¬ B 8=true) → (¬ B 11=true) → False
  intro h20 h8 h11
  have N := M.inactive5 h20
  rw [mark_zero _ h8, mark_zero _ h11] at N
  have u4 := mark_le_one (B 4)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r59 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 8, .pos 13] := by
  change (¬ B 20=true) → (¬ B 8=true) → (¬ B 13=true) → False
  intro h20 h8 h13
  have N := M.inactive5 h20
  rw [mark_zero _ h8, mark_zero _ h13] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  omega

private theorem r60 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 8, .pos 14] := by
  change (¬ B 20=true) → (¬ B 8=true) → (¬ B 14=true) → False
  intro h20 h8 h14
  have N := M.inactive5 h20
  rw [mark_zero _ h8, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  omega

private theorem r61 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 11, .pos 13] := by
  change (¬ B 20=true) → (¬ B 11=true) → (¬ B 13=true) → False
  intro h20 h11 h13
  have N := M.inactive5 h20
  rw [mark_zero _ h11, mark_zero _ h13] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u14 := mark_le_one (B 14)
  omega

private theorem r62 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 11, .pos 14] := by
  change (¬ B 20=true) → (¬ B 11=true) → (¬ B 14=true) → False
  intro h20 h11 h14
  have N := M.inactive5 h20
  rw [mark_zero _ h11, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  omega

private theorem r63 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 20, .pos 13, .pos 14] := by
  change (¬ B 20=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h20 h13 h14
  have N := M.inactive5 h20
  rw [mark_zero _ h13, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  omega

private theorem r64 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16] := by
  change (¬ B 15=true) → (¬ B 16=true) → False
  intro h15 h16
  have N := M.activeA
  rw [mark_zero _ h15, mark_zero _ h16] at N
  omega

private theorem r65 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 18] := by
  change (¬ B 17=true) → (¬ B 18=true) → False
  intro h17 h18
  have N := M.activeB
  rw [mark_zero _ h17, mark_zero _ h18] at N
  omega

private theorem r66 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 8, .neg 10, .neg 13, .neg 15] := by
  change (B 7=true) → (B 8=true) → (B 10=true) → (B 13=true) → (B 15=true) → False
  intro h7 h8 h10 h13 h15
  apply no ⟨0,?_⟩
  intro j m
  change j∈[7,8,10,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r67 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 4, .neg 11, .neg 12, .neg 16] := by
  change (B 3=true) → (B 4=true) → (B 11=true) → (B 12=true) → (B 16=true) → False
  intro h3 h4 h11 h12 h16
  apply no ⟨1,?_⟩
  intro j m
  change j∈[3,4,11,12,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h4
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h16

private theorem r68 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 8, .neg 12, .neg 13, .neg 17] := by
  change (B 3=true) → (B 8=true) → (B 12=true) → (B 13=true) → (B 17=true) → False
  intro h3 h8 h12 h13 h17
  apply no ⟨2,?_⟩
  intro j m
  change j∈[3,8,12,13,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h17

private theorem r69 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 7, .neg 10, .neg 11, .neg 18] := by
  change (B 4=true) → (B 7=true) → (B 10=true) → (B 11=true) → (B 18=true) → False
  intro h4 h7 h10 h11 h18
  apply no ⟨3,?_⟩
  intro j m
  change j∈[4,7,10,11,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h18

private theorem r70 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 5, .neg 8, .neg 12, .neg 14, .neg 15] := by
  change (B 5=true) → (B 8=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h5 h8 h12 h14 h15
  apply no ⟨4,?_⟩
  intro j m
  change j∈[5,8,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h5
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r71 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 10, .neg 14, .neg 16] := by
  change (B 2=true) → (B 4=true) → (B 10=true) → (B 14=true) → (B 16=true) → False
  intro h2 h4 h10 h14 h16
  apply no ⟨5,?_⟩
  intro j m
  change j∈[2,4,10,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r72 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 9, .neg 11, .neg 14, .neg 15] := by
  change (B 3=true) → (B 9=true) → (B 11=true) → (B 14=true) → (B 15=true) → False
  intro h3 h9 h11 h14 h15
  apply no ⟨6,?_⟩
  intro j m
  change j∈[3,9,11,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h9
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r73 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 9, .neg 13, .neg 14, .neg 16] := by
  change (B 7=true) → (B 9=true) → (B 13=true) → (B 14=true) → (B 16=true) → False
  intro h7 h9 h13 h14 h16
  apply no ⟨7,?_⟩
  intro j m
  change j∈[7,9,13,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r74 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 7, .neg 14, .neg 17] := by
  change (B 1=true) → (B 4=true) → (B 7=true) → (B 14=true) → (B 17=true) → False
  intro h1 h4 h7 h14 h17
  apply no ⟨8,?_⟩
  intro j m
  change j∈[1,4,7,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r75 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 8, .neg 14, .neg 17] := by
  change (B 3=true) → (B 6=true) → (B 8=true) → (B 14=true) → (B 17=true) → False
  intro h3 h6 h8 h14 h17
  apply no ⟨9,?_⟩
  intro j m
  change j∈[3,6,8,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h8
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r76 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 10, .neg 12, .neg 13, .neg 15] := by
  change (B 4=true) → (B 10=true) → (B 12=true) → (B 13=true) → (B 15=true) → False
  intro h4 h10 h12 h13 h15
  apply no ⟨10,?_⟩
  intro j m
  change j∈[4,10,12,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r77 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 8, .neg 10, .neg 11, .neg 12, .neg 15] := by
  change (B 8=true) → (B 10=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h8 h10 h11 h12 h15
  apply no ⟨11,?_⟩
  intro j m
  change j∈[8,10,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r78 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 10, .neg 11, .neg 13, .neg 15] := by
  change (B 3=true) → (B 10=true) → (B 11=true) → (B 13=true) → (B 15=true) → False
  intro h3 h10 h11 h13 h15
  apply no ⟨12,?_⟩
  intro j m
  change j∈[3,10,11,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r79 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 11, .neg 12, .neg 13, .neg 15] := by
  change (B 7=true) → (B 11=true) → (B 12=true) → (B 13=true) → (B 15=true) → False
  intro h7 h11 h12 h13 h15
  apply no ⟨13,?_⟩
  intro j m
  change j∈[7,11,12,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r80 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 8, .neg 9, .neg 10, .neg 14, .neg 15] := by
  change (B 8=true) → (B 9=true) → (B 10=true) → (B 14=true) → (B 15=true) → False
  intro h8 h9 h10 h14 h15
  apply no ⟨14,?_⟩
  intro j m
  change j∈[8,9,10,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r81 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 9, .neg 12, .neg 14, .neg 16] := by
  change (B 4=true) → (B 9=true) → (B 12=true) → (B 14=true) → (B 16=true) → False
  intro h4 h9 h12 h14 h16
  apply no ⟨15,?_⟩
  intro j m
  change j∈[4,9,12,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h9
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r82 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 7, .neg 11, .neg 14, .neg 15] := by
  change (B 2=true) → (B 7=true) → (B 11=true) → (B 14=true) → (B 15=true) → False
  intro h2 h7 h11 h14 h15
  apply no ⟨16,?_⟩
  intro j m
  change j∈[2,7,11,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r83 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 5, .neg 13, .neg 14, .neg 15] := by
  change (B 3=true) → (B 5=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h3 h5 h13 h14 h15
  apply no ⟨17,?_⟩
  intro j m
  change j∈[3,5,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h5
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r84 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 10, .neg 13, .neg 14, .neg 15] := by
  change (B 1=true) → (B 10=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h1 h10 h13 h14 h15
  apply no ⟨18,?_⟩
  intro j m
  change j∈[1,10,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r85 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 6, .neg 10, .neg 14, .neg 15] := by
  change (B 4=true) → (B 6=true) → (B 10=true) → (B 14=true) → (B 15=true) → False
  intro h4 h6 h10 h14 h15
  apply no ⟨19,?_⟩
  intro j m
  change j∈[4,6,10,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r86 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 8, .neg 11, .neg 12, .neg 15] := by
  change (B 7=true) → (B 8=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h7 h8 h11 h12 h15
  apply no ⟨20,?_⟩
  intro j m
  change j∈[7,8,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r87 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 12, .neg 14, .neg 16] := by
  change (B 1=true) → (B 4=true) → (B 12=true) → (B 14=true) → (B 16=true) → False
  intro h1 h4 h12 h14 h16
  apply no ⟨21,?_⟩
  intro j m
  change j∈[1,4,12,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r88 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 10, .neg 13, .neg 14, .neg 15] := by
  change (B 0=true) → (B 10=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h0 h10 h13 h14 h15
  apply no ⟨22,?_⟩
  intro j m
  change j∈[0,10,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r89 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 10, .neg 13, .neg 14, .neg 15] := by
  change (B 2=true) → (B 10=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h2 h10 h13 h14 h15
  apply no ⟨23,?_⟩
  intro j m
  change j∈[2,10,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r90 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 6, .neg 7, .neg 11, .neg 14, .neg 15] := by
  change (B 6=true) → (B 7=true) → (B 11=true) → (B 14=true) → (B 15=true) → False
  intro h6 h7 h11 h14 h15
  apply no ⟨24,?_⟩
  intro j m
  change j∈[6,7,11,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h6
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r91 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 7, .neg 11, .neg 13, .neg 15] := by
  change (B 3=true) → (B 7=true) → (B 11=true) → (B 13=true) → (B 15=true) → False
  intro h3 h7 h11 h13 h15
  apply no ⟨25,?_⟩
  intro j m
  change j∈[3,7,11,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r92 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 8, .neg 10, .neg 12, .neg 15] := by
  change (B 4=true) → (B 8=true) → (B 10=true) → (B 12=true) → (B 15=true) → False
  intro h4 h8 h10 h12 h15
  apply no ⟨26,?_⟩
  intro j m
  change j∈[4,8,10,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r93 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 7, .neg 10, .neg 13, .neg 16] := by
  change (B 4=true) → (B 7=true) → (B 10=true) → (B 13=true) → (B 16=true) → False
  intro h4 h7 h10 h13 h16
  apply no ⟨27,?_⟩
  intro j m
  change j∈[4,7,10,13,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h16

private theorem r94 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 11, .neg 12, .neg 14, .neg 15] := by
  change (B 0=true) → (B 11=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h0 h11 h12 h14 h15
  apply no ⟨28,?_⟩
  intro j m
  change j∈[0,11,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r95 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 7, .neg 13, .neg 14, .neg 15] := by
  change (B 1=true) → (B 7=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h1 h7 h13 h14 h15
  apply no ⟨29,?_⟩
  intro j m
  change j∈[1,7,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h7
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r96 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 8, .neg 10, .neg 13, .neg 15] := by
  change (B 3=true) → (B 8=true) → (B 10=true) → (B 13=true) → (B 15=true) → False
  intro h3 h8 h10 h13 h15
  apply no ⟨30,?_⟩
  intro j m
  change j∈[3,8,10,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r97 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 5, .neg 12, .neg 14, .neg 15] := by
  change (B 4=true) → (B 5=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h4 h5 h12 h14 h15
  apply no ⟨31,?_⟩
  intro j m
  change j∈[4,5,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h5
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r98 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 8, .neg 14, .neg 17] := by
  change (B 2=true) → (B 3=true) → (B 8=true) → (B 14=true) → (B 17=true) → False
  intro h2 h3 h8 h14 h17
  apply no ⟨32,?_⟩
  intro j m
  change j∈[2,3,8,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r99 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 7, .neg 8, .neg 9, .neg 15] := by
  change (B 3=true) → (B 7=true) → (B 8=true) → (B 9=true) → (B 15=true) → False
  intro h3 h7 h8 h9 h15
  apply no ⟨33,?_⟩
  intro j m
  change j∈[3,7,8,9,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h15

private theorem r100 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 11, .neg 12, .neg 15] := by
  change (B 3=true) → (B 6=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h3 h6 h11 h12 h15
  apply no ⟨34,?_⟩
  intro j m
  change j∈[3,6,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r101 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 8, .neg 11, .neg 12, .neg 15] := by
  change (B 3=true) → (B 8=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h3 h8 h11 h12 h15
  apply no ⟨35,?_⟩
  intro j m
  change j∈[3,8,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r102 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 7, .neg 11, .neg 12, .neg 15] := by
  change (B 4=true) → (B 7=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h4 h7 h11 h12 h15
  apply no ⟨36,?_⟩
  intro j m
  change j∈[4,7,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

theorem has_template (B : Bit) (M : Model B) : Found B := by
  by_contra no
  exact exclusion (valuation B) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r0 B M)) (fmla_and _ _ _ (fmla_one _ _ (r1 B M)) (fmla_one _ _ (r2 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r3 B M)) (fmla_and _ _ _ (fmla_one _ _ (r4 B M)) (fmla_one _ _ (r5 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r6 B M)) (fmla_and _ _ _ (fmla_one _ _ (r7 B M)) (fmla_one _ _ (r8 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r9 B M)) (fmla_and _ _ _ (fmla_one _ _ (r10 B M)) (fmla_one _ _ (r11 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r12 B M)) (fmla_and _ _ _ (fmla_one _ _ (r13 B M)) (fmla_one _ _ (r14 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r15 B M)) (fmla_and _ _ _ (fmla_one _ _ (r16 B M)) (fmla_one _ _ (r17 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r18 B M)) (fmla_and _ _ _ (fmla_one _ _ (r19 B M)) (fmla_one _ _ (r20 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r21 B M)) (fmla_one _ _ (r22 B M))) (fmla_and _ _ _ (fmla_one _ _ (r23 B M)) (fmla_one _ _ (r24 B M))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r25 B M)) (fmla_and _ _ _ (fmla_one _ _ (r26 B M)) (fmla_one _ _ (r27 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r28 B M)) (fmla_and _ _ _ (fmla_one _ _ (r29 B M)) (fmla_one _ _ (r30 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r31 B M)) (fmla_and _ _ _ (fmla_one _ _ (r32 B M)) (fmla_one _ _ (r33 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r34 B M)) (fmla_one _ _ (r35 B M))) (fmla_and _ _ _ (fmla_one _ _ (r36 B M)) (fmla_one _ _ (r37 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r38 B M)) (fmla_and _ _ _ (fmla_one _ _ (r39 B M)) (fmla_one _ _ (r40 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r41 B M)) (fmla_and _ _ _ (fmla_one _ _ (r42 B M)) (fmla_one _ _ (r43 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r44 B M)) (fmla_and _ _ _ (fmla_one _ _ (r45 B M)) (fmla_one _ _ (r46 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r47 B M)) (fmla_one _ _ (r48 B M))) (fmla_and _ _ _ (fmla_one _ _ (r49 B M)) (fmla_one _ _ (r50 B M)))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r51 B M)) (fmla_and _ _ _ (fmla_one _ _ (r52 B M)) (fmla_one _ _ (r53 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r54 B M)) (fmla_and _ _ _ (fmla_one _ _ (r55 B M)) (fmla_one _ _ (r56 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r57 B M)) (fmla_and _ _ _ (fmla_one _ _ (r58 B M)) (fmla_one _ _ (r59 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r60 B M)) (fmla_one _ _ (r61 B M))) (fmla_and _ _ _ (fmla_one _ _ (r62 B M)) (fmla_one _ _ (r63 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r64 B M)) (fmla_and _ _ _ (fmla_one _ _ (r65 B M)) (fmla_one _ _ (r66 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r67 B no)) (fmla_and _ _ _ (fmla_one _ _ (r68 B no)) (fmla_one _ _ (r69 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r70 B no)) (fmla_and _ _ _ (fmla_one _ _ (r71 B no)) (fmla_one _ _ (r72 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r73 B no)) (fmla_one _ _ (r74 B no))) (fmla_and _ _ _ (fmla_one _ _ (r75 B no)) (fmla_one _ _ (r76 B no))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r77 B no)) (fmla_and _ _ _ (fmla_one _ _ (r78 B no)) (fmla_one _ _ (r79 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r80 B no)) (fmla_and _ _ _ (fmla_one _ _ (r81 B no)) (fmla_one _ _ (r82 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r83 B no)) (fmla_and _ _ _ (fmla_one _ _ (r84 B no)) (fmla_one _ _ (r85 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r86 B no)) (fmla_one _ _ (r87 B no))) (fmla_and _ _ _ (fmla_one _ _ (r88 B no)) (fmla_one _ _ (r89 B no)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r90 B no)) (fmla_and _ _ _ (fmla_one _ _ (r91 B no)) (fmla_one _ _ (r92 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r93 B no)) (fmla_and _ _ _ (fmla_one _ _ (r94 B no)) (fmla_one _ _ (r95 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r96 B no)) (fmla_and _ _ _ (fmla_one _ _ (r97 B no)) (fmla_one _ _ (r98 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r99 B no)) (fmla_one _ _ (r100 B no))) (fmla_and _ _ _ (fmla_one _ _ (r101 B no)) (fmla_one _ _ (r102 B no)))))))))

#print axioms exclusion
#print axioms has_template
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Dense0
