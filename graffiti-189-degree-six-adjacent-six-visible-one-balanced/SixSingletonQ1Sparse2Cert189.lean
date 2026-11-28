import SixSingletonFiveAllLowCert189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Sparse2
open Sat AllLow
set_option maxRecDepth 32768
set_option maxHeartbeats 18000000

packed_rup exclusion
  (include_str "q1-templates/sparse2.cnf")
  (include_str "q1-templates/sparse2.lrat")

abbrev Bit := Nat→Bool
private def valuation (B : Bit) : Sat.Valuation := fun j=>B j=true
structure Model (B : Bit) : Prop where
  row0 : 2≤marks (B 0)+marks (B 1)+marks (B 2)+marks (B 3)+marks (B 4)+marks (B 15)
  row1 : 2≤marks (B 0)+marks (B 5)+marks (B 6)+marks (B 7)+marks (B 8)+marks (B 16)
  row2 : 2≤marks (B 1)+marks (B 5)+marks (B 9)+marks (B 10)+marks (B 11)+marks (B 17)
  row3 : 4≤marks (B 2)+marks (B 6)+marks (B 9)+marks (B 12)+marks (B 13)+marks (B 18)
  row4 : 4≤marks (B 3)+marks (B 7)+marks (B 10)+marks (B 12)+marks (B 14)+marks (B 19)
  row5 : 4≤marks (B 4)+marks (B 8)+marks (B 11)+marks (B 13)+marks (B 14)+marks (B 20)
  bal : 3≤marks (B 15)+marks (B 16)+marks (B 17)+marks (B 18)+marks (B 19)+marks (B 20)

def requirement : Fin 33 → List Nat := ![[2,7,11,14,18],[3,8,9,13,19],[4,6,10,12,20],[6,11,12,14,15],[2,10,13,14,16],[4,7,12,13,17],[8,9,10,14,18],[2,7,8,12,20],[3,6,11,13,19],[4,5,12,13,19],[0,9,12,14,20],[3,7,9,13,20],[3,6,8,14,18],[1,8,12,13,19],[4,6,9,14,19],[0,10,13,14,18],[7,11,12,13,16],[2,8,10,13,19],[3,5,13,14,18],[4,7,10,13,18],[2,9,11,14,19],[1,6,12,14,20],[0,11,12,13,19],[3,6,11,12,20],[3,8,9,12,20],[7,9,13,14,15],[3,6,13,14,17],[1,4,12,14,16],[2,4,10,11,18],[6,8,10,14,18],[0,5,12,14,15],[1,5,12,14,15],[2,8,11,12,16]]
def visit : Fin 33 → List (Fin 10) := ![[9,3,0,6,8,7,1,4,5,2],[9,4,0,6,8,7,1,5,3,2],[9,5,0,6,8,7,1,3,4,2],[9,0,6,8,7,1,3,4,5,2],[9,1,7,8,6,0,3,5,4,2],[9,2,7,8,6,0,5,3,4,1],[9,3,2,4,5,1,7,8,6,0],[9,5,1,4,3,0,6,8,7,2],[9,4,0,6,8,7,1,3,5,2],[9,4,3,5,0,6,8,7,1,2],[9,5,4,3,2,7,8,6,0,1],[9,5,3,2,7,8,6,0,4,1],[9,3,1,5,4,0,6,8,7,2],[9,4,3,5,1,7,8,6,0,2],[9,4,5,0,6,8,7,1,3,2],[9,3,5,4,2,7,8,6,0,1],[9,1,4,3,5,2,7,8,6,0],[9,4,2,7,8,6,0,3,5,1],[9,3,5,4,0,6,8,7,1,2],[9,3,5,0,6,8,7,1,4,2],[9,4,5,2,3,0,6,8,7,1],[9,5,4,3,1,7,8,6,0,2],[9,4,3,5,2,7,8,6,0,1],[9,5,2,7,8,6,0,4,3,1],[9,5,1,7,8,6,0,4,3,2],[9,0,6,8,7,1,4,5,3,2],[9,2,7,8,6,0,4,5,3,1],[9,1,7,8,6,3,4,5,0,2],[9,3,0,5,2,4,6,8,7,1],[9,3,1,5,4,2,7,8,6,0],[9,0,1,2,7,8,6,3,4,5],[9,0,2,1,7,8,6,3,4,5],[9,1,5,2,7,8,6,0,3,4]]
abbrev Found (B : Bit) := ∃ k,∀ j∈requirement k,B j=true
private theorem mark_le_one (a : Bool) : marks a≤1 := by cases a <;> decide
private theorem mark_zero (a : Bool) (h : ¬a=true) : marks a=0 := by cases a <;> simp_all [marks]

private theorem r0 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 2, .pos 3, .pos 4] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 2=true) → (¬ B 3=true) → (¬ B 4=true) → False
  intro h0 h1 h2 h3 h4
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h2, mark_zero _ h3, mark_zero _ h4] at N
  have u15 := mark_le_one (B 15)
  omega

private theorem r1 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 2, .pos 3, .pos 15] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 2=true) → (¬ B 3=true) → (¬ B 15=true) → False
  intro h0 h1 h2 h3 h15
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h2, mark_zero _ h3, mark_zero _ h15] at N
  have u4 := mark_le_one (B 4)
  omega

private theorem r2 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 2, .pos 4, .pos 15] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 2=true) → (¬ B 4=true) → (¬ B 15=true) → False
  intro h0 h1 h2 h4 h15
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h2, mark_zero _ h4, mark_zero _ h15] at N
  have u3 := mark_le_one (B 3)
  omega

private theorem r3 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 3, .pos 4, .pos 15] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 3=true) → (¬ B 4=true) → (¬ B 15=true) → False
  intro h0 h1 h3 h4 h15
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h3, mark_zero _ h4, mark_zero _ h15] at N
  have u2 := mark_le_one (B 2)
  omega

private theorem r4 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 2, .pos 3, .pos 4, .pos 15] := by
  change (¬ B 0=true) → (¬ B 2=true) → (¬ B 3=true) → (¬ B 4=true) → (¬ B 15=true) → False
  intro h0 h2 h3 h4 h15
  have N := M.row0
  rw [mark_zero _ h0, mark_zero _ h2, mark_zero _ h3, mark_zero _ h4, mark_zero _ h15] at N
  have u1 := mark_le_one (B 1)
  omega

private theorem r5 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 2, .pos 3, .pos 4, .pos 15] := by
  change (¬ B 1=true) → (¬ B 2=true) → (¬ B 3=true) → (¬ B 4=true) → (¬ B 15=true) → False
  intro h1 h2 h3 h4 h15
  have N := M.row0
  rw [mark_zero _ h1, mark_zero _ h2, mark_zero _ h3, mark_zero _ h4, mark_zero _ h15] at N
  have u0 := mark_le_one (B 0)
  omega

private theorem r6 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 5, .pos 6, .pos 7, .pos 8] := by
  change (¬ B 0=true) → (¬ B 5=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → False
  intro h0 h5 h6 h7 h8
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h5, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8] at N
  have u16 := mark_le_one (B 16)
  omega

private theorem r7 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 5, .pos 6, .pos 7, .pos 16] := by
  change (¬ B 0=true) → (¬ B 5=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 16=true) → False
  intro h0 h5 h6 h7 h16
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h5, mark_zero _ h6, mark_zero _ h7, mark_zero _ h16] at N
  have u8 := mark_le_one (B 8)
  omega

private theorem r8 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 5, .pos 6, .pos 8, .pos 16] := by
  change (¬ B 0=true) → (¬ B 5=true) → (¬ B 6=true) → (¬ B 8=true) → (¬ B 16=true) → False
  intro h0 h5 h6 h8 h16
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h5, mark_zero _ h6, mark_zero _ h8, mark_zero _ h16] at N
  have u7 := mark_le_one (B 7)
  omega

private theorem r9 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 5, .pos 7, .pos 8, .pos 16] := by
  change (¬ B 0=true) → (¬ B 5=true) → (¬ B 7=true) → (¬ B 8=true) → (¬ B 16=true) → False
  intro h0 h5 h7 h8 h16
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h5, mark_zero _ h7, mark_zero _ h8, mark_zero _ h16] at N
  have u6 := mark_le_one (B 6)
  omega

private theorem r10 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 0, .pos 6, .pos 7, .pos 8, .pos 16] := by
  change (¬ B 0=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → (¬ B 16=true) → False
  intro h0 h6 h7 h8 h16
  have N := M.row1
  rw [mark_zero _ h0, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8, mark_zero _ h16] at N
  have u5 := mark_le_one (B 5)
  omega

private theorem r11 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 5, .pos 6, .pos 7, .pos 8, .pos 16] := by
  change (¬ B 5=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → (¬ B 16=true) → False
  intro h5 h6 h7 h8 h16
  have N := M.row1
  rw [mark_zero _ h5, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8, mark_zero _ h16] at N
  have u0 := mark_le_one (B 0)
  omega

private theorem r12 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 5, .pos 9, .pos 10, .pos 11] := by
  change (¬ B 1=true) → (¬ B 5=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → False
  intro h1 h5 h9 h10 h11
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h5, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11] at N
  have u17 := mark_le_one (B 17)
  omega

private theorem r13 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 5, .pos 9, .pos 10, .pos 17] := by
  change (¬ B 1=true) → (¬ B 5=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 17=true) → False
  intro h1 h5 h9 h10 h17
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h5, mark_zero _ h9, mark_zero _ h10, mark_zero _ h17] at N
  have u11 := mark_le_one (B 11)
  omega

private theorem r14 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 5, .pos 9, .pos 11, .pos 17] := by
  change (¬ B 1=true) → (¬ B 5=true) → (¬ B 9=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h1 h5 h9 h11 h17
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h5, mark_zero _ h9, mark_zero _ h11, mark_zero _ h17] at N
  have u10 := mark_le_one (B 10)
  omega

private theorem r15 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 5, .pos 10, .pos 11, .pos 17] := by
  change (¬ B 1=true) → (¬ B 5=true) → (¬ B 10=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h1 h5 h10 h11 h17
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h5, mark_zero _ h10, mark_zero _ h11, mark_zero _ h17] at N
  have u9 := mark_le_one (B 9)
  omega

private theorem r16 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 1, .pos 9, .pos 10, .pos 11, .pos 17] := by
  change (¬ B 1=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h1 h9 h10 h11 h17
  have N := M.row2
  rw [mark_zero _ h1, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11, mark_zero _ h17] at N
  have u5 := mark_le_one (B 5)
  omega

private theorem r17 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 5, .pos 9, .pos 10, .pos 11, .pos 17] := by
  change (¬ B 5=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h5 h9 h10 h11 h17
  have N := M.row2
  rw [mark_zero _ h5, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11, mark_zero _ h17] at N
  have u1 := mark_le_one (B 1)
  omega

private theorem r18 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 9] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 9=true) → False
  intro h2 h6 h9
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h9] at N
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  have u18 := mark_le_one (B 18)
  omega

private theorem r19 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 12] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 12=true) → False
  intro h2 h6 h12
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h12] at N
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  have u18 := mark_le_one (B 18)
  omega

private theorem r20 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 13] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 13=true) → False
  intro h2 h6 h13
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h13] at N
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  have u18 := mark_le_one (B 18)
  omega

private theorem r21 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 18] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 18=true) → False
  intro h2 h6 h18
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h18] at N
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r22 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 9, .pos 12] := by
  change (¬ B 2=true) → (¬ B 9=true) → (¬ B 12=true) → False
  intro h2 h9 h12
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h9, mark_zero _ h12] at N
  have u6 := mark_le_one (B 6)
  have u13 := mark_le_one (B 13)
  have u18 := mark_le_one (B 18)
  omega

private theorem r23 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 9, .pos 13] := by
  change (¬ B 2=true) → (¬ B 9=true) → (¬ B 13=true) → False
  intro h2 h9 h13
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h9, mark_zero _ h13] at N
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  have u18 := mark_le_one (B 18)
  omega

private theorem r24 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 9, .pos 18] := by
  change (¬ B 2=true) → (¬ B 9=true) → (¬ B 18=true) → False
  intro h2 h9 h18
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h9, mark_zero _ h18] at N
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r25 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 12, .pos 13] := by
  change (¬ B 2=true) → (¬ B 12=true) → (¬ B 13=true) → False
  intro h2 h12 h13
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h12, mark_zero _ h13] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u18 := mark_le_one (B 18)
  omega

private theorem r26 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 12, .pos 18] := by
  change (¬ B 2=true) → (¬ B 12=true) → (¬ B 18=true) → False
  intro h2 h12 h18
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h12, mark_zero _ h18] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  omega

private theorem r27 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 2, .pos 13, .pos 18] := by
  change (¬ B 2=true) → (¬ B 13=true) → (¬ B 18=true) → False
  intro h2 h13 h18
  have N := M.row3
  rw [mark_zero _ h2, mark_zero _ h13, mark_zero _ h18] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  omega

private theorem r28 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 9, .pos 12] := by
  change (¬ B 6=true) → (¬ B 9=true) → (¬ B 12=true) → False
  intro h6 h9 h12
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h9, mark_zero _ h12] at N
  have u2 := mark_le_one (B 2)
  have u13 := mark_le_one (B 13)
  have u18 := mark_le_one (B 18)
  omega

private theorem r29 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 9, .pos 13] := by
  change (¬ B 6=true) → (¬ B 9=true) → (¬ B 13=true) → False
  intro h6 h9 h13
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h9, mark_zero _ h13] at N
  have u2 := mark_le_one (B 2)
  have u12 := mark_le_one (B 12)
  have u18 := mark_le_one (B 18)
  omega

private theorem r30 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 9, .pos 18] := by
  change (¬ B 6=true) → (¬ B 9=true) → (¬ B 18=true) → False
  intro h6 h9 h18
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h9, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r31 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 12, .pos 13] := by
  change (¬ B 6=true) → (¬ B 12=true) → (¬ B 13=true) → False
  intro h6 h12 h13
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h12, mark_zero _ h13] at N
  have u2 := mark_le_one (B 2)
  have u9 := mark_le_one (B 9)
  have u18 := mark_le_one (B 18)
  omega

private theorem r32 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 12, .pos 18] := by
  change (¬ B 6=true) → (¬ B 12=true) → (¬ B 18=true) → False
  intro h6 h12 h18
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h12, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  omega

private theorem r33 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 6, .pos 13, .pos 18] := by
  change (¬ B 6=true) → (¬ B 13=true) → (¬ B 18=true) → False
  intro h6 h13 h18
  have N := M.row3
  rw [mark_zero _ h6, mark_zero _ h13, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  omega

private theorem r34 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 9, .pos 12, .pos 13] := by
  change (¬ B 9=true) → (¬ B 12=true) → (¬ B 13=true) → False
  intro h9 h12 h13
  have N := M.row3
  rw [mark_zero _ h9, mark_zero _ h12, mark_zero _ h13] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u18 := mark_le_one (B 18)
  omega

private theorem r35 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 9, .pos 12, .pos 18] := by
  change (¬ B 9=true) → (¬ B 12=true) → (¬ B 18=true) → False
  intro h9 h12 h18
  have N := M.row3
  rw [mark_zero _ h9, mark_zero _ h12, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u13 := mark_le_one (B 13)
  omega

private theorem r36 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 9, .pos 13, .pos 18] := by
  change (¬ B 9=true) → (¬ B 13=true) → (¬ B 18=true) → False
  intro h9 h13 h18
  have N := M.row3
  rw [mark_zero _ h9, mark_zero _ h13, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  omega

private theorem r37 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 12, .pos 13, .pos 18] := by
  change (¬ B 12=true) → (¬ B 13=true) → (¬ B 18=true) → False
  intro h12 h13 h18
  have N := M.row3
  rw [mark_zero _ h12, mark_zero _ h13, mark_zero _ h18] at N
  have u2 := mark_le_one (B 2)
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  omega

private theorem r38 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 10] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 10=true) → False
  intro h3 h7 h10
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h10] at N
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  have u19 := mark_le_one (B 19)
  omega

private theorem r39 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 12] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 12=true) → False
  intro h3 h7 h12
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h12] at N
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  have u19 := mark_le_one (B 19)
  omega

private theorem r40 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 14] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 14=true) → False
  intro h3 h7 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h14] at N
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  have u19 := mark_le_one (B 19)
  omega

private theorem r41 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 7, .pos 19] := by
  change (¬ B 3=true) → (¬ B 7=true) → (¬ B 19=true) → False
  intro h3 h7 h19
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h7, mark_zero _ h19] at N
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r42 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 10, .pos 12] := by
  change (¬ B 3=true) → (¬ B 10=true) → (¬ B 12=true) → False
  intro h3 h10 h12
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h10, mark_zero _ h12] at N
  have u7 := mark_le_one (B 7)
  have u14 := mark_le_one (B 14)
  have u19 := mark_le_one (B 19)
  omega

private theorem r43 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 10, .pos 14] := by
  change (¬ B 3=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h3 h10 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h10, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  have u19 := mark_le_one (B 19)
  omega

private theorem r44 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 10, .pos 19] := by
  change (¬ B 3=true) → (¬ B 10=true) → (¬ B 19=true) → False
  intro h3 h10 h19
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h10, mark_zero _ h19] at N
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r45 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 12, .pos 14] := by
  change (¬ B 3=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h3 h12 h14
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h12, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  have u19 := mark_le_one (B 19)
  omega

private theorem r46 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 12, .pos 19] := by
  change (¬ B 3=true) → (¬ B 12=true) → (¬ B 19=true) → False
  intro h3 h12 h19
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h12, mark_zero _ h19] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r47 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 3, .pos 14, .pos 19] := by
  change (¬ B 3=true) → (¬ B 14=true) → (¬ B 19=true) → False
  intro h3 h14 h19
  have N := M.row4
  rw [mark_zero _ h3, mark_zero _ h14, mark_zero _ h19] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  omega

private theorem r48 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 12] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 12=true) → False
  intro h7 h10 h12
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u14 := mark_le_one (B 14)
  have u19 := mark_le_one (B 19)
  omega

private theorem r49 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 14] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h7 h10 h14
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u12 := mark_le_one (B 12)
  have u19 := mark_le_one (B 19)
  omega

private theorem r50 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 19] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 19=true) → False
  intro h7 h10 h19
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u12 := mark_le_one (B 12)
  have u14 := mark_le_one (B 14)
  omega

private theorem r51 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 12, .pos 14] := by
  change (¬ B 7=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h7 h12 h14
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h12, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  have u19 := mark_le_one (B 19)
  omega

private theorem r52 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 12, .pos 19] := by
  change (¬ B 7=true) → (¬ B 12=true) → (¬ B 19=true) → False
  intro h7 h12 h19
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h12, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r53 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 7, .pos 14, .pos 19] := by
  change (¬ B 7=true) → (¬ B 14=true) → (¬ B 19=true) → False
  intro h7 h14 h19
  have N := M.row4
  rw [mark_zero _ h7, mark_zero _ h14, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u10 := mark_le_one (B 10)
  have u12 := mark_le_one (B 12)
  omega

private theorem r54 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 10, .pos 12, .pos 14] := by
  change (¬ B 10=true) → (¬ B 12=true) → (¬ B 14=true) → False
  intro h10 h12 h14
  have N := M.row4
  rw [mark_zero _ h10, mark_zero _ h12, mark_zero _ h14] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u19 := mark_le_one (B 19)
  omega

private theorem r55 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 10, .pos 12, .pos 19] := by
  change (¬ B 10=true) → (¬ B 12=true) → (¬ B 19=true) → False
  intro h10 h12 h19
  have N := M.row4
  rw [mark_zero _ h10, mark_zero _ h12, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u14 := mark_le_one (B 14)
  omega

private theorem r56 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 10, .pos 14, .pos 19] := by
  change (¬ B 10=true) → (¬ B 14=true) → (¬ B 19=true) → False
  intro h10 h14 h19
  have N := M.row4
  rw [mark_zero _ h10, mark_zero _ h14, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u12 := mark_le_one (B 12)
  omega

private theorem r57 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 12, .pos 14, .pos 19] := by
  change (¬ B 12=true) → (¬ B 14=true) → (¬ B 19=true) → False
  intro h12 h14 h19
  have N := M.row4
  rw [mark_zero _ h12, mark_zero _ h14, mark_zero _ h19] at N
  have u3 := mark_le_one (B 3)
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  omega

private theorem r58 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 11] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 11=true) → False
  intro h4 h8 h11
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h11] at N
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  have u20 := mark_le_one (B 20)
  omega

private theorem r59 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 13] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 13=true) → False
  intro h4 h8 h13
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h13] at N
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  have u20 := mark_le_one (B 20)
  omega

private theorem r60 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 14] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 14=true) → False
  intro h4 h8 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h14] at N
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  have u20 := mark_le_one (B 20)
  omega

private theorem r61 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 8, .pos 20] := by
  change (¬ B 4=true) → (¬ B 8=true) → (¬ B 20=true) → False
  intro h4 h8 h20
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h8, mark_zero _ h20] at N
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r62 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 11, .pos 13] := by
  change (¬ B 4=true) → (¬ B 11=true) → (¬ B 13=true) → False
  intro h4 h11 h13
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h11, mark_zero _ h13] at N
  have u8 := mark_le_one (B 8)
  have u14 := mark_le_one (B 14)
  have u20 := mark_le_one (B 20)
  omega

private theorem r63 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 11, .pos 14] := by
  change (¬ B 4=true) → (¬ B 11=true) → (¬ B 14=true) → False
  intro h4 h11 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h11, mark_zero _ h14] at N
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  have u20 := mark_le_one (B 20)
  omega

private theorem r64 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 11, .pos 20] := by
  change (¬ B 4=true) → (¬ B 11=true) → (¬ B 20=true) → False
  intro h4 h11 h20
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h11, mark_zero _ h20] at N
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r65 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 13, .pos 14] := by
  change (¬ B 4=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h4 h13 h14
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h13, mark_zero _ h14] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  have u20 := mark_le_one (B 20)
  omega

private theorem r66 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 13, .pos 20] := by
  change (¬ B 4=true) → (¬ B 13=true) → (¬ B 20=true) → False
  intro h4 h13 h20
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h13, mark_zero _ h20] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  omega

private theorem r67 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 4, .pos 14, .pos 20] := by
  change (¬ B 4=true) → (¬ B 14=true) → (¬ B 20=true) → False
  intro h4 h14 h20
  have N := M.row5
  rw [mark_zero _ h4, mark_zero _ h14, mark_zero _ h20] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  omega

private theorem r68 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 13] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 13=true) → False
  intro h8 h11 h13
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h13] at N
  have u4 := mark_le_one (B 4)
  have u14 := mark_le_one (B 14)
  have u20 := mark_le_one (B 20)
  omega

private theorem r69 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 14] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 14=true) → False
  intro h8 h11 h14
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u13 := mark_le_one (B 13)
  have u20 := mark_le_one (B 20)
  omega

private theorem r70 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 20] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 20=true) → False
  intro h8 h11 h20
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u13 := mark_le_one (B 13)
  have u14 := mark_le_one (B 14)
  omega

private theorem r71 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 13, .pos 14] := by
  change (¬ B 8=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h8 h13 h14
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h13, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  have u20 := mark_le_one (B 20)
  omega

private theorem r72 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 13, .pos 20] := by
  change (¬ B 8=true) → (¬ B 13=true) → (¬ B 20=true) → False
  intro h8 h13 h20
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h13, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  have u14 := mark_le_one (B 14)
  omega

private theorem r73 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 8, .pos 14, .pos 20] := by
  change (¬ B 8=true) → (¬ B 14=true) → (¬ B 20=true) → False
  intro h8 h14 h20
  have N := M.row5
  rw [mark_zero _ h8, mark_zero _ h14, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u11 := mark_le_one (B 11)
  have u13 := mark_le_one (B 13)
  omega

private theorem r74 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 11, .pos 13, .pos 14] := by
  change (¬ B 11=true) → (¬ B 13=true) → (¬ B 14=true) → False
  intro h11 h13 h14
  have N := M.row5
  rw [mark_zero _ h11, mark_zero _ h13, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u20 := mark_le_one (B 20)
  omega

private theorem r75 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 11, .pos 13, .pos 20] := by
  change (¬ B 11=true) → (¬ B 13=true) → (¬ B 20=true) → False
  intro h11 h13 h20
  have N := M.row5
  rw [mark_zero _ h11, mark_zero _ h13, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u14 := mark_le_one (B 14)
  omega

private theorem r76 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 11, .pos 14, .pos 20] := by
  change (¬ B 11=true) → (¬ B 14=true) → (¬ B 20=true) → False
  intro h11 h14 h20
  have N := M.row5
  rw [mark_zero _ h11, mark_zero _ h14, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u13 := mark_le_one (B 13)
  omega

private theorem r77 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 13, .pos 14, .pos 20] := by
  change (¬ B 13=true) → (¬ B 14=true) → (¬ B 20=true) → False
  intro h13 h14 h20
  have N := M.row5
  rw [mark_zero _ h13, mark_zero _ h14, mark_zero _ h20] at N
  have u4 := mark_le_one (B 4)
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  omega

private theorem r78 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 17, .pos 18] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 17=true) → (¬ B 18=true) → False
  intro h15 h16 h17 h18
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h17, mark_zero _ h18] at N
  have u19 := mark_le_one (B 19)
  have u20 := mark_le_one (B 20)
  omega

private theorem r79 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 17, .pos 19] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 17=true) → (¬ B 19=true) → False
  intro h15 h16 h17 h19
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h17, mark_zero _ h19] at N
  have u18 := mark_le_one (B 18)
  have u20 := mark_le_one (B 20)
  omega

private theorem r80 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 17, .pos 20] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 17=true) → (¬ B 20=true) → False
  intro h15 h16 h17 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h17, mark_zero _ h20] at N
  have u18 := mark_le_one (B 18)
  have u19 := mark_le_one (B 19)
  omega

private theorem r81 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 18, .pos 19] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 18=true) → (¬ B 19=true) → False
  intro h15 h16 h18 h19
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h18, mark_zero _ h19] at N
  have u17 := mark_le_one (B 17)
  have u20 := mark_le_one (B 20)
  omega

private theorem r82 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 18, .pos 20] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 18=true) → (¬ B 20=true) → False
  intro h15 h16 h18 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h18, mark_zero _ h20] at N
  have u17 := mark_le_one (B 17)
  have u19 := mark_le_one (B 19)
  omega

private theorem r83 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 16, .pos 19, .pos 20] := by
  change (¬ B 15=true) → (¬ B 16=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h15 h16 h19 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h16, mark_zero _ h19, mark_zero _ h20] at N
  have u17 := mark_le_one (B 17)
  have u18 := mark_le_one (B 18)
  omega

private theorem r84 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 17, .pos 18, .pos 19] := by
  change (¬ B 15=true) → (¬ B 17=true) → (¬ B 18=true) → (¬ B 19=true) → False
  intro h15 h17 h18 h19
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h17, mark_zero _ h18, mark_zero _ h19] at N
  have u16 := mark_le_one (B 16)
  have u20 := mark_le_one (B 20)
  omega

private theorem r85 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 17, .pos 18, .pos 20] := by
  change (¬ B 15=true) → (¬ B 17=true) → (¬ B 18=true) → (¬ B 20=true) → False
  intro h15 h17 h18 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h17, mark_zero _ h18, mark_zero _ h20] at N
  have u16 := mark_le_one (B 16)
  have u19 := mark_le_one (B 19)
  omega

private theorem r86 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 17, .pos 19, .pos 20] := by
  change (¬ B 15=true) → (¬ B 17=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h15 h17 h19 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h17, mark_zero _ h19, mark_zero _ h20] at N
  have u16 := mark_le_one (B 16)
  have u18 := mark_le_one (B 18)
  omega

private theorem r87 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 15, .pos 18, .pos 19, .pos 20] := by
  change (¬ B 15=true) → (¬ B 18=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h15 h18 h19 h20
  have N := M.bal
  rw [mark_zero _ h15, mark_zero _ h18, mark_zero _ h19, mark_zero _ h20] at N
  have u16 := mark_le_one (B 16)
  have u17 := mark_le_one (B 17)
  omega

private theorem r88 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 17, .pos 18, .pos 19] := by
  change (¬ B 16=true) → (¬ B 17=true) → (¬ B 18=true) → (¬ B 19=true) → False
  intro h16 h17 h18 h19
  have N := M.bal
  rw [mark_zero _ h16, mark_zero _ h17, mark_zero _ h18, mark_zero _ h19] at N
  have u15 := mark_le_one (B 15)
  have u20 := mark_le_one (B 20)
  omega

private theorem r89 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 17, .pos 18, .pos 20] := by
  change (¬ B 16=true) → (¬ B 17=true) → (¬ B 18=true) → (¬ B 20=true) → False
  intro h16 h17 h18 h20
  have N := M.bal
  rw [mark_zero _ h16, mark_zero _ h17, mark_zero _ h18, mark_zero _ h20] at N
  have u15 := mark_le_one (B 15)
  have u19 := mark_le_one (B 19)
  omega

private theorem r90 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 17, .pos 19, .pos 20] := by
  change (¬ B 16=true) → (¬ B 17=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h16 h17 h19 h20
  have N := M.bal
  rw [mark_zero _ h16, mark_zero _ h17, mark_zero _ h19, mark_zero _ h20] at N
  have u15 := mark_le_one (B 15)
  have u18 := mark_le_one (B 18)
  omega

private theorem r91 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 16, .pos 18, .pos 19, .pos 20] := by
  change (¬ B 16=true) → (¬ B 18=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h16 h18 h19 h20
  have N := M.bal
  rw [mark_zero _ h16, mark_zero _ h18, mark_zero _ h19, mark_zero _ h20] at N
  have u15 := mark_le_one (B 15)
  have u17 := mark_le_one (B 17)
  omega

private theorem r92 (B : Bit) (M : Model B) : (valuation B).satisfies [.pos 17, .pos 18, .pos 19, .pos 20] := by
  change (¬ B 17=true) → (¬ B 18=true) → (¬ B 19=true) → (¬ B 20=true) → False
  intro h17 h18 h19 h20
  have N := M.bal
  rw [mark_zero _ h17, mark_zero _ h18, mark_zero _ h19, mark_zero _ h20] at N
  have u15 := mark_le_one (B 15)
  have u16 := mark_le_one (B 16)
  omega

private theorem r93 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 7, .neg 11, .neg 14, .neg 18] := by
  change (B 2=true) → (B 7=true) → (B 11=true) → (B 14=true) → (B 18=true) → False
  intro h2 h7 h11 h14 h18
  apply no ⟨0,?_⟩
  intro j m
  change j∈[2,7,11,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r94 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 8, .neg 9, .neg 13, .neg 19] := by
  change (B 3=true) → (B 8=true) → (B 9=true) → (B 13=true) → (B 19=true) → False
  intro h3 h8 h9 h13 h19
  apply no ⟨1,?_⟩
  intro j m
  change j∈[3,8,9,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r95 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 6, .neg 10, .neg 12, .neg 20] := by
  change (B 4=true) → (B 6=true) → (B 10=true) → (B 12=true) → (B 20=true) → False
  intro h4 h6 h10 h12 h20
  apply no ⟨2,?_⟩
  intro j m
  change j∈[4,6,10,12,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h20

private theorem r96 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 6, .neg 11, .neg 12, .neg 14, .neg 15] := by
  change (B 6=true) → (B 11=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h6 h11 h12 h14 h15
  apply no ⟨3,?_⟩
  intro j m
  change j∈[6,11,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h6
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r97 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 10, .neg 13, .neg 14, .neg 16] := by
  change (B 2=true) → (B 10=true) → (B 13=true) → (B 14=true) → (B 16=true) → False
  intro h2 h10 h13 h14 h16
  apply no ⟨4,?_⟩
  intro j m
  change j∈[2,10,13,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r98 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 7, .neg 12, .neg 13, .neg 17] := by
  change (B 4=true) → (B 7=true) → (B 12=true) → (B 13=true) → (B 17=true) → False
  intro h4 h7 h12 h13 h17
  apply no ⟨5,?_⟩
  intro j m
  change j∈[4,7,12,13,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h17

private theorem r99 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 8, .neg 9, .neg 10, .neg 14, .neg 18] := by
  change (B 8=true) → (B 9=true) → (B 10=true) → (B 14=true) → (B 18=true) → False
  intro h8 h9 h10 h14 h18
  apply no ⟨6,?_⟩
  intro j m
  change j∈[8,9,10,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r100 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 7, .neg 8, .neg 12, .neg 20] := by
  change (B 2=true) → (B 7=true) → (B 8=true) → (B 12=true) → (B 20=true) → False
  intro h2 h7 h8 h12 h20
  apply no ⟨7,?_⟩
  intro j m
  change j∈[2,7,8,12,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h20

private theorem r101 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 11, .neg 13, .neg 19] := by
  change (B 3=true) → (B 6=true) → (B 11=true) → (B 13=true) → (B 19=true) → False
  intro h3 h6 h11 h13 h19
  apply no ⟨8,?_⟩
  intro j m
  change j∈[3,6,11,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r102 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 5, .neg 12, .neg 13, .neg 19] := by
  change (B 4=true) → (B 5=true) → (B 12=true) → (B 13=true) → (B 19=true) → False
  intro h4 h5 h12 h13 h19
  apply no ⟨9,?_⟩
  intro j m
  change j∈[4,5,12,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h5
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r103 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 9, .neg 12, .neg 14, .neg 20] := by
  change (B 0=true) → (B 9=true) → (B 12=true) → (B 14=true) → (B 20=true) → False
  intro h0 h9 h12 h14 h20
  apply no ⟨10,?_⟩
  intro j m
  change j∈[0,9,12,14,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h9
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h20

private theorem r104 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 7, .neg 9, .neg 13, .neg 20] := by
  change (B 3=true) → (B 7=true) → (B 9=true) → (B 13=true) → (B 20=true) → False
  intro h3 h7 h9 h13 h20
  apply no ⟨11,?_⟩
  intro j m
  change j∈[3,7,9,13,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h20

private theorem r105 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 8, .neg 14, .neg 18] := by
  change (B 3=true) → (B 6=true) → (B 8=true) → (B 14=true) → (B 18=true) → False
  intro h3 h6 h8 h14 h18
  apply no ⟨12,?_⟩
  intro j m
  change j∈[3,6,8,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h8
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r106 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 8, .neg 12, .neg 13, .neg 19] := by
  change (B 1=true) → (B 8=true) → (B 12=true) → (B 13=true) → (B 19=true) → False
  intro h1 h8 h12 h13 h19
  apply no ⟨13,?_⟩
  intro j m
  change j∈[1,8,12,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r107 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 6, .neg 9, .neg 14, .neg 19] := by
  change (B 4=true) → (B 6=true) → (B 9=true) → (B 14=true) → (B 19=true) → False
  intro h4 h6 h9 h14 h19
  apply no ⟨14,?_⟩
  intro j m
  change j∈[4,6,9,14,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h9
  · exact m.symm ▸ h14
  · exact m.symm ▸ h19

private theorem r108 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 10, .neg 13, .neg 14, .neg 18] := by
  change (B 0=true) → (B 10=true) → (B 13=true) → (B 14=true) → (B 18=true) → False
  intro h0 h10 h13 h14 h18
  apply no ⟨15,?_⟩
  intro j m
  change j∈[0,10,13,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r109 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 11, .neg 12, .neg 13, .neg 16] := by
  change (B 7=true) → (B 11=true) → (B 12=true) → (B 13=true) → (B 16=true) → False
  intro h7 h11 h12 h13 h16
  apply no ⟨16,?_⟩
  intro j m
  change j∈[7,11,12,13,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h16

private theorem r110 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 8, .neg 10, .neg 13, .neg 19] := by
  change (B 2=true) → (B 8=true) → (B 10=true) → (B 13=true) → (B 19=true) → False
  intro h2 h8 h10 h13 h19
  apply no ⟨17,?_⟩
  intro j m
  change j∈[2,8,10,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r111 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 5, .neg 13, .neg 14, .neg 18] := by
  change (B 3=true) → (B 5=true) → (B 13=true) → (B 14=true) → (B 18=true) → False
  intro h3 h5 h13 h14 h18
  apply no ⟨18,?_⟩
  intro j m
  change j∈[3,5,13,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h5
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r112 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 4, .neg 7, .neg 10, .neg 13, .neg 18] := by
  change (B 4=true) → (B 7=true) → (B 10=true) → (B 13=true) → (B 18=true) → False
  intro h4 h7 h10 h13 h18
  apply no ⟨19,?_⟩
  intro j m
  change j∈[4,7,10,13,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h18

private theorem r113 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 9, .neg 11, .neg 14, .neg 19] := by
  change (B 2=true) → (B 9=true) → (B 11=true) → (B 14=true) → (B 19=true) → False
  intro h2 h9 h11 h14 h19
  apply no ⟨20,?_⟩
  intro j m
  change j∈[2,9,11,14,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h9
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h19

private theorem r114 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 6, .neg 12, .neg 14, .neg 20] := by
  change (B 1=true) → (B 6=true) → (B 12=true) → (B 14=true) → (B 20=true) → False
  intro h1 h6 h12 h14 h20
  apply no ⟨21,?_⟩
  intro j m
  change j∈[1,6,12,14,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h6
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h20

private theorem r115 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 11, .neg 12, .neg 13, .neg 19] := by
  change (B 0=true) → (B 11=true) → (B 12=true) → (B 13=true) → (B 19=true) → False
  intro h0 h11 h12 h13 h19
  apply no ⟨22,?_⟩
  intro j m
  change j∈[0,11,12,13,19] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h19

private theorem r116 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 11, .neg 12, .neg 20] := by
  change (B 3=true) → (B 6=true) → (B 11=true) → (B 12=true) → (B 20=true) → False
  intro h3 h6 h11 h12 h20
  apply no ⟨23,?_⟩
  intro j m
  change j∈[3,6,11,12,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h20

private theorem r117 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 8, .neg 9, .neg 12, .neg 20] := by
  change (B 3=true) → (B 8=true) → (B 9=true) → (B 12=true) → (B 20=true) → False
  intro h3 h8 h9 h12 h20
  apply no ⟨24,?_⟩
  intro j m
  change j∈[3,8,9,12,20] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h12
  · exact m.symm ▸ h20

private theorem r118 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 7, .neg 9, .neg 13, .neg 14, .neg 15] := by
  change (B 7=true) → (B 9=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h7 h9 h13 h14 h15
  apply no ⟨25,?_⟩
  intro j m
  change j∈[7,9,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r119 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 3, .neg 6, .neg 13, .neg 14, .neg 17] := by
  change (B 3=true) → (B 6=true) → (B 13=true) → (B 14=true) → (B 17=true) → False
  intro h3 h6 h13 h14 h17
  apply no ⟨26,?_⟩
  intro j m
  change j∈[3,6,13,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r120 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 12, .neg 14, .neg 16] := by
  change (B 1=true) → (B 4=true) → (B 12=true) → (B 14=true) → (B 16=true) → False
  intro h1 h4 h12 h14 h16
  apply no ⟨27,?_⟩
  intro j m
  change j∈[1,4,12,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r121 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 10, .neg 11, .neg 18] := by
  change (B 2=true) → (B 4=true) → (B 10=true) → (B 11=true) → (B 18=true) → False
  intro h2 h4 h10 h11 h18
  apply no ⟨28,?_⟩
  intro j m
  change j∈[2,4,10,11,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h18

private theorem r122 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 6, .neg 8, .neg 10, .neg 14, .neg 18] := by
  change (B 6=true) → (B 8=true) → (B 10=true) → (B 14=true) → (B 18=true) → False
  intro h6 h8 h10 h14 h18
  apply no ⟨29,?_⟩
  intro j m
  change j∈[6,8,10,14,18] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h6
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h18

private theorem r123 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 5, .neg 12, .neg 14, .neg 15] := by
  change (B 0=true) → (B 5=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h0 h5 h12 h14 h15
  apply no ⟨30,?_⟩
  intro j m
  change j∈[0,5,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h5
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r124 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 12, .neg 14, .neg 15] := by
  change (B 1=true) → (B 5=true) → (B 12=true) → (B 14=true) → (B 15=true) → False
  intro h1 h5 h12 h14 h15
  apply no ⟨31,?_⟩
  intro j m
  change j∈[1,5,12,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r125 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 8, .neg 11, .neg 12, .neg 16] := by
  change (B 2=true) → (B 8=true) → (B 11=true) → (B 12=true) → (B 16=true) → False
  intro h2 h8 h11 h12 h16
  apply no ⟨32,?_⟩
  intro j m
  change j∈[2,8,11,12,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h8
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h16

theorem has_template (B : Bit) (M : Model B) : Found B := by
  by_contra no
  exact exclusion (valuation B) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r0 B M)) (fmla_and _ _ _ (fmla_one _ _ (r1 B M)) (fmla_one _ _ (r2 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r3 B M)) (fmla_one _ _ (r4 B M))) (fmla_and _ _ _ (fmla_one _ _ (r5 B M)) (fmla_one _ _ (r6 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r7 B M)) (fmla_one _ _ (r8 B M))) (fmla_and _ _ _ (fmla_one _ _ (r9 B M)) (fmla_one _ _ (r10 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r11 B M)) (fmla_one _ _ (r12 B M))) (fmla_and _ _ _ (fmla_one _ _ (r13 B M)) (fmla_one _ _ (r14 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r15 B M)) (fmla_one _ _ (r16 B M))) (fmla_and _ _ _ (fmla_one _ _ (r17 B M)) (fmla_one _ _ (r18 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r19 B M)) (fmla_one _ _ (r20 B M))) (fmla_and _ _ _ (fmla_one _ _ (r21 B M)) (fmla_one _ _ (r22 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r23 B M)) (fmla_one _ _ (r24 B M))) (fmla_and _ _ _ (fmla_one _ _ (r25 B M)) (fmla_one _ _ (r26 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r27 B M)) (fmla_one _ _ (r28 B M))) (fmla_and _ _ _ (fmla_one _ _ (r29 B M)) (fmla_one _ _ (r30 B M))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r31 B M)) (fmla_one _ _ (r32 B M))) (fmla_and _ _ _ (fmla_one _ _ (r33 B M)) (fmla_one _ _ (r34 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r35 B M)) (fmla_one _ _ (r36 B M))) (fmla_and _ _ _ (fmla_one _ _ (r37 B M)) (fmla_one _ _ (r38 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r39 B M)) (fmla_one _ _ (r40 B M))) (fmla_and _ _ _ (fmla_one _ _ (r41 B M)) (fmla_one _ _ (r42 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r43 B M)) (fmla_one _ _ (r44 B M))) (fmla_and _ _ _ (fmla_one _ _ (r45 B M)) (fmla_one _ _ (r46 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r47 B M)) (fmla_one _ _ (r48 B M))) (fmla_and _ _ _ (fmla_one _ _ (r49 B M)) (fmla_one _ _ (r50 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r51 B M)) (fmla_one _ _ (r52 B M))) (fmla_and _ _ _ (fmla_one _ _ (r53 B M)) (fmla_one _ _ (r54 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r55 B M)) (fmla_one _ _ (r56 B M))) (fmla_and _ _ _ (fmla_one _ _ (r57 B M)) (fmla_one _ _ (r58 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r59 B M)) (fmla_one _ _ (r60 B M))) (fmla_and _ _ _ (fmla_one _ _ (r61 B M)) (fmla_one _ _ (r62 B M)))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r63 B M)) (fmla_and _ _ _ (fmla_one _ _ (r64 B M)) (fmla_one _ _ (r65 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r66 B M)) (fmla_one _ _ (r67 B M))) (fmla_and _ _ _ (fmla_one _ _ (r68 B M)) (fmla_one _ _ (r69 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r70 B M)) (fmla_one _ _ (r71 B M))) (fmla_and _ _ _ (fmla_one _ _ (r72 B M)) (fmla_one _ _ (r73 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r74 B M)) (fmla_one _ _ (r75 B M))) (fmla_and _ _ _ (fmla_one _ _ (r76 B M)) (fmla_one _ _ (r77 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r78 B M)) (fmla_one _ _ (r79 B M))) (fmla_and _ _ _ (fmla_one _ _ (r80 B M)) (fmla_one _ _ (r81 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r82 B M)) (fmla_one _ _ (r83 B M))) (fmla_and _ _ _ (fmla_one _ _ (r84 B M)) (fmla_one _ _ (r85 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r86 B M)) (fmla_one _ _ (r87 B M))) (fmla_and _ _ _ (fmla_one _ _ (r88 B M)) (fmla_one _ _ (r89 B M)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r90 B M)) (fmla_one _ _ (r91 B M))) (fmla_and _ _ _ (fmla_one _ _ (r92 B M)) (fmla_one _ _ (r93 B no))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r94 B no)) (fmla_one _ _ (r95 B no))) (fmla_and _ _ _ (fmla_one _ _ (r96 B no)) (fmla_one _ _ (r97 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r98 B no)) (fmla_one _ _ (r99 B no))) (fmla_and _ _ _ (fmla_one _ _ (r100 B no)) (fmla_one _ _ (r101 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r102 B no)) (fmla_one _ _ (r103 B no))) (fmla_and _ _ _ (fmla_one _ _ (r104 B no)) (fmla_one _ _ (r105 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r106 B no)) (fmla_one _ _ (r107 B no))) (fmla_and _ _ _ (fmla_one _ _ (r108 B no)) (fmla_one _ _ (r109 B no)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r110 B no)) (fmla_one _ _ (r111 B no))) (fmla_and _ _ _ (fmla_one _ _ (r112 B no)) (fmla_one _ _ (r113 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r114 B no)) (fmla_one _ _ (r115 B no))) (fmla_and _ _ _ (fmla_one _ _ (r116 B no)) (fmla_one _ _ (r117 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r118 B no)) (fmla_one _ _ (r119 B no))) (fmla_and _ _ _ (fmla_one _ _ (r120 B no)) (fmla_one _ _ (r121 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r122 B no)) (fmla_one _ _ (r123 B no))) (fmla_and _ _ _ (fmla_one _ _ (r124 B no)) (fmla_one _ _ (r125 B no)))))))))

#print axioms exclusion
#print axioms has_template
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Sparse2
