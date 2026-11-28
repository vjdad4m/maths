import SixSingletonFivePortPairCert189
import DiversityElevenMathlibRup384b

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow
open Sat
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000

packed_rup no_bad_cover
  (include_str "all-low-cert/cover.cnf")
  (include_str "all-low-cert/cover.lrat")

abbrev Bit := Nat→Bool
private def valuation (B : Bit) : Sat.Valuation := fun i=>B i=true
theorem fmla_and (v : Valuation) (f g : Fmla)
    (hf : v.satisfies_fmla f) (hg : v.satisfies_fmla g) :
    v.satisfies_fmla (Fmla.and f g) := by
  constructor
  intro c h
  rcases List.mem_append.mp h with h|h
  · exact hf.1 _ h
  · exact hg.1 _ h

theorem fmla_one (v : Valuation) (c : Clause)
    (h : v.satisfies c) : v.satisfies_fmla (Fmla.one c) := by
  constructor
  intro d dm
  exact (List.mem_singleton.mp dm).symm ▸ h


structure PortModel (B : Bit) : Prop where
  n0 : B 0=true ∨ B 1=true
  n1 : B 0=true ∨ B 2=true
  n2 : B 1=true ∨ B 2=true
  c0 : 2≤marks (B 0)+marks (B 1)+marks (B 3)+marks (B 4)+marks (B 5)
  c1 : 2≤marks (B 0)+marks (B 2)+marks (B 6)+marks (B 7)+marks (B 8)
  c2 : 2≤marks (B 1)+marks (B 2)+marks (B 9)+marks (B 10)+marks (B 11)
  d0 : 4≤marks (B 3)+marks (B 6)+marks (B 9)+marks (B 12)+marks (B 13)
  d1 : 3≤marks (B 4)+marks (B 7)+marks (B 10)+marks (B 14)+marks (B 15)
  d2 : 3≤marks (B 5)+marks (B 8)+marks (B 11)+marks (B 16)+marks (B 17)

def requirement : Fin 49 → List Nat := ![[0,2,3,10,14,17],[1,4,6,7,11,16],[1,5,8,9,13,15],[0,2,4,11,12,15],[1,5,6,10,12,14],[1,3,7,8,12,17],[0,5,7,9,13,16],[1,3,11,14,15,16],[2,4,6,10,13,17],[2,3,4,8,9,14],[1,6,7,9,15,17],[0,8,10,12,15,16],[2,3,5,7,11,13],[0,1,11,13,14,17],[2,5,7,9,12,17],[2,3,5,6,15,16],[1,3,8,10,13,16],[2,4,8,12,13,14],[0,5,6,10,11,15],[0,3,7,9,11,16],[0,4,6,9,14,16],[1,4,8,11,12,15],[0,4,8,9,10,17],[2,6,11,13,14,15],[1,3,7,10,13,17],[1,5,7,8,9,14],[1,4,12,15,16,17],[0,5,7,11,12,14],[2,4,5,10,12,16],[2,3,8,9,15,17],[1,5,6,7,10,12],[1,2,6,14,16,17],[0,2,5,10,13,14],[0,2,4,11,13,16],[1,3,6,14,15,17],[2,3,7,11,12,16],[0,1,8,10,13,14],[2,4,5,7,9,17],[0,5,7,10,12,17],[1,4,7,11,12,13],[0,4,9,15,16,17],[1,8,10,12,14,17],[1,4,6,8,11,13],[0,3,7,10,11,17],[1,5,6,8,10,15],[0,4,8,9,11,12],[1,7,9,12,15,16],[2,3,5,10,14,16],[2,3,4,11,15,17]]
def visit : Fin 49 → List (Fin 11) := ![[3,0,1,2,4,9,6,8,7,10,5],[3,1,4,0,2,5,9,6,8,7,10],[4,10,3,2,0,5,1,7,8,6,9],[3,9,6,8,7,10,4,0,1,2,5],[5,0,2,4,9,3,1,6,8,7,10],[4,1,5,10,7,8,6,9,3,0,2],[4,1,0,5,9,6,8,7,10,3,2],[3,0,2,5,9,4,10,7,8,6,1],[5,10,3,1,2,4,0,7,8,6,9],[5,1,2,3,0,4,9,6,8,7,10],[5,10,4,1,3,2,0,7,8,6,9],[3,9,5,1,0,6,8,7,10,4,2],[4,1,2,5,0,3,10,7,8,6,9],[3,10,5,2,0,1,7,8,6,9,4],[4,1,2,3,9,6,8,7,10,5,0],[4,10,7,8,6,9,5,0,3,1,2],[4,2,0,3,10,7,8,6,9,5,1],[5,1,2,6,8,7,10,3,9,4,0],[3,1,0,5,2,4,10,7,8,6,9],[4,1,0,3,2,5,9,6,8,7,10],[5,9,4,0,1,3,2,6,8,7,10],[3,9,6,8,7,10,4,0,2,5,1],[3,2,4,0,1,5,10,7,8,6,9],[5,2,1,3,10,4,9,6,8,7,0],[5,10,3,0,2,4,1,7,8,6,9],[3,2,0,5,1,4,9,6,8,7,10],[3,9,5,10,4,0,2,6,8,7,1],[3,9,4,1,0,5,2,6,8,7,10],[3,9,5,0,4,2,1,6,8,7,10],[4,10,5,1,2,3,0,7,8,6,9],[5,0,2,4,1,3,9,6,8,7,10],[3,1,2,0,6,8,7,10,5,9,4],[3,10,7,8,6,9,4,2,1,0,5],[3,10,7,8,6,9,5,2,1,0,4],[5,10,4,9,6,8,7,1,3,0,2],[4,1,2,5,9,3,0,6,8,7,10],[3,10,7,8,6,9,4,2,0,1,5],[3,2,1,4,0,5,10,7,8,6,9],[3,9,6,8,7,10,5,0,1,4,2],[5,2,0,4,1,6,8,7,10,3,9],[3,2,6,8,7,1,0,4,10,5,9],[3,9,4,2,0,6,8,7,10,5,1],[4,0,2,5,1,3,10,7,8,6,9],[3,0,1,4,2,5,10,7,8,6,9],[3,1,5,0,2,4,10,7,8,6,9],[4,0,1,5,2,3,9,6,8,7,10],[5,9,3,2,0,6,8,7,10,4,1],[3,0,5,9,4,2,1,6,8,7,10],[3,0,4,10,5,2,1,7,8,6,9]]
private abbrev Found (B : Bit) := ∃ k,∀ i∈requirement k,B i=true
private theorem mark_le_one (a : Bool) : marks a≤1 := by cases a <;> decide
private theorem mark_zero (a : Bool) (h : ¬a=true) : marks a=0 := by cases a <;> simp_all [marks]

private theorem r0 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 1] := by
  change (¬ B 0=true) → (¬ B 1=true) → False
  intro h0 h1
  exact M.n0.elim h0 h1

private theorem r1 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 2] := by
  change (¬ B 0=true) → (¬ B 2=true) → False
  intro h0 h2
  exact M.n1.elim h0 h2

private theorem r2 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 2] := by
  change (¬ B 1=true) → (¬ B 2=true) → False
  intro h1 h2
  exact M.n2.elim h1 h2

private theorem r3 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 3, .pos 4] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 3=true) → (¬ B 4=true) → False
  intro h0 h1 h3 h4
  have N := M.c0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h3, mark_zero _ h4] at N
  have u5 := mark_le_one (B 5)
  omega

private theorem r4 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 3, .pos 5] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 3=true) → (¬ B 5=true) → False
  intro h0 h1 h3 h5
  have N := M.c0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h3, mark_zero _ h5] at N
  have u4 := mark_le_one (B 4)
  omega

private theorem r5 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 1, .pos 4, .pos 5] := by
  change (¬ B 0=true) → (¬ B 1=true) → (¬ B 4=true) → (¬ B 5=true) → False
  intro h0 h1 h4 h5
  have N := M.c0
  rw [mark_zero _ h0, mark_zero _ h1, mark_zero _ h4, mark_zero _ h5] at N
  have u3 := mark_le_one (B 3)
  omega

private theorem r6 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 3, .pos 4, .pos 5] := by
  change (¬ B 0=true) → (¬ B 3=true) → (¬ B 4=true) → (¬ B 5=true) → False
  intro h0 h3 h4 h5
  have N := M.c0
  rw [mark_zero _ h0, mark_zero _ h3, mark_zero _ h4, mark_zero _ h5] at N
  have u1 := mark_le_one (B 1)
  omega

private theorem r7 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 3, .pos 4, .pos 5] := by
  change (¬ B 1=true) → (¬ B 3=true) → (¬ B 4=true) → (¬ B 5=true) → False
  intro h1 h3 h4 h5
  have N := M.c0
  rw [mark_zero _ h1, mark_zero _ h3, mark_zero _ h4, mark_zero _ h5] at N
  have u0 := mark_le_one (B 0)
  omega

private theorem r8 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 2, .pos 6, .pos 7] := by
  change (¬ B 0=true) → (¬ B 2=true) → (¬ B 6=true) → (¬ B 7=true) → False
  intro h0 h2 h6 h7
  have N := M.c1
  rw [mark_zero _ h0, mark_zero _ h2, mark_zero _ h6, mark_zero _ h7] at N
  have u8 := mark_le_one (B 8)
  omega

private theorem r9 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 2, .pos 6, .pos 8] := by
  change (¬ B 0=true) → (¬ B 2=true) → (¬ B 6=true) → (¬ B 8=true) → False
  intro h0 h2 h6 h8
  have N := M.c1
  rw [mark_zero _ h0, mark_zero _ h2, mark_zero _ h6, mark_zero _ h8] at N
  have u7 := mark_le_one (B 7)
  omega

private theorem r10 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 2, .pos 7, .pos 8] := by
  change (¬ B 0=true) → (¬ B 2=true) → (¬ B 7=true) → (¬ B 8=true) → False
  intro h0 h2 h7 h8
  have N := M.c1
  rw [mark_zero _ h0, mark_zero _ h2, mark_zero _ h7, mark_zero _ h8] at N
  have u6 := mark_le_one (B 6)
  omega

private theorem r11 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 0, .pos 6, .pos 7, .pos 8] := by
  change (¬ B 0=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → False
  intro h0 h6 h7 h8
  have N := M.c1
  rw [mark_zero _ h0, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8] at N
  have u2 := mark_le_one (B 2)
  omega

private theorem r12 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 2, .pos 6, .pos 7, .pos 8] := by
  change (¬ B 2=true) → (¬ B 6=true) → (¬ B 7=true) → (¬ B 8=true) → False
  intro h2 h6 h7 h8
  have N := M.c1
  rw [mark_zero _ h2, mark_zero _ h6, mark_zero _ h7, mark_zero _ h8] at N
  have u0 := mark_le_one (B 0)
  omega

private theorem r13 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 2, .pos 9, .pos 10] := by
  change (¬ B 1=true) → (¬ B 2=true) → (¬ B 9=true) → (¬ B 10=true) → False
  intro h1 h2 h9 h10
  have N := M.c2
  rw [mark_zero _ h1, mark_zero _ h2, mark_zero _ h9, mark_zero _ h10] at N
  have u11 := mark_le_one (B 11)
  omega

private theorem r14 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 2, .pos 9, .pos 11] := by
  change (¬ B 1=true) → (¬ B 2=true) → (¬ B 9=true) → (¬ B 11=true) → False
  intro h1 h2 h9 h11
  have N := M.c2
  rw [mark_zero _ h1, mark_zero _ h2, mark_zero _ h9, mark_zero _ h11] at N
  have u10 := mark_le_one (B 10)
  omega

private theorem r15 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 2, .pos 10, .pos 11] := by
  change (¬ B 1=true) → (¬ B 2=true) → (¬ B 10=true) → (¬ B 11=true) → False
  intro h1 h2 h10 h11
  have N := M.c2
  rw [mark_zero _ h1, mark_zero _ h2, mark_zero _ h10, mark_zero _ h11] at N
  have u9 := mark_le_one (B 9)
  omega

private theorem r16 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 1, .pos 9, .pos 10, .pos 11] := by
  change (¬ B 1=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → False
  intro h1 h9 h10 h11
  have N := M.c2
  rw [mark_zero _ h1, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11] at N
  have u2 := mark_le_one (B 2)
  omega

private theorem r17 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 2, .pos 9, .pos 10, .pos 11] := by
  change (¬ B 2=true) → (¬ B 9=true) → (¬ B 10=true) → (¬ B 11=true) → False
  intro h2 h9 h10 h11
  have N := M.c2
  rw [mark_zero _ h2, mark_zero _ h9, mark_zero _ h10, mark_zero _ h11] at N
  have u1 := mark_le_one (B 1)
  omega

private theorem r18 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 3, .pos 6] := by
  change (¬ B 3=true) → (¬ B 6=true) → False
  intro h3 h6
  have N := M.d0
  rw [mark_zero _ h3, mark_zero _ h6] at N
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r19 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 3, .pos 9] := by
  change (¬ B 3=true) → (¬ B 9=true) → False
  intro h3 h9
  have N := M.d0
  rw [mark_zero _ h3, mark_zero _ h9] at N
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r20 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 3, .pos 12] := by
  change (¬ B 3=true) → (¬ B 12=true) → False
  intro h3 h12
  have N := M.d0
  rw [mark_zero _ h3, mark_zero _ h12] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  omega

private theorem r21 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 3, .pos 13] := by
  change (¬ B 3=true) → (¬ B 13=true) → False
  intro h3 h13
  have N := M.d0
  rw [mark_zero _ h3, mark_zero _ h13] at N
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  omega

private theorem r22 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 6, .pos 9] := by
  change (¬ B 6=true) → (¬ B 9=true) → False
  intro h6 h9
  have N := M.d0
  rw [mark_zero _ h6, mark_zero _ h9] at N
  have u3 := mark_le_one (B 3)
  have u12 := mark_le_one (B 12)
  have u13 := mark_le_one (B 13)
  omega

private theorem r23 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 6, .pos 12] := by
  change (¬ B 6=true) → (¬ B 12=true) → False
  intro h6 h12
  have N := M.d0
  rw [mark_zero _ h6, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u9 := mark_le_one (B 9)
  have u13 := mark_le_one (B 13)
  omega

private theorem r24 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 6, .pos 13] := by
  change (¬ B 6=true) → (¬ B 13=true) → False
  intro h6 h13
  have N := M.d0
  rw [mark_zero _ h6, mark_zero _ h13] at N
  have u3 := mark_le_one (B 3)
  have u9 := mark_le_one (B 9)
  have u12 := mark_le_one (B 12)
  omega

private theorem r25 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 9, .pos 12] := by
  change (¬ B 9=true) → (¬ B 12=true) → False
  intro h9 h12
  have N := M.d0
  rw [mark_zero _ h9, mark_zero _ h12] at N
  have u3 := mark_le_one (B 3)
  have u6 := mark_le_one (B 6)
  have u13 := mark_le_one (B 13)
  omega

private theorem r26 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 9, .pos 13] := by
  change (¬ B 9=true) → (¬ B 13=true) → False
  intro h9 h13
  have N := M.d0
  rw [mark_zero _ h9, mark_zero _ h13] at N
  have u3 := mark_le_one (B 3)
  have u6 := mark_le_one (B 6)
  have u12 := mark_le_one (B 12)
  omega

private theorem r27 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 12, .pos 13] := by
  change (¬ B 12=true) → (¬ B 13=true) → False
  intro h12 h13
  have N := M.d0
  rw [mark_zero _ h12, mark_zero _ h13] at N
  have u3 := mark_le_one (B 3)
  have u6 := mark_le_one (B 6)
  have u9 := mark_le_one (B 9)
  omega

private theorem r28 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 7, .pos 10] := by
  change (¬ B 4=true) → (¬ B 7=true) → (¬ B 10=true) → False
  intro h4 h7 h10
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h7, mark_zero _ h10] at N
  have u14 := mark_le_one (B 14)
  have u15 := mark_le_one (B 15)
  omega

private theorem r29 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 7, .pos 14] := by
  change (¬ B 4=true) → (¬ B 7=true) → (¬ B 14=true) → False
  intro h4 h7 h14
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h7, mark_zero _ h14] at N
  have u10 := mark_le_one (B 10)
  have u15 := mark_le_one (B 15)
  omega

private theorem r30 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 7, .pos 15] := by
  change (¬ B 4=true) → (¬ B 7=true) → (¬ B 15=true) → False
  intro h4 h7 h15
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h7, mark_zero _ h15] at N
  have u10 := mark_le_one (B 10)
  have u14 := mark_le_one (B 14)
  omega

private theorem r31 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 10, .pos 14] := by
  change (¬ B 4=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h4 h10 h14
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h10, mark_zero _ h14] at N
  have u7 := mark_le_one (B 7)
  have u15 := mark_le_one (B 15)
  omega

private theorem r32 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 10, .pos 15] := by
  change (¬ B 4=true) → (¬ B 10=true) → (¬ B 15=true) → False
  intro h4 h10 h15
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h10, mark_zero _ h15] at N
  have u7 := mark_le_one (B 7)
  have u14 := mark_le_one (B 14)
  omega

private theorem r33 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 4, .pos 14, .pos 15] := by
  change (¬ B 4=true) → (¬ B 14=true) → (¬ B 15=true) → False
  intro h4 h14 h15
  have N := M.d1
  rw [mark_zero _ h4, mark_zero _ h14, mark_zero _ h15] at N
  have u7 := mark_le_one (B 7)
  have u10 := mark_le_one (B 10)
  omega

private theorem r34 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 14] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 14=true) → False
  intro h7 h10 h14
  have N := M.d1
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h14] at N
  have u4 := mark_le_one (B 4)
  have u15 := mark_le_one (B 15)
  omega

private theorem r35 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 7, .pos 10, .pos 15] := by
  change (¬ B 7=true) → (¬ B 10=true) → (¬ B 15=true) → False
  intro h7 h10 h15
  have N := M.d1
  rw [mark_zero _ h7, mark_zero _ h10, mark_zero _ h15] at N
  have u4 := mark_le_one (B 4)
  have u14 := mark_le_one (B 14)
  omega

private theorem r36 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 7, .pos 14, .pos 15] := by
  change (¬ B 7=true) → (¬ B 14=true) → (¬ B 15=true) → False
  intro h7 h14 h15
  have N := M.d1
  rw [mark_zero _ h7, mark_zero _ h14, mark_zero _ h15] at N
  have u4 := mark_le_one (B 4)
  have u10 := mark_le_one (B 10)
  omega

private theorem r37 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 10, .pos 14, .pos 15] := by
  change (¬ B 10=true) → (¬ B 14=true) → (¬ B 15=true) → False
  intro h10 h14 h15
  have N := M.d1
  rw [mark_zero _ h10, mark_zero _ h14, mark_zero _ h15] at N
  have u4 := mark_le_one (B 4)
  have u7 := mark_le_one (B 7)
  omega

private theorem r38 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 8, .pos 11] := by
  change (¬ B 5=true) → (¬ B 8=true) → (¬ B 11=true) → False
  intro h5 h8 h11
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h8, mark_zero _ h11] at N
  have u16 := mark_le_one (B 16)
  have u17 := mark_le_one (B 17)
  omega

private theorem r39 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 8, .pos 16] := by
  change (¬ B 5=true) → (¬ B 8=true) → (¬ B 16=true) → False
  intro h5 h8 h16
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h8, mark_zero _ h16] at N
  have u11 := mark_le_one (B 11)
  have u17 := mark_le_one (B 17)
  omega

private theorem r40 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 8, .pos 17] := by
  change (¬ B 5=true) → (¬ B 8=true) → (¬ B 17=true) → False
  intro h5 h8 h17
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h8, mark_zero _ h17] at N
  have u11 := mark_le_one (B 11)
  have u16 := mark_le_one (B 16)
  omega

private theorem r41 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 11, .pos 16] := by
  change (¬ B 5=true) → (¬ B 11=true) → (¬ B 16=true) → False
  intro h5 h11 h16
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h11, mark_zero _ h16] at N
  have u8 := mark_le_one (B 8)
  have u17 := mark_le_one (B 17)
  omega

private theorem r42 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 11, .pos 17] := by
  change (¬ B 5=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h5 h11 h17
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h11, mark_zero _ h17] at N
  have u8 := mark_le_one (B 8)
  have u16 := mark_le_one (B 16)
  omega

private theorem r43 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 5, .pos 16, .pos 17] := by
  change (¬ B 5=true) → (¬ B 16=true) → (¬ B 17=true) → False
  intro h5 h16 h17
  have N := M.d2
  rw [mark_zero _ h5, mark_zero _ h16, mark_zero _ h17] at N
  have u8 := mark_le_one (B 8)
  have u11 := mark_le_one (B 11)
  omega

private theorem r44 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 16] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 16=true) → False
  intro h8 h11 h16
  have N := M.d2
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h16] at N
  have u5 := mark_le_one (B 5)
  have u17 := mark_le_one (B 17)
  omega

private theorem r45 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 8, .pos 11, .pos 17] := by
  change (¬ B 8=true) → (¬ B 11=true) → (¬ B 17=true) → False
  intro h8 h11 h17
  have N := M.d2
  rw [mark_zero _ h8, mark_zero _ h11, mark_zero _ h17] at N
  have u5 := mark_le_one (B 5)
  have u16 := mark_le_one (B 16)
  omega

private theorem r46 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 8, .pos 16, .pos 17] := by
  change (¬ B 8=true) → (¬ B 16=true) → (¬ B 17=true) → False
  intro h8 h16 h17
  have N := M.d2
  rw [mark_zero _ h8, mark_zero _ h16, mark_zero _ h17] at N
  have u5 := mark_le_one (B 5)
  have u11 := mark_le_one (B 11)
  omega

private theorem r47 (B : Bit) (M : PortModel B) : (valuation B).satisfies [.pos 11, .pos 16, .pos 17] := by
  change (¬ B 11=true) → (¬ B 16=true) → (¬ B 17=true) → False
  intro h11 h16 h17
  have N := M.d2
  rw [mark_zero _ h11, mark_zero _ h16, mark_zero _ h17] at N
  have u5 := mark_le_one (B 5)
  have u8 := mark_le_one (B 8)
  omega

private theorem r48 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 2, .neg 3, .neg 10, .neg 14, .neg 17] := by
  change (B 0=true) → (B 2=true) → (B 3=true) → (B 10=true) → (B 14=true) → (B 17=true) → False
  intro h0 h2 h3 h10 h14 h17
  apply no ⟨0,?_⟩
  intro i m
  change i∈[0,2,3,10,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r49 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 6, .neg 7, .neg 11, .neg 16] := by
  change (B 1=true) → (B 4=true) → (B 6=true) → (B 7=true) → (B 11=true) → (B 16=true) → False
  intro h1 h4 h6 h7 h11 h16
  apply no ⟨1,?_⟩
  intro i m
  change i∈[1,4,6,7,11,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h16

private theorem r50 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 8, .neg 9, .neg 13, .neg 15] := by
  change (B 1=true) → (B 5=true) → (B 8=true) → (B 9=true) → (B 13=true) → (B 15=true) → False
  intro h1 h5 h8 h9 h13 h15
  apply no ⟨2,?_⟩
  intro i m
  change i∈[1,5,8,9,13,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h15

private theorem r51 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 2, .neg 4, .neg 11, .neg 12, .neg 15] := by
  change (B 0=true) → (B 2=true) → (B 4=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h0 h2 h4 h11 h12 h15
  apply no ⟨3,?_⟩
  intro i m
  change i∈[0,2,4,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r52 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 6, .neg 10, .neg 12, .neg 14] := by
  change (B 1=true) → (B 5=true) → (B 6=true) → (B 10=true) → (B 12=true) → (B 14=true) → False
  intro h1 h5 h6 h10 h12 h14
  apply no ⟨4,?_⟩
  intro i m
  change i∈[1,5,6,10,12,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h6
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14

private theorem r53 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 3, .neg 7, .neg 8, .neg 12, .neg 17] := by
  change (B 1=true) → (B 3=true) → (B 7=true) → (B 8=true) → (B 12=true) → (B 17=true) → False
  intro h1 h3 h7 h8 h12 h17
  apply no ⟨5,?_⟩
  intro i m
  change i∈[1,3,7,8,12,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h17

private theorem r54 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 5, .neg 7, .neg 9, .neg 13, .neg 16] := by
  change (B 0=true) → (B 5=true) → (B 7=true) → (B 9=true) → (B 13=true) → (B 16=true) → False
  intro h0 h5 h7 h9 h13 h16
  apply no ⟨6,?_⟩
  intro i m
  change i∈[0,5,7,9,13,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h13
  · exact m.symm ▸ h16

private theorem r55 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 3, .neg 11, .neg 14, .neg 15, .neg 16] := by
  change (B 1=true) → (B 3=true) → (B 11=true) → (B 14=true) → (B 15=true) → (B 16=true) → False
  intro h1 h3 h11 h14 h15 h16
  apply no ⟨7,?_⟩
  intro i m
  change i∈[1,3,11,14,15,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h3
  · exact m.symm ▸ h11
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16

private theorem r56 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 6, .neg 10, .neg 13, .neg 17] := by
  change (B 2=true) → (B 4=true) → (B 6=true) → (B 10=true) → (B 13=true) → (B 17=true) → False
  intro h2 h4 h6 h10 h13 h17
  apply no ⟨8,?_⟩
  intro i m
  change i∈[2,4,6,10,13,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h17

private theorem r57 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 4, .neg 8, .neg 9, .neg 14] := by
  change (B 2=true) → (B 3=true) → (B 4=true) → (B 8=true) → (B 9=true) → (B 14=true) → False
  intro h2 h3 h4 h8 h9 h14
  apply no ⟨9,?_⟩
  intro i m
  change i∈[2,3,4,8,9,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h14

private theorem r58 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 6, .neg 7, .neg 9, .neg 15, .neg 17] := by
  change (B 1=true) → (B 6=true) → (B 7=true) → (B 9=true) → (B 15=true) → (B 17=true) → False
  intro h1 h6 h7 h9 h15 h17
  apply no ⟨10,?_⟩
  intro i m
  change i∈[1,6,7,9,15,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h6
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h15
  · exact m.symm ▸ h17

private theorem r59 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 8, .neg 10, .neg 12, .neg 15, .neg 16] := by
  change (B 0=true) → (B 8=true) → (B 10=true) → (B 12=true) → (B 15=true) → (B 16=true) → False
  intro h0 h8 h10 h12 h15 h16
  apply no ⟨11,?_⟩
  intro i m
  change i∈[0,8,10,12,15,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16

private theorem r60 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 5, .neg 7, .neg 11, .neg 13] := by
  change (B 2=true) → (B 3=true) → (B 5=true) → (B 7=true) → (B 11=true) → (B 13=true) → False
  intro h2 h3 h5 h7 h11 h13
  apply no ⟨12,?_⟩
  intro i m
  change i∈[2,3,5,7,11,13] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13

private theorem r61 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 1, .neg 11, .neg 13, .neg 14, .neg 17] := by
  change (B 0=true) → (B 1=true) → (B 11=true) → (B 13=true) → (B 14=true) → (B 17=true) → False
  intro h0 h1 h11 h13 h14 h17
  apply no ⟨13,?_⟩
  intro i m
  change i∈[0,1,11,13,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h1
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r62 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 5, .neg 7, .neg 9, .neg 12, .neg 17] := by
  change (B 2=true) → (B 5=true) → (B 7=true) → (B 9=true) → (B 12=true) → (B 17=true) → False
  intro h2 h5 h7 h9 h12 h17
  apply no ⟨14,?_⟩
  intro i m
  change i∈[2,5,7,9,12,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h12
  · exact m.symm ▸ h17

private theorem r63 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 5, .neg 6, .neg 15, .neg 16] := by
  change (B 2=true) → (B 3=true) → (B 5=true) → (B 6=true) → (B 15=true) → (B 16=true) → False
  intro h2 h3 h5 h6 h15 h16
  apply no ⟨15,?_⟩
  intro i m
  change i∈[2,3,5,6,15,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h5
  · exact m.symm ▸ h6
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16

private theorem r64 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 3, .neg 8, .neg 10, .neg 13, .neg 16] := by
  change (B 1=true) → (B 3=true) → (B 8=true) → (B 10=true) → (B 13=true) → (B 16=true) → False
  intro h1 h3 h8 h10 h13 h16
  apply no ⟨16,?_⟩
  intro i m
  change i∈[1,3,8,10,13,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h16

private theorem r65 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 8, .neg 12, .neg 13, .neg 14] := by
  change (B 2=true) → (B 4=true) → (B 8=true) → (B 12=true) → (B 13=true) → (B 14=true) → False
  intro h2 h4 h8 h12 h13 h14
  apply no ⟨17,?_⟩
  intro i m
  change i∈[2,4,8,12,13,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14

private theorem r66 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 5, .neg 6, .neg 10, .neg 11, .neg 15] := by
  change (B 0=true) → (B 5=true) → (B 6=true) → (B 10=true) → (B 11=true) → (B 15=true) → False
  intro h0 h5 h6 h10 h11 h15
  apply no ⟨18,?_⟩
  intro i m
  change i∈[0,5,6,10,11,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h5
  · exact m.symm ▸ h6
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h15

private theorem r67 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 3, .neg 7, .neg 9, .neg 11, .neg 16] := by
  change (B 0=true) → (B 3=true) → (B 7=true) → (B 9=true) → (B 11=true) → (B 16=true) → False
  intro h0 h3 h7 h9 h11 h16
  apply no ⟨19,?_⟩
  intro i m
  change i∈[0,3,7,9,11,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h11
  · exact m.symm ▸ h16

private theorem r68 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 4, .neg 6, .neg 9, .neg 14, .neg 16] := by
  change (B 0=true) → (B 4=true) → (B 6=true) → (B 9=true) → (B 14=true) → (B 16=true) → False
  intro h0 h4 h6 h9 h14 h16
  apply no ⟨20,?_⟩
  intro i m
  change i∈[0,4,6,9,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h9
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r69 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 8, .neg 11, .neg 12, .neg 15] := by
  change (B 1=true) → (B 4=true) → (B 8=true) → (B 11=true) → (B 12=true) → (B 15=true) → False
  intro h1 h4 h8 h11 h12 h15
  apply no ⟨21,?_⟩
  intro i m
  change i∈[1,4,8,11,12,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15

private theorem r70 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 4, .neg 8, .neg 9, .neg 10, .neg 17] := by
  change (B 0=true) → (B 4=true) → (B 8=true) → (B 9=true) → (B 10=true) → (B 17=true) → False
  intro h0 h4 h8 h9 h10 h17
  apply no ⟨22,?_⟩
  intro i m
  change i∈[0,4,8,9,10,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h10
  · exact m.symm ▸ h17

private theorem r71 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 6, .neg 11, .neg 13, .neg 14, .neg 15] := by
  change (B 2=true) → (B 6=true) → (B 11=true) → (B 13=true) → (B 14=true) → (B 15=true) → False
  intro h2 h6 h11 h13 h14 h15
  apply no ⟨23,?_⟩
  intro i m
  change i∈[2,6,11,13,14,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h6
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15

private theorem r72 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 3, .neg 7, .neg 10, .neg 13, .neg 17] := by
  change (B 1=true) → (B 3=true) → (B 7=true) → (B 10=true) → (B 13=true) → (B 17=true) → False
  intro h1 h3 h7 h10 h13 h17
  apply no ⟨24,?_⟩
  intro i m
  change i∈[1,3,7,10,13,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h17

private theorem r73 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 7, .neg 8, .neg 9, .neg 14] := by
  change (B 1=true) → (B 5=true) → (B 7=true) → (B 8=true) → (B 9=true) → (B 14=true) → False
  intro h1 h5 h7 h8 h9 h14
  apply no ⟨25,?_⟩
  intro i m
  change i∈[1,5,7,8,9,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h14

private theorem r74 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 12, .neg 15, .neg 16, .neg 17] := by
  change (B 1=true) → (B 4=true) → (B 12=true) → (B 15=true) → (B 16=true) → (B 17=true) → False
  intro h1 h4 h12 h15 h16 h17
  apply no ⟨26,?_⟩
  intro i m
  change i∈[1,4,12,15,16,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16
  · exact m.symm ▸ h17

private theorem r75 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 5, .neg 7, .neg 11, .neg 12, .neg 14] := by
  change (B 0=true) → (B 5=true) → (B 7=true) → (B 11=true) → (B 12=true) → (B 14=true) → False
  intro h0 h5 h7 h11 h12 h14
  apply no ⟨27,?_⟩
  intro i m
  change i∈[0,5,7,11,12,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14

private theorem r76 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 5, .neg 10, .neg 12, .neg 16] := by
  change (B 2=true) → (B 4=true) → (B 5=true) → (B 10=true) → (B 12=true) → (B 16=true) → False
  intro h2 h4 h5 h10 h12 h16
  apply no ⟨28,?_⟩
  intro i m
  change i∈[2,4,5,10,12,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h5
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h16

private theorem r77 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 8, .neg 9, .neg 15, .neg 17] := by
  change (B 2=true) → (B 3=true) → (B 8=true) → (B 9=true) → (B 15=true) → (B 17=true) → False
  intro h2 h3 h8 h9 h15 h17
  apply no ⟨29,?_⟩
  intro i m
  change i∈[2,3,8,9,15,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h15
  · exact m.symm ▸ h17

private theorem r78 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 6, .neg 7, .neg 10, .neg 12] := by
  change (B 1=true) → (B 5=true) → (B 6=true) → (B 7=true) → (B 10=true) → (B 12=true) → False
  intro h1 h5 h6 h7 h10 h12
  apply no ⟨30,?_⟩
  intro i m
  change i∈[1,5,6,7,10,12] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h6
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12

private theorem r79 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 2, .neg 6, .neg 14, .neg 16, .neg 17] := by
  change (B 1=true) → (B 2=true) → (B 6=true) → (B 14=true) → (B 16=true) → (B 17=true) → False
  intro h1 h2 h6 h14 h16 h17
  apply no ⟨31,?_⟩
  intro i m
  change i∈[1,2,6,14,16,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h2
  · exact m.symm ▸ h6
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16
  · exact m.symm ▸ h17

private theorem r80 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 2, .neg 5, .neg 10, .neg 13, .neg 14] := by
  change (B 0=true) → (B 2=true) → (B 5=true) → (B 10=true) → (B 13=true) → (B 14=true) → False
  intro h0 h2 h5 h10 h13 h14
  apply no ⟨32,?_⟩
  intro i m
  change i∈[0,2,5,10,13,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h2
  · exact m.symm ▸ h5
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14

private theorem r81 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 2, .neg 4, .neg 11, .neg 13, .neg 16] := by
  change (B 0=true) → (B 2=true) → (B 4=true) → (B 11=true) → (B 13=true) → (B 16=true) → False
  intro h0 h2 h4 h11 h13 h16
  apply no ⟨33,?_⟩
  intro i m
  change i∈[0,2,4,11,13,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13
  · exact m.symm ▸ h16

private theorem r82 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 3, .neg 6, .neg 14, .neg 15, .neg 17] := by
  change (B 1=true) → (B 3=true) → (B 6=true) → (B 14=true) → (B 15=true) → (B 17=true) → False
  intro h1 h3 h6 h14 h15 h17
  apply no ⟨34,?_⟩
  intro i m
  change i∈[1,3,6,14,15,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h3
  · exact m.symm ▸ h6
  · exact m.symm ▸ h14
  · exact m.symm ▸ h15
  · exact m.symm ▸ h17

private theorem r83 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 7, .neg 11, .neg 12, .neg 16] := by
  change (B 2=true) → (B 3=true) → (B 7=true) → (B 11=true) → (B 12=true) → (B 16=true) → False
  intro h2 h3 h7 h11 h12 h16
  apply no ⟨35,?_⟩
  intro i m
  change i∈[2,3,7,11,12,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h16

private theorem r84 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 1, .neg 8, .neg 10, .neg 13, .neg 14] := by
  change (B 0=true) → (B 1=true) → (B 8=true) → (B 10=true) → (B 13=true) → (B 14=true) → False
  intro h0 h1 h8 h10 h13 h14
  apply no ⟨36,?_⟩
  intro i m
  change i∈[0,1,8,10,13,14] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h1
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h13
  · exact m.symm ▸ h14

private theorem r85 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 4, .neg 5, .neg 7, .neg 9, .neg 17] := by
  change (B 2=true) → (B 4=true) → (B 5=true) → (B 7=true) → (B 9=true) → (B 17=true) → False
  intro h2 h4 h5 h7 h9 h17
  apply no ⟨37,?_⟩
  intro i m
  change i∈[2,4,5,7,9,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h4
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h17

private theorem r86 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 5, .neg 7, .neg 10, .neg 12, .neg 17] := by
  change (B 0=true) → (B 5=true) → (B 7=true) → (B 10=true) → (B 12=true) → (B 17=true) → False
  intro h0 h5 h7 h10 h12 h17
  apply no ⟨38,?_⟩
  intro i m
  change i∈[0,5,7,10,12,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h5
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h17

private theorem r87 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 7, .neg 11, .neg 12, .neg 13] := by
  change (B 1=true) → (B 4=true) → (B 7=true) → (B 11=true) → (B 12=true) → (B 13=true) → False
  intro h1 h4 h7 h11 h12 h13
  apply no ⟨39,?_⟩
  intro i m
  change i∈[1,4,7,11,12,13] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h7
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12
  · exact m.symm ▸ h13

private theorem r88 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 4, .neg 9, .neg 15, .neg 16, .neg 17] := by
  change (B 0=true) → (B 4=true) → (B 9=true) → (B 15=true) → (B 16=true) → (B 17=true) → False
  intro h0 h4 h9 h15 h16 h17
  apply no ⟨40,?_⟩
  intro i m
  change i∈[0,4,9,15,16,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h4
  · exact m.symm ▸ h9
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16
  · exact m.symm ▸ h17

private theorem r89 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 8, .neg 10, .neg 12, .neg 14, .neg 17] := by
  change (B 1=true) → (B 8=true) → (B 10=true) → (B 12=true) → (B 14=true) → (B 17=true) → False
  intro h1 h8 h10 h12 h14 h17
  apply no ⟨41,?_⟩
  intro i m
  change i∈[1,8,10,12,14,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h12
  · exact m.symm ▸ h14
  · exact m.symm ▸ h17

private theorem r90 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 4, .neg 6, .neg 8, .neg 11, .neg 13] := by
  change (B 1=true) → (B 4=true) → (B 6=true) → (B 8=true) → (B 11=true) → (B 13=true) → False
  intro h1 h4 h6 h8 h11 h13
  apply no ⟨42,?_⟩
  intro i m
  change i∈[1,4,6,8,11,13] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h4
  · exact m.symm ▸ h6
  · exact m.symm ▸ h8
  · exact m.symm ▸ h11
  · exact m.symm ▸ h13

private theorem r91 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 3, .neg 7, .neg 10, .neg 11, .neg 17] := by
  change (B 0=true) → (B 3=true) → (B 7=true) → (B 10=true) → (B 11=true) → (B 17=true) → False
  intro h0 h3 h7 h10 h11 h17
  apply no ⟨43,?_⟩
  intro i m
  change i∈[0,3,7,10,11,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h3
  · exact m.symm ▸ h7
  · exact m.symm ▸ h10
  · exact m.symm ▸ h11
  · exact m.symm ▸ h17

private theorem r92 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 5, .neg 6, .neg 8, .neg 10, .neg 15] := by
  change (B 1=true) → (B 5=true) → (B 6=true) → (B 8=true) → (B 10=true) → (B 15=true) → False
  intro h1 h5 h6 h8 h10 h15
  apply no ⟨44,?_⟩
  intro i m
  change i∈[1,5,6,8,10,15] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h5
  · exact m.symm ▸ h6
  · exact m.symm ▸ h8
  · exact m.symm ▸ h10
  · exact m.symm ▸ h15

private theorem r93 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 0, .neg 4, .neg 8, .neg 9, .neg 11, .neg 12] := by
  change (B 0=true) → (B 4=true) → (B 8=true) → (B 9=true) → (B 11=true) → (B 12=true) → False
  intro h0 h4 h8 h9 h11 h12
  apply no ⟨45,?_⟩
  intro i m
  change i∈[0,4,8,9,11,12] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h0
  · exact m.symm ▸ h4
  · exact m.symm ▸ h8
  · exact m.symm ▸ h9
  · exact m.symm ▸ h11
  · exact m.symm ▸ h12

private theorem r94 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 1, .neg 7, .neg 9, .neg 12, .neg 15, .neg 16] := by
  change (B 1=true) → (B 7=true) → (B 9=true) → (B 12=true) → (B 15=true) → (B 16=true) → False
  intro h1 h7 h9 h12 h15 h16
  apply no ⟨46,?_⟩
  intro i m
  change i∈[1,7,9,12,15,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h1
  · exact m.symm ▸ h7
  · exact m.symm ▸ h9
  · exact m.symm ▸ h12
  · exact m.symm ▸ h15
  · exact m.symm ▸ h16

private theorem r95 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 5, .neg 10, .neg 14, .neg 16] := by
  change (B 2=true) → (B 3=true) → (B 5=true) → (B 10=true) → (B 14=true) → (B 16=true) → False
  intro h2 h3 h5 h10 h14 h16
  apply no ⟨47,?_⟩
  intro i m
  change i∈[2,3,5,10,14,16] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h5
  · exact m.symm ▸ h10
  · exact m.symm ▸ h14
  · exact m.symm ▸ h16

private theorem r96 (B : Bit) (no : ¬ Found B) : (valuation B).satisfies [.neg 2, .neg 3, .neg 4, .neg 11, .neg 15, .neg 17] := by
  change (B 2=true) → (B 3=true) → (B 4=true) → (B 11=true) → (B 15=true) → (B 17=true) → False
  intro h2 h3 h4 h11 h15 h17
  apply no ⟨48,?_⟩
  intro i m
  change i∈[2,3,4,11,15,17] at m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with m|m|m|m|m|m
  · exact m.symm ▸ h2
  · exact m.symm ▸ h3
  · exact m.symm ▸ h4
  · exact m.symm ▸ h11
  · exact m.symm ▸ h15
  · exact m.symm ▸ h17

theorem has_template (B : Bit) (M : PortModel B) : Found B := by
  by_contra no
  exact no_bad_cover (valuation B) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r0 B M)) (fmla_and _ _ _ (fmla_one _ _ (r1 B M)) (fmla_one _ _ (r2 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r3 B M)) (fmla_and _ _ _ (fmla_one _ _ (r4 B M)) (fmla_one _ _ (r5 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r6 B M)) (fmla_and _ _ _ (fmla_one _ _ (r7 B M)) (fmla_one _ _ (r8 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r9 B M)) (fmla_and _ _ _ (fmla_one _ _ (r10 B M)) (fmla_one _ _ (r11 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r12 B M)) (fmla_and _ _ _ (fmla_one _ _ (r13 B M)) (fmla_one _ _ (r14 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r15 B M)) (fmla_and _ _ _ (fmla_one _ _ (r16 B M)) (fmla_one _ _ (r17 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r18 B M)) (fmla_and _ _ _ (fmla_one _ _ (r19 B M)) (fmla_one _ _ (r20 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r21 B M)) (fmla_and _ _ _ (fmla_one _ _ (r22 B M)) (fmla_one _ _ (r23 B M))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r24 B M)) (fmla_and _ _ _ (fmla_one _ _ (r25 B M)) (fmla_one _ _ (r26 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r27 B M)) (fmla_and _ _ _ (fmla_one _ _ (r28 B M)) (fmla_one _ _ (r29 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r30 B M)) (fmla_and _ _ _ (fmla_one _ _ (r31 B M)) (fmla_one _ _ (r32 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r33 B M)) (fmla_and _ _ _ (fmla_one _ _ (r34 B M)) (fmla_one _ _ (r35 B M)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r36 B M)) (fmla_and _ _ _ (fmla_one _ _ (r37 B M)) (fmla_one _ _ (r38 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r39 B M)) (fmla_and _ _ _ (fmla_one _ _ (r40 B M)) (fmla_one _ _ (r41 B M))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r42 B M)) (fmla_and _ _ _ (fmla_one _ _ (r43 B M)) (fmla_one _ _ (r44 B M)))) (fmla_and _ _ _ (fmla_one _ _ (r45 B M)) (fmla_and _ _ _ (fmla_one _ _ (r46 B M)) (fmla_one _ _ (r47 B M)))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r48 B no)) (fmla_and _ _ _ (fmla_one _ _ (r49 B no)) (fmla_one _ _ (r50 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r51 B no)) (fmla_and _ _ _ (fmla_one _ _ (r52 B no)) (fmla_one _ _ (r53 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r54 B no)) (fmla_and _ _ _ (fmla_one _ _ (r55 B no)) (fmla_one _ _ (r56 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r57 B no)) (fmla_and _ _ _ (fmla_one _ _ (r58 B no)) (fmla_one _ _ (r59 B no)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r60 B no)) (fmla_and _ _ _ (fmla_one _ _ (r61 B no)) (fmla_one _ _ (r62 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r63 B no)) (fmla_and _ _ _ (fmla_one _ _ (r64 B no)) (fmla_one _ _ (r65 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r66 B no)) (fmla_and _ _ _ (fmla_one _ _ (r67 B no)) (fmla_one _ _ (r68 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r69 B no)) (fmla_and _ _ _ (fmla_one _ _ (r70 B no)) (fmla_one _ _ (r71 B no))))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r72 B no)) (fmla_and _ _ _ (fmla_one _ _ (r73 B no)) (fmla_one _ _ (r74 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r75 B no)) (fmla_and _ _ _ (fmla_one _ _ (r76 B no)) (fmla_one _ _ (r77 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r78 B no)) (fmla_and _ _ _ (fmla_one _ _ (r79 B no)) (fmla_one _ _ (r80 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r81 B no)) (fmla_and _ _ _ (fmla_one _ _ (r82 B no)) (fmla_one _ _ (r83 B no)))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r84 B no)) (fmla_and _ _ _ (fmla_one _ _ (r85 B no)) (fmla_one _ _ (r86 B no)))) (fmla_and _ _ _ (fmla_one _ _ (r87 B no)) (fmla_and _ _ _ (fmla_one _ _ (r88 B no)) (fmla_one _ _ (r89 B no))))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r90 B no)) (fmla_and _ _ _ (fmla_one _ _ (r91 B no)) (fmla_one _ _ (r92 B no)))) (fmla_and _ _ _ (fmla_and _ _ _ (fmla_one _ _ (r93 B no)) (fmla_one _ _ (r94 B no))) (fmla_and _ _ _ (fmla_one _ _ (r95 B no)) (fmla_one _ _ (r96 B no)))))))))

#print axioms no_bad_cover
#print axioms has_template
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow
