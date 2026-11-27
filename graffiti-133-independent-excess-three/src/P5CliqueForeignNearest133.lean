import P5CliqueNearestStemLift133
import P5CliqueNearestPortStem133

namespace Graffiti133P5CliqueArms.ForeignStem
open SimpleGraph Graffiti133 Graffiti133Camby IndependentFanFinite
set_option maxHeartbeats 5000000
set_option maxRecDepth 140000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def row0 : NearestStemCapsule := ⟨⟨1,2,1,0⟩,[],[⟨0,65,![1,12,2,6,4,0,8,11,3]⟩,⟨0,9,![2,12,1,5,4,0,8,11,3]⟩,⟨0,780,![5,1,12,2,10,8,11,3,7]⟩]⟩
private theorem row0_cert : nearestStemCapsuleChecked row0 := by decide
private def row1 : NearestStemCapsule := ⟨⟨1,2,2,0⟩,[],[⟨0,65,![1,12,13,2,6,4,0,8,11]⟩,⟨64,8,![0,8,11,6,2,13,12,1,5]⟩,⟨0,576,![1,12,13,2,6,4,7,3,11]⟩]⟩
private theorem row1_cert : nearestStemCapsuleChecked row1 := by decide
private def row2 : NearestStemCapsule := ⟨⟨1,2,2,1⟩,[],[⟨0,576,![1,12,13,2,6,4,7,3,11]⟩,⟨0,520,![2,13,12,1,5,4,7,3,11]⟩,⟨512,65,![1,12,13,2,6,4,7,11,8]⟩]⟩
private theorem row2_cert : nearestStemCapsuleChecked row2 := by decide
private def row3 : NearestStemCapsule := ⟨⟨1,2,2,8⟩,[],[⟨0,5,![1,5,4,0,8,10,2,13,3]⟩,⟨4,256,![0,8,10,5,1,12,13,3,7]⟩,⟨0,390,![5,1,9,8,10,2,13,3,7]⟩]⟩
private theorem row3_cert : nearestStemCapsuleChecked row3 := by decide
private def row4 : NearestStemCapsule := ⟨⟨1,2,2,9⟩,[],[⟨0,73,![1,5,4,6,2,13,3,11,8]⟩,⟨0,261,![1,5,4,7,3,13,2,10,8]⟩,⟨0,131,![2,13,3,7,4,5,1,9,8]⟩,⟨0,390,![5,1,9,8,10,2,13,3,7]⟩,⟨0,11,![2,13,3,11,8,9,1,5,4]⟩,⟨0,13,![4,5,1,12,13,2,10,8,11]⟩]⟩
private theorem row4_cert : nearestStemCapsuleChecked row4 := by decide
private def row5 : NearestStemCapsule := ⟨⟨1,2,3,0⟩,[],[⟨0,1,![1,12,13,14,2,6,4,0,8]⟩,⟨0,4,![0,4,5,1,12,13,14,2,10]⟩]⟩
private theorem row5_cert : nearestStemCapsuleChecked row5 := by decide
private def row6 : NearestStemCapsule := ⟨⟨1,2,3,1⟩,[],[⟨0,0,![1,12,13,14,2,6,4,7,3]⟩]⟩
private theorem row6_cert : nearestStemCapsuleChecked row6 := by decide
private def row7 : NearestStemCapsule := ⟨⟨1,2,3,8⟩,[],[⟨0,4,![0,4,5,1,12,13,14,2,10]⟩,⟨0,8,![0,4,5,1,12,13,14,3,11]⟩]⟩
private theorem row7_cert : nearestStemCapsuleChecked row7 := by decide
private def row8 : NearestStemCapsule := ⟨⟨1,2,3,9⟩,[],[⟨0,17,![2,6,4,0,8,9,1,12,13]⟩,⟨0,73,![1,5,4,6,2,14,3,11,8]⟩,⟨1,64,![1,12,13,14,2,6,4,8,11]⟩,⟨0,261,![1,5,4,7,3,14,2,10,8]⟩,⟨264,516,![2,10,7,3,11,5,1,12,13]⟩]⟩
private theorem row8_cert : nearestStemCapsuleChecked row8 := by decide
private def row9 : NearestStemCapsule := ⟨⟨1,2,4,0⟩,[],[⟨0,0,![0,4,5,1,12,13,14,15,2]⟩]⟩
private theorem row9_cert : nearestStemCapsuleChecked row9 := by decide
private def row10 : NearestStemCapsule := ⟨⟨1,2,4,1⟩,[],[⟨0,0,![1,12,13,14,15,0,4,7,3]⟩]⟩
private theorem row10_cert : nearestStemCapsuleChecked row10 := by decide
private def row11 : NearestStemCapsule := ⟨⟨1,2,4,8⟩,[],[⟨0,0,![0,4,5,1,12,13,14,15,2]⟩]⟩
private theorem row11_cert : nearestStemCapsuleChecked row11 := by decide
private def row12 : NearestStemCapsule := ⟨⟨1,2,4,9⟩,[],[⟨0,73,![1,5,4,6,2,15,3,11,8]⟩,⟨0,261,![1,5,4,7,3,15,2,10,8]⟩,⟨64,8,![1,5,4,6,11,3,15,14,13]⟩,⟨256,4,![1,5,4,7,10,2,15,14,13]⟩,⟨1,4,![1,5,4,8,10,2,15,14,13]⟩]⟩
private theorem row12_cert : nearestStemCapsuleChecked row12 := by decide

/-- Original-graph nearest-stem obstruction for two same-home clean fans. -/
theorem foreign_nearest_stem_without_relay_forces_p9 (h4 : FourCycleFree G)
    (D : Finset V) (p : Fin 4→V) (A : Finset V) (f : V→Fin 4→V)
    (H : PortFanFamily G (D : Set V) p A f) (ind : ∀ i j,¬G.Adj (p i) (p j))
    (q r : V) (qm : q∈A) (rm : r∈A) (qr : q≠r)
    (d : Nat) (lo : 2≤d) (hi : d≤5)
    (stem : IsNearestPortStem (G:=G) D p 1 2 d) :
    (∃ path : Fin 9→V,InducedPath G path) ∨
      (d=2 ∧ ∃ v∈D,G.Adj (p 1) v ∧ G.Adj (p 2) v ∧ (G.Adj (p 0) v ∨ G.Adj (p 3) v)) := by
  by_cases path : ∃ path : Fin 9→V,InducedPath G path
  · exact Or.inl path
  have noP9 : NoPath G 9 := path
  obtain ⟨m,F,fi,ports,outer,pure,fit⟩ := TwoFan.normalize h4 H ind q r qm rm qr
  have lens : d=2 ∨ d=3 ∨ d=4 ∨ d=5 := by omega
  rcases lens with rfl|rfl|rfl|rfl
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    have startEdge : G.Adj (p 1) (w 1) := by
      rw [←w0]
      exact (wp.2 0 1 (by decide)).mpr (by decide)
    have endEdge : G.Adj (p 2) (w 1) := by
      rw [←we,SimpleGraph.adj_comm]
      exact (wp.2 1 2 (by decide)).mpr (by decide)
    by_cases one : G.Adj (p 0) (w 1)
    · exact Or.inr ⟨rfl,w 1,wd _,startEdge,endEdge,Or.inl one⟩
    by_cases two : G.Adj (p 3) (w 1)
    · exact Or.inr ⟨rfl,w 1,wd _,startEdge,endEdge,Or.inr two⟩
    have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row0 row0_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
          intro i ni nz
          fin_cases i
          · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 0=true)) h).elim⟩
          · exact (ni rfl).elim
          · exact (nz rfl).elim
          · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 3=true)) h).elim⟩)
    exact False.elim (List.not_mem_nil rejected)
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    by_cases one : G.Adj (p 0) (w 2)
    · by_cases two : G.Adj (p 3) (w 2)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row4 row4_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row2 row2_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row2.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
    · by_cases two : G.Adj (p 3) (w 2)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row3 row3_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row3.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row1 row1_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row1.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row1.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    by_cases one : G.Adj (p 0) (w 3)
    · by_cases two : G.Adj (p 3) (w 3)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row8 row8_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row6 row6_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row6.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
    · by_cases two : G.Adj (p 3) (w 3)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row7 row7_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row7.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row5 row5_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row5.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row5.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    by_cases one : G.Adj (p 0) (w 4)
    · by_cases two : G.Adj (p 3) (w 4)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row12 row12_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row10 row10_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row10.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
    · by_cases two : G.Adj (p 3) (w 4)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row11 row11_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row11.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row9 row9_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row9.spec.extraTail.testBit 0=true)) h).elim⟩
              · exact (ni rfl).elim
              · exact (nz rfl).elim
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row9.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)

#print axioms foreign_nearest_stem_without_relay_forces_p9
end Graffiti133P5CliqueArms.ForeignStem
