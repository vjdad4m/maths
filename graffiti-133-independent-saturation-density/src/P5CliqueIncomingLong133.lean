import P5CliqueNearestStemLift133
import P5CliqueNearestPortStem133

namespace Graffiti133P5CliqueArms.IncomingLongStem
open SimpleGraph Graffiti133 Graffiti133Camby IndependentFanFinite
set_option maxHeartbeats 5000000
set_option maxRecDepth 140000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def row0 : NearestStemCapsule := ⟨⟨1,0,3,0⟩,[],[⟨0,32,![1,12,13,14,0,4,6,2,10]⟩,⟨0,17,![2,6,4,0,8,9,1,12,13]⟩]⟩
private theorem row0_cert : nearestStemCapsuleChecked row0 := by decide
private def row1 : NearestStemCapsule := ⟨⟨1,0,3,4⟩,[],[⟨0,0,![1,12,13,14,2,6,4,7,3]⟩]⟩
private theorem row1_cert : nearestStemCapsuleChecked row1 := by decide
private def row2 : NearestStemCapsule := ⟨⟨1,0,3,8⟩,[],[⟨0,0,![1,12,13,14,3,7,4,6,2]⟩]⟩
private theorem row2_cert : nearestStemCapsuleChecked row2 := by decide
private def row3 : NearestStemCapsule := ⟨⟨1,0,3,12⟩,[],[⟨0,17,![2,6,4,0,8,9,1,12,13]⟩,⟨0,73,![1,5,4,6,2,14,3,11,8]⟩,⟨1,64,![1,12,13,14,2,6,4,8,11]⟩,⟨0,261,![1,5,4,7,3,14,2,10,8]⟩,⟨264,516,![2,10,7,3,11,5,1,12,13]⟩]⟩
private theorem row3_cert : nearestStemCapsuleChecked row3 := by decide
private def row4 : NearestStemCapsule := ⟨⟨1,0,4,0⟩,[],[⟨0,0,![1,12,13,14,15,0,4,6,2]⟩]⟩
private theorem row4_cert : nearestStemCapsuleChecked row4 := by decide
private def row5 : NearestStemCapsule := ⟨⟨1,0,4,4⟩,[],[⟨0,0,![1,12,13,14,15,0,4,7,3]⟩]⟩
private theorem row5_cert : nearestStemCapsuleChecked row5 := by decide
private def row6 : NearestStemCapsule := ⟨⟨1,0,4,8⟩,[],[⟨0,0,![1,12,13,14,15,0,4,6,2]⟩]⟩
private theorem row6_cert : nearestStemCapsuleChecked row6 := by decide
private def row7 : NearestStemCapsule := ⟨⟨1,0,4,12⟩,[],[⟨0,73,![1,5,4,6,2,15,3,11,8]⟩,⟨0,261,![1,5,4,7,3,15,2,10,8]⟩,⟨64,8,![1,5,4,6,11,3,15,14,13]⟩,⟨256,4,![1,5,4,7,10,2,15,14,13]⟩,⟨1,4,![1,5,4,8,10,2,15,14,13]⟩]⟩
private theorem row7_cert : nearestStemCapsuleChecked row7 := by decide

/-- Original-graph nearest-stem obstruction for two same-home clean fans. -/
theorem incoming_nearest_stem_length_four_or_five_forces_p9 (h4 : FourCycleFree G)
    (D : Finset V) (p : Fin 4→V) (A : Finset V) (f : V→Fin 4→V)
    (H : PortFanFamily G (D : Set V) p A f) (ind : ∀ i j,¬G.Adj (p i) (p j))
    (q r : V) (qm : q∈A) (rm : r∈A) (qr : q≠r)
    (d : Nat) (lo : 4≤d) (hi : d≤5)
    (stem : IsNearestPortStem (G:=G) D p 1 0 d) :
    ∃ path : Fin 9→V,InducedPath G path := by
  by_cases path : ∃ path : Fin 9→V,InducedPath G path
  · exact path
  have noP9 : NoPath G 9 := path
  obtain ⟨m,F,fi,ports,outer,pure,fit⟩ := TwoFan.normalize h4 H ind q r qm rm qr
  have lens : d=4 ∨ d=5 := by omega
  rcases lens with rfl|rfl
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    by_cases one : G.Adj (p 2) (w 3)
    · by_cases two : G.Adj (p 3) (w 3)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row3 row3_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row1 row1_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row1.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
    · by_cases two : G.Adj (p 3) (w 3)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row2 row2_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row2.spec.extraTail.testBit 2=true)) h).elim⟩
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row0 row0_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 2=true)) h).elim⟩
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
  · obtain ⟨w,wp,wd,w0,we,mid,near⟩ := stem
    by_cases one : G.Adj (p 2) (w 4)
    · by_cases two : G.Adj (p 3) (w 4)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row7 row7_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row5 row5_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun _=>by decide,fun _=>one⟩
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row5.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)
    · by_cases two : G.Adj (p 3) (w 4)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row6 row6_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row6.spec.extraTail.testBit 2=true)) h).elim⟩
              · exact ⟨fun _=>by decide,fun _=>two⟩)
        exact False.elim (List.not_mem_nil rejected)
      · have rejected := TwoFan.nearest_stem_mask_survives noP9 D p row4 row4_cert m F fi ports outer pure fit
            (by decide) (by decide) (by decide) (by decide) w wp wd w0 we mid near (by
              intro i ni nz
              fin_cases i
              · exact (nz rfl).elim
              · exact (ni rfl).elim
              · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row4.spec.extraTail.testBit 2=true)) h).elim⟩
              · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row4.spec.extraTail.testBit 3=true)) h).elim⟩)
        exact False.elim (List.not_mem_nil rejected)

#print axioms incoming_nearest_stem_length_four_or_five_forces_p9
end Graffiti133P5CliqueArms.IncomingLongStem
