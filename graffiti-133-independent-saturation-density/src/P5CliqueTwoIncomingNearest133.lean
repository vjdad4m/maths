import P5CliqueNearestStemLift133
import P5CliqueNearestPortStem133
import P5CliqueDoubleStemSix133

namespace Graffiti133P5CliqueArms.TwoIncomingNearest
open SimpleGraph Graffiti133 Graffiti133Camby IndependentFanFinite
set_option maxHeartbeats 5000000
set_option maxRecDepth 140000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def row0 : NearestStemCapsule := ⟨⟨1,0,2,0⟩,[168,532],[⟨0,36,![5,1,12,13,0,8,10,2,6]⟩,⟨0,641,![4,7,3,11,8,9,1,12,13]⟩,⟨0,91,![2,6,4,5,1,9,8,11,3]⟩,⟨68,40,![0,13,12,1,5,10,2,6,11]⟩,⟨512,209,![2,6,4,7,11,8,9,1,12]⟩]⟩
private theorem row0_cert : nearestStemCapsuleChecked row0 := by decide
private def row1 : NearestStemCapsule := ⟨⟨1,0,2,4⟩,[],[⟨0,576,![1,12,13,2,6,4,7,3,11]⟩,⟨0,520,![2,13,12,1,5,4,7,3,11]⟩,⟨512,65,![1,12,13,2,6,4,7,11,8]⟩]⟩
private theorem row1_cert : nearestStemCapsuleChecked row1 := by decide
private def row2 : NearestStemCapsule := ⟨⟨1,0,2,8⟩,[],[⟨0,288,![1,12,13,3,7,4,6,2,10]⟩,⟨0,144,![2,6,4,7,3,13,12,1,9]⟩,⟨32,257,![1,12,13,3,7,4,6,10,8]⟩,⟨272,160,![0,13,3,7,10,2,6,9,1]⟩]⟩
private theorem row2_cert : nearestStemCapsuleChecked row2 := by decide
private def row3 : NearestStemCapsule := ⟨⟨1,0,2,12⟩,[],[⟨0,73,![1,5,4,6,2,13,3,11,8]⟩,⟨0,261,![1,5,4,7,3,13,2,10,8]⟩,⟨0,131,![2,13,3,7,4,5,1,9,8]⟩,⟨0,390,![5,1,9,8,10,2,13,3,7]⟩,⟨0,11,![2,13,3,11,8,9,1,5,4]⟩,⟨0,13,![4,5,1,12,13,2,10,8,11]⟩]⟩
private theorem row3_cert : nearestStemCapsuleChecked row3 := by decide
private def row4 : NearestStemCapsule := ⟨⟨2,0,2,0⟩,[322,532],[⟨0,18,![5,1,9,8,0,13,12,2,6]⟩,⟨0,109,![1,5,4,6,2,10,8,11,3]⟩,⟨0,769,![4,7,3,11,8,10,2,12,13]⟩,⟨8,64,![1,5,11,8,0,13,12,2,6]⟩,⟨512,269,![1,5,4,7,11,8,10,2,12]⟩]⟩
private theorem row4_cert : nearestStemCapsuleChecked row4 := by decide
private def row5 : NearestStemCapsule := ⟨⟨2,0,2,2⟩,[],[⟨0,576,![1,13,12,2,6,4,7,3,11]⟩,⟨0,520,![2,12,13,1,5,4,7,3,11]⟩,⟨512,65,![1,13,12,2,6,4,7,11,8]⟩]⟩
private theorem row5_cert : nearestStemCapsuleChecked row5 := by decide
private def row6 : NearestStemCapsule := ⟨⟨2,0,2,8⟩,[],[⟨0,72,![1,5,4,6,2,12,13,3,11]⟩,⟨0,260,![1,5,4,7,3,13,12,2,10]⟩,⟨0,130,![2,12,13,3,7,4,5,1,9]⟩,⟨68,40,![0,13,3,11,6,2,10,5,1]⟩,⟨2,129,![2,12,13,3,7,4,5,9,8]⟩]⟩
private theorem row6_cert : nearestStemCapsuleChecked row6 := by decide
private def row7 : NearestStemCapsule := ⟨⟨2,0,2,10⟩,[],[⟨0,289,![1,13,3,7,4,6,2,10,8]⟩,⟨0,81,![4,6,2,12,13,1,9,8,11]⟩,⟨0,108,![5,1,13,3,11,8,10,2,6]⟩,⟨0,145,![2,6,4,7,3,13,1,9,8]⟩,⟨0,97,![1,13,3,11,8,10,2,6,4]⟩]⟩
private theorem row7_cert : nearestStemCapsuleChecked row7 := by decide

private theorem report1 (h9 : NoPath G 9) (D : Finset V) (p : Fin 4→V)
    (m : Fin 35) (F : Fin 12→V) (fi : Function.Injective F)
    (ports : ∀ i : Fin 4,F ⟨i.val,by omega⟩=p i)
    (outer : ∀ x : Fin 12,4≤x.val→F x∉D)
    (pure : ∀ x : Fin 12,4≤x.val→∀ y∈D,G.Adj (F x) y↔y=p ⟨x.val%4,by omega⟩)
    (fit : ∀ x y : Fin 12,G.Adj (F x) (F y)↔rawEdge (masks m) (TwoFan.castBase x) (TwoFan.castBase y)=true)
    (w : Fin 4→V) (wp : InducedPath G w) (wd : ∀ i,w i∈D)
    (w0 : w 0=p 1) (w3 : w 3=p 0)
    (mid : ∀ i : Fin 4, (0 : Nat) < (i : Nat) → (i : Nat) < 3 →∀ c,w i≠p c)
    (near : ∀ i : Fin 4, (i : Nat) < 3 →∀ c≠1,G.Adj (w i) (p c)→ (3 : Nat) ≤ (i : Nat) + 1) :
    masks m∈[168,532] ∧ ∀ i : Fin 4,i≠0→i≠1→¬G.Adj (p i) (w 2) := by
  by_cases one : G.Adj (p 2) (w 2)
  · by_cases two : G.Adj (p 3) (w 2)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row3 row3_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact (ni rfl).elim
          · exact ⟨fun _=>by decide,fun _=>one⟩
          · exact ⟨fun _=>by decide,fun _=>two⟩)
      exact False.elim (List.not_mem_nil r)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row1 row1_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact (ni rfl).elim
          · exact ⟨fun _=>by decide,fun _=>one⟩
          · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row1.spec.extraTail.testBit 3=true)) h).elim⟩)
      exact False.elim (List.not_mem_nil r)
  · by_cases two : G.Adj (p 3) (w 2)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row2 row2_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact (ni rfl).elim
          · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row2.spec.extraTail.testBit 2=true)) h).elim⟩
          · exact ⟨fun _=>by decide,fun _=>two⟩)
      exact False.elim (List.not_mem_nil r)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row0 row0_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact (ni rfl).elim
          · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 2=true)) h).elim⟩
          · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row0.spec.extraTail.testBit 3=true)) h).elim⟩)
      refine ⟨r,?_⟩
      intro i nz ni
      fin_cases i
      · exact (nz rfl).elim
      · exact (ni rfl).elim
      · exact one
      · exact two

private theorem report2 (h9 : NoPath G 9) (D : Finset V) (p : Fin 4→V)
    (m : Fin 35) (F : Fin 12→V) (fi : Function.Injective F)
    (ports : ∀ i : Fin 4,F ⟨i.val,by omega⟩=p i)
    (outer : ∀ x : Fin 12,4≤x.val→F x∉D)
    (pure : ∀ x : Fin 12,4≤x.val→∀ y∈D,G.Adj (F x) y↔y=p ⟨x.val%4,by omega⟩)
    (fit : ∀ x y : Fin 12,G.Adj (F x) (F y)↔rawEdge (masks m) (TwoFan.castBase x) (TwoFan.castBase y)=true)
    (w : Fin 4→V) (wp : InducedPath G w) (wd : ∀ i,w i∈D)
    (w0 : w 0=p 2) (w3 : w 3=p 0)
    (mid : ∀ i : Fin 4, (0 : Nat) < (i : Nat) → (i : Nat) < 3 →∀ c,w i≠p c)
    (near : ∀ i : Fin 4, (i : Nat) < 3 →∀ c≠2,G.Adj (w i) (p c)→ (3 : Nat) ≤ (i : Nat) + 1) :
    masks m∈[322,532] ∧ ∀ i : Fin 4,i≠0→i≠2→¬G.Adj (p i) (w 2) := by
  by_cases one : G.Adj (p 1) (w 2)
  · by_cases two : G.Adj (p 3) (w 2)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row7 row7_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact ⟨fun _=>by decide,fun _=>one⟩
          · exact (ni rfl).elim
          · exact ⟨fun _=>by decide,fun _=>two⟩)
      exact False.elim (List.not_mem_nil r)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row5 row5_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact ⟨fun _=>by decide,fun _=>one⟩
          · exact (ni rfl).elim
          · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row5.spec.extraTail.testBit 3=true)) h).elim⟩)
      exact False.elim (List.not_mem_nil r)
  · by_cases two : G.Adj (p 3) (w 2)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row6 row6_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row6.spec.extraTail.testBit 1=true)) h).elim⟩
          · exact (ni rfl).elim
          · exact ⟨fun _=>by decide,fun _=>two⟩)
      exact False.elim (List.not_mem_nil r)
    · have r := TwoFan.nearest_stem_mask_survives h9 D p row4 row4_cert m F fi ports outer pure fit
        (by decide) (by decide) (by decide) (by decide) w wp wd w0 w3 mid near (by
          intro i ni nz
          fin_cases i
          · exact (nz rfl).elim
          · exact ⟨fun h=>(one h).elim,fun h=>((by decide : ¬(row4.spec.extraTail.testBit 1=true)) h).elim⟩
          · exact (ni rfl).elim
          · exact ⟨fun h=>(two h).elim,fun h=>((by decide : ¬(row4.spec.extraTail.testBit 3=true)) h).elim⟩)
      refine ⟨r,?_⟩
      intro i nz ni
      fin_cases i
      · exact (nz rfl).elim
      · exact one
      · exact (ni rfl).elim
      · exact two

private theorem stem_profiles (p : Fin 4→V) (j : Fin 4) (j0 : j≠0) (w : Fin 4→V)
    (wp : InducedPath G w) (w0 : w 0=p j) (w3 : w 3=p 0)
    (near : ∀ i : Fin 4, (i : Nat) < 3 →∀ c≠j,G.Adj (w i) (p c)→ (3 : Nat) ≤ (i : Nat) + 1)
    (no : ∀ i : Fin 4,i≠0→i≠j→¬G.Adj (p i) (w 2)) :
    (∀ i,G.Adj (p i) (w 2)↔i=0) ∧ (∀ i,G.Adj (p i) (w 1)↔i=j) := by
  constructor
  · intro i
    constructor
    · intro a
      by_cases zi : i=0
      · exact zi
      by_cases ji : i=j
      · subst i
        have e : G.Adj (w 0) (w 2) := by simpa only [w0] using a
        have bad := (wp.2 0 2 (by decide)).mp e
        exact ((by decide : ¬ ((0:Nat)+1=2)) bad).elim
      exact (no i zi ji a).elim
    · rintro rfl
      rw [←w3,SimpleGraph.adj_comm]
      exact (wp.2 2 3 (by decide)).mpr (by decide)
  · intro i
    constructor
    · intro a
      by_cases eq : i=j
      · exact eq
      have h := near 1 (by decide) i eq a.symm
      exact ((by decide : ¬ (3≤(1:Nat)+1)) h).elim
    · rintro rfl
      rw [←w0]
      exact (wp.2 0 1 (by decide)).mpr (by decide)

/-- A pair of clean same-home fans forbids two length-three nearest core
stems incoming from distinct foreign labels 1 and 2. The nearest-stem
tie bits are allowed in the hypotheses and forced away by the certificates. -/
theorem two_nearest_three_edge_incoming_stems_or_induced_p9 (h4 : FourCycleFree G)
    (D : Finset V) (p : Fin 4→V) (A : Finset V) (f : V→Fin 4→V)
    (H : PortFanFamily G (D : Set V) p A f)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (q r : V) (qm : q∈A) (rm : r∈A) (qr : q≠r)
    (one : IsNearestPortStem (G:=G) D p 1 0 3)
    (two : IsNearestPortStem (G:=G) D p 2 0 3) :
    ∃ path : Fin 9→V, InducedPath G path := by
  by_cases path : ∃ path : Fin 9→V,InducedPath G path
  · exact path
  have noP9 : NoPath G 9 := path
  obtain ⟨m,F,fi,ports,outer,pure,fit⟩ := TwoFan.normalize h4 H ind q r qm rm qr
  obtain ⟨w,wp,wd,w0,w3,wm,wn⟩ := one
  obtain ⟨z,zp,zd,z0,z3,zm,zn⟩ := two
  obtain ⟨r1,off1⟩ := report1 noP9 D p m F fi ports outer pure fit w wp wd w0 w3 wm wn
  obtain ⟨r2,off2⟩ := report2 noP9 D p m F fi ports outer pure fit z zp zd z0 z3 zm zn
  have r532 : masks m=532 := by
    rcases List.mem_cons.mp r1 with bad|g
    · exact ((by decide : (168 : Nat)∉[322,532]) (bad ▸ r2)).elim
    · exact List.mem_singleton.mp g
  have base : ∀ i j, G.Adj (F i) (F j)↔
      rawEdge 532 (DoubleStemSix.insideBase i) (DoubleStemSix.insideBase j)=true := by
    intro i j
    rw [←r532]
    exact fit i j
  obtain ⟨a,b⟩ := stem_profiles p 1 (by decide) w wp w0 w3 wn off1
  obtain ⟨c,d⟩ := stem_profiles p 2 (by decide) z zp z0 z3 zn off2
  exact DoubleStemSix.mask532_double_stem_forces_induced_p9 h4 (D : Set V) p F fi ports outer pure base
    (w 2) (w 1) (z 2) (z 1) (wd _) (wd _) (zd _) (zd _)
    (wm _ (by decide) (by decide)) (wm _ (by decide) (by decide))
    (zm _ (by decide) (by decide)) (zm _ (by decide) (by decide))
    a b c d ((wp.2 1 2 (by decide)).mpr (by decide)).symm
    ((zp.2 1 2 (by decide)).mpr (by decide)).symm

#print axioms two_nearest_three_edge_incoming_stems_or_induced_p9
end Graffiti133P5CliqueArms.TwoIncomingNearest
