import P8ModelLift133

namespace Graffiti133DominatingHex
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000
set_option maxRecDepth 20000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Frame (G : SimpleGraph V) extends Hole G 6 where
  h4 : FourCycleFree G
  no8 : ¬∃ p : Fin 8 → V, InducedPath G p
  dom : ∀ x, Outside c x → ∃ i, G.Adj x (c i)

namespace Frame
variable (F : Frame G)

def Single (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i
def Double (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i ∨ j=i+1

def frontInd (i : Fin 3) : Fin 6 := i.castLE (by decide)
def Opp (x : V) (i : Fin 3) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=frontInd i ∨ j=frontInd i+3

def Near (x : V) : Prop := Outside F.c x ∧ ∃ i, G.Adj x (F.c i)
def Far (x : V) : Prop := Outside F.c x ∧ ∀ i, ¬G.Adj x (F.c i)

lemma near_not_far {x : V} (hn : F.Near x) (hf : F.Far x) : False := by
  obtain ⟨i,hi⟩ := hn.2
  exact hf.2 i hi

private lemma allowed6 : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j=true ↔ j=i) ∨ (∃ i, ∀ j, b j=true ↔ j=i ∨ j=i+1) ∨
      (∃ i : Fin 3, ∀ j, b j=true ↔ j=frontInd i ∨ j=frontInd i+3) := by decide

private lemma step6 : ∀ i : Fin 6, Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ i≠i+2 := by decide

theorem classify {x : V} (hx : F.Near x) :
    (∃ i, F.Single x i) ∨ (∃ i, F.Double x i) ∨ ∃ i, F.Opp x i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 6) (h : b i=true) : b (i+2)=false := by
    cases he : b (i+2)
    · rfl
    · have t := step6 i
      have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
        (fun e => t.2.2 (F.inj e)) ((bt _).mp h).symm ((bt _).mp he).symm
        ((F.adj _ _).mpr t.1) ((F.adj _ _).mpr t.2.1).symm
      exact (hx.1 _ eq).elim
  obtain ⟨i,hi⟩ := hx.2
  rcases allowed6 b sep ⟨i,(bt _).mpr hi⟩ with a | a | a
  · obtain ⟨j,hj⟩ := a
    exact Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inr ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)

theorem contact_forbid {x y : V} (hx : Outside F.c x) (hy : Outside F.c y)
    (e : G.Adj x y) {i j : Fin 6} (ex : G.Adj x (F.c i)) (ey : G.Adj y (F.c j)) :
    ¬Cyclic i j := by
  intro ed
  have h := F.h4 x (F.c j) y (F.c i) (hx j) e ey.symm ex ((F.adj _ _).mpr ed).symm
  exact hy _ h

theorem stamp_uniq {x y z : V} {i : Fin 6} (hx : x ≠ F.c i)
    (ex : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (hy : y = F.c i ∨ G.Adj y (F.c i)) (hz : z = F.c i ∨ G.Adj z (F.c i)) :
    y=z := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact hy.trans hz.symm
  · exact (no (hy.symm ▸ hz.symm)).elim
  · exact (no (hz.symm ▸ hy)).elim
  · exact F.h4 x (F.c i) y z hx ex hy.symm ez hz.symm


theorem exists_cycle {x : V} (hx : ¬Outside F.c x) : ∃ i, x=F.c i := by
  apply Classical.byContradiction
  intro no
  exact hx (fun i e => no ⟨i,e⟩)

theorem cycle_adj (i j : Fin 6) (h : Cyclic i j) : G.Adj (F.c i) (F.c j) :=
  (F.adj _ _).mpr h

private lemma cycle_path_at_most_two : ∀ i j : Fin 6, j≠i+3 →
    i=j ∨ Cyclic i j ∨ ∃ k, Cyclic i k ∧ Cyclic k j := by decide
private lemma cycle_path_three : ∀ i : Fin 6,
    Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by decide
private lemma cycle_neighbors : ∀ i j : Fin 6, Cyclic i j ↔ j=i+1 ∨ j=i+5 := by decide
private lemma cycle_distinct : ∀ i j : Fin 6, Cyclic i j → i≠j := by decide
private lemma cycle_step : ∀ i : Fin 6, Cyclic i (i+1) := by decide

theorem cycle_dist_two (hc : G.Connected) {i j : Fin 6} (h : j≠i+3) :
    G.dist (F.c i) (F.c j) ≤ 2 := by
  rcases cycle_path_at_most_two i j h with rfl | e | ⟨k,e1,e2⟩
  · simpa only [dist_self] using Nat.zero_le 2
  · rw [dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ e)]
    decide
  · have L := hc.dist_triangle (u:=F.c i) (v:=F.c k) (w:=F.c j)
    rw [dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ e1),
      dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ e2)] at L
    exact L

theorem cycle_dist_three (hc : G.Connected) (i j : Fin 6) :
    G.dist (F.c i) (F.c j) ≤ 3 := by
  by_cases h : j=i+3
  · subst j
    have eq : i+2 ≠ i+3 := (by decide : ∀ i : Fin 6, i+2≠i+3) i
    have L := F.cycle_dist_two hc eq
    have tri := hc.dist_triangle (u:=F.c i) (v:=F.c (i+2)) (w:=F.c (i+3))
    rw [dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ (cycle_path_three i).2.2)] at tri
    omega
  · exact (F.cycle_dist_two hc h).trans (by decide)

private theorem radius_to (G : SimpleGraph V) (v : V) (k : ℕ) (h : ∀ w,G.dist v w≤k) :
    radius G ≤ k := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  have hs : Finset.univ.sup (G.dist v) ≤ k := Finset.sup_le_iff.mpr (fun w _ => h w)
  cases eq : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have h' : d ≤ Finset.univ.sup (G.dist v) := by simpa [eq] using hl
    exact h'.trans hs

/-- An opposite spoke supplies a radius-three center when C6 dominates. -/
theorem radius_three_of_opp (hc : G.Connected) {x : V} {i : Fin 3} (hx : F.Opp x i) :
    radius G ≤ 3 := by
  have all (j : Fin 6) : G.dist (F.c (frontInd i)) (F.c j)≤2 := by
    by_cases eq : j=frontInd i+3
    · subst j
      have h := hc.dist_triangle (u:=F.c (frontInd i)) (v:=x) (w:=F.c (frontInd i+3))
      rw [dist_eq_one_iff_adj.mpr ((hx.2 _).mpr (Or.inl rfl)).symm,
        dist_eq_one_iff_adj.mpr ((hx.2 _).mpr (Or.inr rfl))] at h
      exact h
    · exact F.cycle_dist_two hc eq
  apply radius_to G (F.c (frontInd i)) 3
  intro y
  by_cases out : Outside F.c y
  · obtain ⟨j,e⟩ := F.dom y out
    have hh := all j
    have h := hc.dist_triangle (u:=F.c (frontInd i)) (v:=F.c j) (w:=y)
    rw [dist_eq_one_iff_adj.mpr e.symm] at h
    omega
  · obtain ⟨j,rfl⟩ := F.exists_cycle out
    exact (all j).trans (by decide)

theorem only_single_double (hc : G.Connected) (hr : 3 < radius G) {x : V}
    (out : Outside F.c x) : (∃ i,F.Single x i) ∨ (∃ i,F.Double x i) := by
  rcases F.classify ⟨out,F.dom x out⟩ with s | d | ⟨i,h⟩
  · exact Or.inl s
  · exact Or.inr d
  · exact (Nat.not_le_of_gt hr (F.radius_three_of_opp hc h)).elim

def Witness (x : V) (i : Fin 6) : Prop :=
  F.Single x i ∧ 3 < G.dist (F.c (i+3)) x

theorem exists_witness (hc : G.Connected) (hr : 3 < radius G) (i : Fin 6) :
    ∃ x,F.Witness x i := by
  classical
  have wx : ∃ x, 3 < G.dist (F.c (i+3)) x := by
    apply Classical.byContradiction
    intro no
    exact Nat.not_le_of_gt hr (radius_to G (F.c (i+3)) 3
      (fun x => Nat.le_of_not_gt (fun h => no ⟨x,h⟩)))
  obtain ⟨x,dx⟩ := wx
  have off : Outside F.c x := by
    intro j e
    exact Nat.not_le_of_gt dx (e.symm ▸ F.cycle_dist_three hc (i+3) j)
  have root (j : Fin 6) (e : G.Adj x (F.c j)) : j=i := by
    by_contra ne
    have test : ∀ i j : Fin 6, j≠i → j≠(i+3)+3 := by decide
    have d := F.cycle_dist_two hc (test i j ne)
    have tri := hc.dist_triangle (u:=F.c (i+3)) (v:=F.c j) (w:=x)
    rw [dist_eq_one_iff_adj.mpr e.symm] at tri
    omega
  obtain ⟨j,e⟩ := F.dom x off
  refine ⟨x,⟨off,fun k => ?_⟩,dx⟩
  exact ⟨root k,fun h => h.symm ▸ (root j e ▸ e)⟩

private lemma near_or_same : ∀ i j : Fin 6, ¬Cyclic i j → (j≠i+3) →
    ¬Cyclic (i+3) j → j=i := by decide

theorem witness_contact (hc : G.Connected) {x y : V} {i j : Fin 6}
    (wx : F.Witness x i) (oy : Outside F.c y) (a : G.Adj x y)
    (b : G.Adj y (F.c j)) : j=i := by
  have n1 := F.contact_forbid wx.1.1 oy a ((wx.1.2 i).mpr rfl) b
  have lo : G.dist (F.c (i+3)) (F.c j) ≤ 1 → False := by
    intro d
    have h := hc.dist_triangle (u:=F.c (i+3)) (v:=F.c j) (w:=y)
    have k := hc.dist_triangle (u:=F.c (i+3)) (v:=y) (w:=x)
    rw [dist_eq_one_iff_adj.mpr b.symm] at h
    rw [dist_eq_one_iff_adj.mpr a.symm] at k
    have far := wx.2
    omega
  have n2 : j≠i+3 := by
    intro e
    subst j
    exact lo (by simpa only [dist_self] using Nat.zero_le 1)
  have n3 : ¬Cyclic (i+3) j := fun e => lo (dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ e)).le
  exact near_or_same i j n1 n2 n3

open Graffiti133P8Heawood
open Graffiti133Eighth

private def baseEdges : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(1,7),(2,8),(3,9),(4,10),(5,11)]
private def Base : Fin 12 → Fin 12 → Prop := edgeRel baseEdges
private instance : DecidableRel Base := inferInstanceAs (DecidableRel (edgeRel baseEdges))
private def site (t : Fin 5) : Fin 6 := ![2,3,4,2,3] t
private def siteMask (t : Fin 5) (j : Fin 6) : Bool :=
  decide (j=site t ∨ (3≤t.val ∧ j=site t+1))
private def xMask (b : Bool) (i : Fin 12) : Bool :=
  if i.val=0 then true else if i.val=6 then b else false
private def yMask (t : Fin 5) (b : Bool) (i : Fin 13) : Bool :=
  if hi : i.val < 6 then siteMask t ⟨i.val,hi⟩
  else if i.val=12 then true
  else if t.val < 3 ∧ i.val=6+(site t).val then b else false
private def testModel (t : Fin 5) (a b : Bool) : Fin 14 → Fin 14 → Prop :=
  ext (ext Base (xMask a)) (yMask t b)
private instance (t : Fin 5) (a b : Bool) : DecidableRel (testModel t a b) :=
  inferInstanceAs (DecidableRel (ext (ext Base (xMask a)) (yMask t b)))

private def p8 (t : Fin 5) (a : Bool) : Fin 8 → Fin 14 :=
  match t.val with
  | 0 => if a then ![6,12,13,2,3,4,5,11] else ![6,0,12,13,2,3,4,10]
  | 1 => ![7,1,0,12,13,3,4,10]
  | 2 => if a then ![6,12,13,4,3,2,1,7] else ![6,0,12,13,4,3,2,8]
  | 3 => ![7,1,0,12,13,3,4,10]
  | _ => ![8,2,1,0,12,13,4,10]

private lemma test_cert : ∀ (t : Fin 5) (a b : Bool),
    (Cert.eight (p8 t a)).Valid (testModel t a b) False := by decide

private lemma base_cc : ∀ i j : Fin 6, Base (i.castAdd 6) (j.castAdd 6) ↔ Cyclic i j := by decide
private lemma base_cw : ∀ i j : Fin 6, Base (i.castAdd 6) (j.natAdd 6) ↔ i=j := by decide
private lemma base_wc : ∀ i j : Fin 6, Base (i.natAdd 6) (j.castAdd 6) ↔ j=i := by decide
private lemma base_ww : ∀ i j : Fin 6, ¬Base (i.natAdd 6) (j.natAdd 6) := by decide

private def baseModel (hc : G.Connected) (w : Fin 6 → V) (hw : ∀ i,F.Witness (w i) i) :
    Model G Base where
  f := fun i => @Fin.addCases 6 6 (fun _ => V) F.c w i
  inj := by
    intro i j
    refine Fin.addCases (m:=6) (n:=6) ?_ ?_ i
    · intro i
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro j e
        exact congrArg (Fin.castAdd 6) (F.inj (by simpa only [Fin.addCases_left] using e))
      · intro j e
        exact ((hw j).1.1 i (by simpa only [Fin.addCases_left,Fin.addCases_right] using e.symm)).elim
    · intro i
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro j e
        exact ((hw i).1.1 j (by simpa only [Fin.addCases_left,Fin.addCases_right] using e)).elim
      · intro j e
        have eq : w i=w j := by simpa only [Fin.addCases_right] using e
        exact congrArg (Fin.natAdd 6) ((hw j).1.2 i |>.mp (eq ▸ ((hw i).1.2 i).mpr rfl))
  adj := by
    intro i j
    refine Fin.addCases (m:=6) (n:=6) ?_ ?_ i
    · intro i
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro j
        simpa only [Fin.addCases_left] using (base_cc i j).trans (F.adj i j).symm
      · intro j
        simp only [Fin.addCases_left,Fin.addCases_right]
        rw [G.adj_comm]
        exact (base_cw i j).trans ((hw j).1.2 i).symm
    · intro i
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro j
        simpa only [Fin.addCases_left,Fin.addCases_right] using (base_wc i j).trans ((hw i).1.2 j).symm
      · intro j
        simp only [Fin.addCases_right]
        apply iff_of_false (base_ww i j)
        intro e
        have he : j=i := F.witness_contact hc (hw i) (hw j).1.1 e (((hw j).1.2 j).mpr rfl)
        subst j
        exact G.loopless _ e

private lemma profile_case : ∀ b : Fin 6 → Bool,
    b 0=false → b 1=false → b 5=false →
    ((∃ i,∀ j,b j=true ↔ j=i) ∨ (∃ i,∀ j,b j=true ↔ j=i ∨ j=i+1)) →
    ∃ t : Fin 5, ∀ j,siteMask t j=b j := by decide

private theorem exterior_profile (hc : G.Connected) (hr : 3 < radius G) {x y : V}
    (sx : F.Single x 0) (oy : Outside F.c y) (ed : G.Adj x y) (ny : ¬G.Adj y (F.c 0)) :
    ∃ t : Fin 5, ∀ j,siteMask t j=true ↔ G.Adj y (F.c j) := by
  classical
  let b (j : Fin 6) := decide (G.Adj y (F.c j))
  have bb (j : Fin 6) : b j=true ↔ G.Adj y (F.c j) := by simp [b]
  have np (j : Fin 6) (p : Cyclic 0 j) : b j=false := Bool.eq_false_iff.mpr (fun e =>
    F.contact_forbid sx.1 oy ed ((sx.2 _).mpr rfl) ((bb j).mp e) p)
  have sh : (∃ i,∀ j,b j=true ↔ j=i) ∨ (∃ i,∀ j,b j=true ↔ j=i ∨ j=i+1) := by
    rcases F.only_single_double hc hr oy with ⟨i,h⟩ | ⟨i,h⟩
    · exact Or.inl ⟨i,fun j => (bb j).trans (h.2 j)⟩
    · exact Or.inr ⟨i,fun j => (bb j).trans (h.2 j)⟩
  obtain ⟨t,h⟩ := profile_case b (Bool.eq_false_iff.mpr (fun e => ny ((bb _).mp e)))
    (np 1 (by decide)) (np 5 (by decide)) sh
  exact ⟨t,fun j => h j ▸ bb j⟩

private lemma profile_singleton_check : ∀ (t : Fin 5) (i : Fin 6),
    (∀ j,siteMask t j=true ↔ j=i) → t.val < 3 ∧ i=site t := by decide
private lemma all_not_root : ∀ t : Fin 5, siteMask t 0=false := by decide
private lemma mask_base_x : ∀ (a : Bool) (i : Fin 6), xMask a (i.castAdd 6)=decide (i=0) := by decide
private lemma mask_base_w : ∀ (a : Bool) (i : Fin 6), xMask a (i.natAdd 6)=(if i=0 then a else false) := by decide
private lemma mask_add_c : ∀ (t : Fin 5) (b : Bool) (i : Fin 6),
    yMask t b (i.castAdd 6).castSucc=siteMask t i := by decide
private lemma mask_add_w : ∀ (t : Fin 5) (b : Bool) (i : Fin 6),
    yMask t b (i.natAdd 6).castSucc=(if t.val < 3 ∧ i=site t then b else false) := by decide
private lemma mask_add_last : ∀ (t : Fin 5) (b : Bool), yMask t b (Fin.last 12)=true := by decide

/-- A singleton in the radius-four geometry has no exterior edge to a
vertex that misses its anchor. The certificate is the 7 explicit P8s. -/
theorem singleton_neighbors_zero (hc : G.Connected) (hr : 3 < radius G) {x y : V}
    (sx : F.Single x 0) (oy : Outside F.c y) (ed : G.Adj x y) : G.Adj y (F.c 0) := by
  classical
  apply Classical.byContradiction
  intro ny
  obtain ⟨t,ht⟩ := F.exterior_profile hc hr sx oy ed ny
  choose w hw using F.exists_witness hc hr
  let M := F.baseModel hc w hw
  have cMap (i : Fin 6) : M.f (i.castAdd 6)=F.c i := by simp only [M,baseModel,Fin.addCases_left]
  have wMap (i : Fin 6) : M.f (i.natAdd 6)=w i := by simp only [M,baseModel,Fin.addCases_right]
  have xoff (i : Fin 6) : x≠w i := by
    intro eq
    have ei : (0:Fin 6)=i := (hw i).1.2 0 |>.mp (eq ▸ ((sx.2 0).mpr rfl))
    obtain ⟨j,ej⟩ := F.dom y oy
    have eJ : j=i := F.witness_contact hc (eq.symm ▸ hw i) oy ed ej
    exact ny ((eJ.trans ei.symm) ▸ ej)
  have yoff (i : Fin 6) : y≠w i := by
    intro eq
    have ei : (0:Fin 6)=i := F.witness_contact hc (eq.symm ▸ hw i) sx.1 ed.symm ((sx.2 0).mpr rfl)
    exact ny (ei.symm ▸ (eq.symm ▸ ((hw i).1.2 i).mpr rfl))
  let a := decide (G.Adj x (w 0))
  let b := decide (G.Adj y (w (site t)))
  have xFresh : M.Fresh x := by
    intro i
    refine Fin.addCases (m:=6) (n:=6) ?_ ?_ i
    · intro j; rw [cMap]; exact sx.1 j
    · intro j; rw [wMap]; exact xoff j
  have xHit (i : Fin 12) : xMask a i=true ↔ G.Adj x (M.f i) := by
    refine Fin.addCases (m:=6) (n:=6) ?_ ?_ i
    · intro j; rw [cMap,mask_base_x,decide_eq_true_eq,sx.2]
    · intro j
      rw [wMap,mask_base_w]
      by_cases eq : j=0
      · subst j; simp [a]
      · have ee : ¬G.Adj x (w j) := fun e => eq
          (F.witness_contact hc (hw j) sx.1 e.symm ((sx.2 0).mpr rfl)).symm
        simp [eq,ee]
  let T := M.extend x xFresh xHit
  have yFresh : T.Fresh y := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [T,Model.extend_f_new] using ed.ne.symm
    · rw [show T.f j.castSucc=M.f j from M.extend_f_old x xFresh xHit j]
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro i; rw [cMap]; exact oy i
      · intro i; rw [wMap]; exact yoff i
  have yHit (i : Fin 13) : yMask t b i=true ↔ G.Adj y (T.f i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [mask_add_last,T,Model.extend_f_new,ed.symm,iff_true]
    · rw [show T.f j.castSucc=M.f j from M.extend_f_old x xFresh xHit j]
      refine Fin.addCases (m:=6) (n:=6) ?_ ?_ j
      · intro i; rw [cMap,mask_add_c]; exact ht i
      · intro i
        rw [wMap,mask_add_w]
        by_cases ok : t.val < 3 ∧ i=site t
        · have e := ok.2
          rw [if_pos ok,e]
          simp [b]
        · have no : ¬G.Adj y (w i) := by
            intro yW
            have loc (j : Fin 6) (ej : G.Adj y (F.c j)) : j=i :=
              F.witness_contact hc (hw i) oy yW.symm ej
            obtain ⟨j,e⟩ := F.dom y oy
            have snd : ∀ j,siteMask t j=true ↔ j=i :=
              fun j => ⟨fun h => loc j ((ht j).mp h),fun h => (ht j).mpr (h.symm ▸ (loc _ e ▸ e))⟩
            exact ok (profile_singleton_check t i snd)
          simp [ok,no]
  let U := T.extend y yFresh yHit
  have cv := test_cert t a b
  apply F.no8
  exact ⟨U.f ∘ p8 t a,U.inj.comp (fun {_ _} => cv.1 _ _),
    fun i j h => (U.adj _ _).symm.trans (cv.2 _ _ h)⟩

private lemma rotate_inj (a : Fin 6) : Function.Injective (fun j : Fin 6 => a+j) := by
  intro u v h
  have h' : ∀ a u v : Fin 6, a+u=a+v → u=v := by decide
  exact h' a u v h
private lemma rotate_rel : ∀ a i j : Fin 6, Cyclic (a+i) (a+j) ↔ Cyclic i j := by decide
private lemma rotate_surj : ∀ a j : Fin 6, ∃ i, a+i=j := by decide
private lemma rotate_center : ∀ a j : Fin 6, a+j=a ↔ j=0 := by decide

private def rotated (a : Fin 6) : Frame G where
  c := fun j => F.c (a+j)
  inj := F.inj.comp (rotate_inj a)
  adj i j := (F.adj _ _).trans (rotate_rel _ _ _)
  h4 := F.h4
  no8 := F.no8
  dom := by
    intro x out
    have off (j : Fin 6) : x≠F.c j := by
      obtain ⟨i,hi⟩ := rotate_surj a j
      exact hi ▸ out i
    obtain ⟨j,e⟩ := F.dom x off
    obtain ⟨i,hi⟩ := rotate_surj a j
    exact ⟨i,hi.symm ▸ e⟩

theorem singleton_neighbors (hc : G.Connected) (hr : 3 < radius G) {x y : V} {i : Fin 6}
    (sx : F.Single x i) (oy : Outside F.c y) (exy : G.Adj x y) : G.Adj y (F.c i) := by
  let H := F.rotated i
  have hs : H.Single x 0 := by
    refine ⟨fun j => sx.1 _,fun j => ?_⟩
    change G.Adj x (F.c (i+j)) ↔ j=0
    exact (sx.2 _).trans (rotate_center _ _)
  have hy : Outside H.c y := fun j => oy _
  have h := H.singleton_neighbors_zero hc hr hs hy exy
  change G.Adj y (F.c (i+0)) at h
  simpa using h

theorem local_single_bound (hc : G.Connected) (hr : 3 < radius G) {x : V} {i : Fin 6}
    (hx : F.Single x i) : localIndependence G x≤1 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have seat (u : V) (hu : u∈A) : u=F.c i ∨ G.Adj u (F.c i) := by
    by_cases off : Outside F.c u
    · exact Or.inr (F.singleton_neighbors hc hr hx off (hN _ hu))
    · obtain ⟨j,rfl⟩ := F.exists_cycle off
      exact Or.inl (congrArg F.c ((hx.2 j).mp (hN _ hu)))
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact F.stamp_uniq (hx.1 i) (hN _ ha) (hN _ hb) (hI _ ha _ hb) (seat _ ha) (seat _ hb)

private lemma double_seats : ∀ i j : Fin 6, ¬Cyclic i j → ¬Cyclic (i+1) j →
    j=i+3 ∨ j=i+4 := by decide

theorem local_double_bound {x : V} {i : Fin 6} (hx : F.Double x i) :
    localIndependence G x≤3 := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let T : Finset (Fin 6) := {i,i+3,i+4}
  have seat (y : V) (hy : y∈A) : ∃ j ∈ T, y=F.c j ∨ G.Adj y (F.c j) := by
    have e := hN _ hy
    by_cases out : Outside F.c y
    · obtain ⟨j,hj⟩ := F.dom y out
      have hj1 := F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj
      have hj2 := F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj
      rcases double_seats i j hj1 hj2 with rfl | rfl
      · exact ⟨i+3,by simp [T],Or.inr hj⟩
      · exact ⟨i+4,by simp [T],Or.inr hj⟩
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      refine ⟨i,by simp [T],?_⟩
      rcases (hx.2 j).mp e with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ((F.adj _ _).mpr (cycle_step i)).symm
  let f (y : V) := if h : y∈A then Classical.choose (seat y h) else i
  have hs {y : V} (h : y∈A) : f y∈T ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inj : Set.InjOn f (↑A : Set V) := by
    intro y hy z hz he
    exact F.stamp_uniq (hx.1 (f y)) (hN _ hy) (hN _ hz) (hI _ hy _ hz)
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)
  exact eq ▸ (Finset.card_le_card_of_injOn f (fun _ h => (hs h).1) inj).trans hT

private def Stamp (y : V) (j : Fin 6) : Prop :=
  y = F.c j ∨ (Outside F.c y ∧ G.Adj y (F.c j))

private theorem stamp_single {x y z : V} {j : Fin 6} (hne : x ≠ F.c j)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (sy : F.Stamp y j) (sz : F.Stamp z j) : y = z := by
  refine F.stamp_uniq hne ey ez no ?_ ?_
  · exact sy.imp id (fun h => h.2)
  · exact sz.imp id (fun h => h.2)

private noncomputable def singleSite (F : Frame G) (i : Fin 6) : Finset V := by
  classical exact Finset.univ.filter (fun x => F.Single x i)

private lemma site_mem (F : Frame G) {i : Fin 6} {x : V} :
    x ∈ singleSite F i ↔ F.Single x i := by
  classical simp [singleSite]

private theorem local_cycle_bound (F : Frame G) (hc : G.Connected)
    (hr : 3 < radius G) (i : Fin 6) :
    localIndependence G (F.c i) ≤ 2 + (singleSite F i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A \ singleSite F i
  let seats : Finset (Fin 6) := {i+1,i+5}
  have label (w : V) (hw : w ∈ B) : ∃ j, Cyclic i j ∧ F.Stamp w j := by
    have e := hN w (Finset.mem_sdiff.mp hw).1
    by_cases out : Outside F.c w
    · rcases F.only_single_double hc hr out with ⟨j,hj⟩ | ⟨j,hj⟩
      · have he := (hj.2 i).mp e.symm
        exact ((Finset.mem_sdiff.mp hw).2 ((site_mem F).mpr (he.symm ▸ hj))).elim
      · rcases (hj.2 i).mp e.symm with he | he
        · have m : Cyclic i (j+1) := (cycle_neighbors _ _).mpr (Or.inl (by rw [he]))
          exact ⟨j+1,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inr rfl)⟩⟩
        · have m : Cyclic i j := (cyclic_symm _ _).mpr ((cycle_neighbors _ _).mpr (Or.inl he))
          exact ⟨j,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inl rfl)⟩⟩
    · obtain ⟨j,hj⟩ : ∃ j, w = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j eq => no ⟨j,eq⟩)
      exact ⟨j,(F.adj _ _).mp (hj ▸ e),Or.inl hj⟩
  let f (w : V) := if hw : w ∈ B then Classical.choose (label w hw) else i
  have fs (w : V) (hw : w ∈ B) : Cyclic i (f w) ∧ F.Stamp w (f w) := by
    simpa only [f,dif_pos hw] using Classical.choose_spec (label w hw)
  have hf (w : V) (hw : w ∈ B) : f w ∈ seats := by
    simpa [seats] using (cycle_neighbors _ _).mp (fs w hw).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz e
    have hyA := (Finset.mem_sdiff.mp hy).1
    have hzA := (Finset.mem_sdiff.mp hz).1
    have ne : F.c i ≠ F.c (f y) := F.inj.ne (cycle_distinct _ _ (fs y hy).1)
    exact F.stamp_single ne (hN _ hyA) (hN _ hzA) (hI _ hyA _ hzA)
      (fs y hy).2 (e.symm ▸ (fs z hz).2)
  have cb : B.card ≤ 2 := (Finset.card_le_card_of_injOn f hf inj).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  have hInt := Finset.card_le_card (show A ∩ singleSite F i ⊆ singleSite F i from Finset.inter_subset_right)
  have hC : B.card + (A ∩ singleSite F i).card = A.card := Finset.card_sdiff_add_card_inter A _
  omega


private noncomputable def singles (F : Frame G) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, F.Single x i)

private lemma singles_iff (F : Frame G) (x : V) :
    x ∈ singles F ↔ ∃ i, F.Single x i := by classical simp [singles]

private noncomputable def core (F : Frame G) : Finset V := by
  classical
  exact (Finset.univ : Finset (Fin 6)).image F.c

private noncomputable def fSite (F : Frame G) (x : V) : Fin 6 := by
  classical exact if h : ∃ i, F.Single x i then Classical.choose h else 0

private theorem sum_sites (F : Frame G) : (∑ i, (singleSite F i).card) = (singles F).card := by
  classical
  have fiber (i : Fin 6) : singleSite F i = (singles F).filter (fun x => fSite F x = i) := by
    ext x
    rw [site_mem,Finset.mem_filter]
    have fvalid (h : x ∈ singles F) : F.Single x (fSite F x) := by
      have q := (singles_iff F x).mp h
      unfold fSite
      rw [dif_pos q]
      exact Classical.choose_spec q
    refine ⟨?_,fun ⟨h,he⟩ => he ▸ fvalid h⟩
    intro h
    have hS := (singles_iff F x).mpr ⟨i,h⟩
    exact ⟨hS,(h.2 _).mp (((fvalid hS).2 _).mpr rfl)⟩
  simpa only [fiber] using
    (Finset.card_eq_sum_card_fiberwise (s:=singles F) (t:=Finset.univ)
      (f:=fSite F) (fun _ _ => Finset.mem_univ _)).symm

private noncomputable def charge (F : Frame G) (x : V) : ℕ := by
  classical exact ∑ i : Fin 6, if x = F.c i then (singleSite F i).card else 0

private noncomputable def fee (F : Frame G) (x : V) : ℕ := by
  classical exact if x ∈ core F ∪ singles F then 1 else 0

/-- A dominating induced hexagon imposes a strict density bound in the
ordinary-C4-free induced-P8-free class at radius at least four: sum of local independence plus six is at
most three times the order. -/
theorem hex_budget (F : Frame G) (conn : G.Connected) (hr : 3 < radius G) :
    (∑ x, localIndependence G x) + 6 ≤ 3 * Fintype.card V := by
  classical
  have pointwise (x : V) : localIndependence G x + fee F x ≤ 3 + charge F x := by
    by_cases out : Outside F.c x
    · have b : fee F x ≤ 1 := by
        unfold fee
        split <;> omega
      rcases F.only_single_double conn hr out with ⟨i,h⟩ | ⟨i,h⟩
      · have l := F.local_single_bound conn hr h
        omega
      · have l := F.local_double_bound h
        have zz : fee F x=0 := by
          unfold fee
          apply if_neg
          intro hmem
          rcases Finset.mem_union.mp hmem with cc | ss
          · obtain ⟨j,_,he⟩ := Finset.mem_image.mp cc
            exact out j he.symm
          · obtain ⟨j,hj⟩ := (singles_iff F x).mp ss
            have q : i=j := (hj.2 _).mp ((h.2 _).mpr (Or.inl rfl))
            have r : i+1=j := (hj.2 _).mp ((h.2 _).mpr (Or.inr rfl))
            exact (by decide : ∀ i : Fin 6, i≠i+1) i (q.trans r.symm)
        omega
    · obtain ⟨i,e⟩ : ∃ i, x = F.c i := by
        apply Classical.byContradiction
        intro no
        exact out fun j e => no ⟨j,e⟩
      have hL := local_cycle_bound F conn hr i
      rw [← e] at hL
      have hl : (singleSite F i).card ≤ charge F x := by
        have hh := Finset.single_le_sum (f := fun j : Fin 6 =>
          if x = F.c j then (singleSite F j).card else 0) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        simpa [charge,e] using hh
      have b : fee F x ≤ 1 := by
        unfold fee
        split <;> omega
      omega
  have disj : Disjoint (core F) (singles F) := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,_,e⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi⟩ := (singles_iff F x).mp hs
    exact hi.1 a e.symm
  have hc : (core F).card = 6 := by
    unfold core
    rw [Finset.card_image_of_injective _ F.inj]
    simp
  have hfee : (∑ x, fee F x) = 6+(singles F).card := by
    have hF : (Finset.univ : Finset V).filter (fun x => x ∈ core F ∪ singles F) = core F ∪ singles F := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [fee,Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,
      Nat.cast_id,mul_one,mul_zero,add_zero,hF,Finset.card_union_of_disjoint disj,hc]
  have hcharge : (∑ x, charge F x) = (singles F).card := by
    unfold charge
    rw [Finset.sum_comm]
    simp [sum_sites F]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => pointwise x)
  have hu : (∑ x, localIndependence G x) + (6+(singles F).card) ≤
      3*Fintype.card V + (singles F).card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hfee,hcharge,
      Nat.mul_comm] using h
  omega

private def path6 (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6,i.castSucc,(i+(if positive then 1 else 5)).castSucc,
    (i+(if positive then 2 else 4)).castSucc,(i+3).castSucc,
    (i+(if positive then 4 else 2)).castSucc]

private lemma normal6 : ∀ b : Fin 6 → Bool,
    ((∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i, ∀ j,b j=true ↔ j=i ∨ j=i+1)) →
    ∃ i pos,
      (∀ a c : Fin 6,path6 i pos a=path6 i pos c → a=c) ∧
      (∀ a c : Fin 6,a < c → (ext (@Cyclic 6) b (path6 i pos a) (path6 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 6,0 < a.val → (path6 i pos a).val < 6) := by decide


theorem P6_of_single_or_double {x : V} (hx : Outside F.c x)
    (kind : (∃ i, F.Single x i) ∨ ∃ i, F.Double x i) :
    ∃ p : Fin 6 → V, InducedPath G p := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have shape : (∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i,∀ j,b j=true ↔ j=i ∨ j=i+1) := by
    rcases kind with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨i,fun j => (bt j).trans (hi.2 j)⟩
    · exact Or.inr ⟨i,fun j => (bt j).trans (hi.2 j)⟩
  obtain ⟨i,pos,hi,he,_⟩ := normal6 b shape
  let M : Model G (@Cyclic 6) := ⟨F.c,F.inj,fun i j => (F.adj i j).symm⟩
  let T := M.extend x hx bt
  exact ⟨T.f ∘ path6 i pos,T.inj.comp (fun {_ _} => hi _ _),
    fun i j h => (T.adj _ _).symm.trans (he _ _ h)⟩

private lemma opp_near_site : ∀ a : Fin 6, ∀ b : Fin 3,
    ∃ j : Fin 6, (j=frontInd b ∨ j=frontInd b+3) ∧ (a=j ∨ Cyclic a j) := by decide

theorem radius_two_of_all_opp (hc : G.Connected)
    (every : ∀ x,Outside F.c x → ∃ i,F.Opp x i)
    {x : V} {i : Fin 3} (hx : F.Opp x i) : radius G≤2 := by
  let a := frontInd i
  have all (j : Fin 6) : G.dist (F.c a) (F.c j)≤2 := by
    by_cases eq : j=a+3
    · subst j
      have h := hc.dist_triangle (u:=F.c a) (v:=x) (w:=F.c (a+3))
      rw [dist_eq_one_iff_adj.mpr ((hx.2 _).mpr (Or.inl rfl)).symm,
        dist_eq_one_iff_adj.mpr ((hx.2 _).mpr (Or.inr rfl))] at h
      exact h
    · exact F.cycle_dist_two hc eq
  apply radius_to G (F.c a) 2
  intro y
  by_cases out : Outside F.c y
  · obtain ⟨i,ho⟩ := every y out
    obtain ⟨j,site,near⟩ := opp_near_site a i
    have hit := (ho.2 j).mpr site
    have nearDist : G.dist (F.c a) (F.c j)≤1 := by
      rcases near with eq | e
      · rw [eq,dist_self]
        exact Nat.zero_le _
      · exact (dist_eq_one_iff_adj.mpr (F.cycle_adj _ _ e)).le
    have tri := hc.dist_triangle (u:=F.c a) (v:=F.c j) (w:=y)
    rw [dist_eq_one_iff_adj.mpr hit.symm] at tri
    omega
  · obtain ⟨j,rfl⟩ := F.exists_cycle out
    exact all j

/-- A dominating C6 in a P6-free C4-free connected graph either spans or
provides a center of radius at most two, even when C5 is permitted. -/
theorem P6free_hex_radius_two_or_spans (hc : G.Connected)
    (no6 : ¬∃ p : Fin 6 → V, InducedPath G p) :
    radius G≤2 ∨ Function.Surjective F.c := by
  classical
  by_cases sur : Function.Surjective F.c
  · exact Or.inr sur
  · have out : ∃ x,Outside F.c x := by
      apply Classical.byContradiction
      intro no
      apply sur
      intro x
      have e : ¬Outside F.c x := fun h => no ⟨x,h⟩
      obtain ⟨i,he⟩ := F.exists_cycle e
      exact ⟨i,he.symm⟩
    have every (x : V) (h : Outside F.c x) : ∃ i,F.Opp x i := by
      rcases F.classify ⟨h,F.dom x h⟩ with s | d | opp
      · exact (no6 (F.P6_of_single_or_double h (Or.inl s))).elim
      · exact (no6 (F.P6_of_single_or_double h (Or.inr d))).elim
      · exact opp
    obtain ⟨x,hx⟩ := out
    obtain ⟨i,hi⟩ := every x hx
    exact Or.inl (F.radius_two_of_all_opp hc every hi)

#print axioms P6free_hex_radius_two_or_spans

#print axioms singleton_neighbors
#print axioms hex_budget

end Frame

theorem dominating_hex_radius_or_strict_density (H : Hole G 6) (hc : G.Connected)
    (h4 : FourCycleFree G) (h8 : ¬∃ p : Fin 8 → V, InducedPath G p)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    radius G ≤ 3 ∨ (∑ x, localIndependence G x) + 6 ≤ 3 * Fintype.card V := by
  by_cases hr : radius G≤3
  · exact Or.inl hr
  · let F : Frame G := ⟨H,h4,h8,dom⟩
    exact Or.inr (F.hex_budget hc (Nat.lt_of_not_ge hr))

#print axioms dominating_hex_radius_or_strict_density
end Graffiti133DominatingHex
