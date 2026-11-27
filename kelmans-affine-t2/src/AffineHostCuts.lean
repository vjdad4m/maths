import AffineHost

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.AffineHost
open AffineBase FourRingBudget FourRingReplica FourRingReplica.Layout FourRingCutAux FourRingCutChoices
noncomputable section
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r) (c : V r→Bool)

def active : Finset (Point×Slot) :=
  univ.filter (fun s=>c (cell s.1 (L.port s.2))≠c (control (route s.1 s.2)))

omit [Fintype U] [DecidableEq U] in
theorem mem_active {s : Point×Slot} :
    s∈active L c ↔ c (cell s.1 (L.port s.2))≠c (control (route s.1 s.2)) :=
  by simp [active]

private def reprEdge (s : Point×Slot) : V r×V r :=
  orientation c (cell s.1 (L.port s.2)) (control (route s.1 s.2))

omit [Fintype U] [DecidableEq U] in
private theorem repr_inj : Function.Injective (reprEdge L c) := by
  intro s t eq
  have inl : cell s.1 (L.port s.2)=cell t.1 (L.port t.2) := by
    rcases orientation_cases (c:=c) (x:=cell s.1 (L.port s.2))
      (y:=control (route s.1 s.2)) with es|es <;>
    rcases orientation_cases (c:=c) (x:=cell t.1 (L.port t.2))
      (y:=control (route t.1 t.2)) with et|et
    · exact congrArg Prod.fst (es.symm.trans (eq.trans et))
    · have n := congrArg Prod.fst (es.symm.trans (eq.trans et))
      cases n
    · have n := congrArg Prod.snd (es.symm.trans (eq.trans et))
      cases n
    · exact congrArg Prod.snd (es.symm.trans (eq.trans et))
  have zx := Sum.inl.inj inl
  exact Prod.ext (congrArg (fun p : Point×Piece r=>p.1) zx)
    (L.port.injective (congrArg (fun p : Point×Piece r=>p.2) zx))

def colourOfCell (i : Point) : Piece r→Bool := fun x=>c (cell i x)

def bodyCut (i : Point) : ℕ := (boundary (minor A r) (colourOfCell c i)).card

private def bodyEmbedding (i : Point) : (Piece r×Piece r)↪(V r×V r) :=
  ⟨fun z=>(cell i z.1,cell i z.2),by
    intro x y eq
    have l : cell i x.1=cell i y.1 := congrArg Prod.fst eq
    have r : cell i x.2=cell i y.2 := congrArg Prod.snd eq
    exact Prod.ext (congrArg (fun z : Point×Piece _=>z.2) (Sum.inl.inj l))
      (congrArg (fun z : Point×Piece _=>z.2) (Sum.inl.inj r))⟩

private def mappedBody (i : Point) : Finset (V r×V r) :=
  (boundary (minor A r) (colourOfCell c i)).map (bodyEmbedding i)

private def cellTag : V r→Option Point
  | .inl z => some z.1
  | .inr _ => none

private theorem bothCellTags (i : Point) {e : V r×V r} (m : e∈mappedBody (A:=A) c i) :
    cellTag e.1=some i ∧ cellTag e.2=some i := by
  obtain ⟨z,_,rfl⟩ := mem_map.mp m
  exact ⟨rfl,rfl⟩

theorem boundary_lower :
    (∑ i : Point,bodyCut (A:=A) c i)+(active L c).card≤(boundary (graph L) c).card := by
  classical
  let B := univ.biUnion (mappedBody (A:=A) c)
  let X := (active L c).image (reprEdge L c)
  have bib : ∀i,mappedBody (A:=A) c i⊆boundary (graph L) c := by
    intro i z zm
    obtain ⟨w,wm,rfl⟩ := mem_map.mp zm
    obtain ⟨b,d,e⟩ := mem_boundary.mp wm
    change (cell i w.1,cell i w.2)∈boundary (graph L) c
    exact mem_boundary.mpr ⟨b,d,⟨rfl,e⟩⟩
  have ex : X⊆boundary (graph L) c := by
    intro z zm
    obtain ⟨s,sm,rfl⟩ := mem_image.mp zm
    exact active_edge ((mem_active L c).mp sm) (attach L s.1 s.2)
  have both : B∪X⊆boundary (graph L) c := by
    refine union_subset ?_ ex
    intro z bm
    obtain ⟨i,_,m⟩ := mem_biUnion.mp bm
    exact bib i m
  have d : Disjoint B X := by
    apply disjoint_left.mpr
    intro z bz xz
    obtain ⟨i,_,m⟩ := mem_biUnion.mp bz
    have good := bothCellTags c i m
    obtain ⟨s,_,rfl⟩ := mem_image.mp xz
    rcases orientation_cases (c:=c) (x:=cell s.1 (L.port s.2))
      (y:=control (route s.1 s.2)) with h|h
    · change reprEdge L c s=_ at h
      rw [h] at good
      exact Option.noConfusion good.2
    · change reprEdge L c s=_ at h
      rw [h] at good
      exact Option.noConfusion good.1
  have sep : (↑(univ:Finset Point):Set Point).PairwiseDisjoint (mappedBody (A:=A) c) := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro z zi zj
    exact ne (Option.some.inj ((bothCellTags c i zi).1.symm.trans (bothCellTags c j zj).1))
  have bound := card_le_card both
  rw [card_union_of_disjoint d] at bound
  have b : B.card=∑ i:Point,bodyCut (A:=A) c i := by
    change (univ.biUnion (mappedBody (A:=A) c)).card=_
    rw [card_biUnion sep]
    exact sum_congr rfl (fun i _=>card_map _)
  have x : X.card=(active L c).card := card_image_of_injective _ (repr_inj L c)
  rwa [b,x] at bound

def MixedCell (i : Point) : Prop :=
    (∃ x : Piece r,c (cell i x)=true) ∧ (∃ x : Piece r,c (cell i x)=false)

def cellHue (i : Point) : Bool := c (cell i (L.port (false,false)))

omit [Fintype U] [DecidableEq U] in
theorem healthy {i : Point} (no : ¬MixedCell c i) (x : Piece r) :
    c (cell i x)=cellHue L c i := by
  classical
  by_contra ne
  cases h : c (cell i x) <;> cases j : cellHue L c i
  · exact ne (h.trans j.symm)
  · exact no ⟨⟨L.port (false,false),j⟩,⟨x,h⟩⟩
  · exact no ⟨⟨x,h⟩,⟨L.port (false,false),j⟩⟩
  · exact ne (h.trans j.symm)

omit [Fintype U] [DecidableEq U] in
theorem mixed_lines_le_active (ex : Option Point)
    (unmixed : ∀ i,some i≠ex→¬MixedCell c i) :
    (univ.filter (MixedLine (cellHue L c) ex)).card≤(active L c).card := by
  classical
  let e (s : Point×Slot) := route s.1 s.2
  have sub : univ.filter (MixedLine (cellHue L c) ex)⊆(active L c).image e := by
    intro l lm
    obtain ⟨⟨p,pn,pi,pt⟩,⟨q,qn,qi,qf⟩⟩ := (mem_filter.mp lm).2
    have pick (i : Point) (hi : some i≠ex) (inc : Incident i l)
        (dif : cellHue L c i≠c (control l)) : l∈(active L c).image e := by
      obtain ⟨s,rt⟩ := (incident_iff i l).mp inc
      refine mem_image.mpr ⟨(i,s),(mem_active L c).mpr ?_,rt⟩
      change c (cell i (L.port s))≠c (control (route i s))
      rw [rt,healthy L c (unmixed i hi)]
      exact dif
    cases cc : c (control l)
    · exact pick p pn pi (by rw [pt,cc]; decide)
    · exact pick q qn qi (by rw [qf,cc]; decide)
  exact (card_le_card sub).trans card_image_le

def activeAtLine (l : Line) : Finset (Point×Slot) :=
    (active L c).filter (fun s=>route s.1 s.2=l)

omit [Fintype U] [DecidableEq U] in
theorem line_points_le_active (ex : Option Point) (l : Line) (b : Bool)
    (hue : ∀ i,some i≠ex→∀ x : Piece r,c (cell i x)=b)
    (dif : c (control l)≠b) :
    (univ.filter (fun i=>some i≠ex ∧ Incident i l)).card≤(activeAtLine L c l).card := by
  classical
  have sub : univ.filter (fun i=>some i≠ex ∧ Incident i l) ⊆ (activeAtLine L c l).image Prod.fst := by
    intro i im
    obtain ⟨hi,it⟩ := (mem_filter.mp im).2
    obtain ⟨s,rt⟩ := (incident_iff i l).mp it
    refine mem_image.mpr ⟨(i,s),mem_filter.mpr ⟨(mem_active L c).mpr ?_,rt⟩,rfl⟩
    change c (cell i (L.port s))≠c (control (route i s))
    rw [rt,hue i hi]
    exact dif.symm
  exact (card_le_card sub).trans card_image_le

omit [Fintype U] [DecidableEq U] in
theorem disjoint_active_line {l m : Line} (ne : l≠m) :
    Disjoint (activeAtLine L c l) (activeAtLine L c m) := by
  apply disjoint_left.mpr
  intro s sl sm
  exact ne (((mem_filter.mp sl).2).symm.trans (mem_filter.mp sm).2)

omit [Fintype U] in
private theorem uniform_cost (i : Point) (b : Bool)
    (all : ∀ l,c (control l)=b) :
    extensionCost (fun s=>c (cell i (L.port s))) b b≤(active L c).card := by
  classical
  let D := L.capActive (colourOfCell c i) b b
  let f : Option Slot→Point×Slot := fun s=>(i,s.getD (false,false))
  have ne (j : Option Slot) (m : j∈D) : j≠none := by
    rintro rfl
    have h : extend (colourOfCell c i) b b (r false)≠extend (colourOfCell c i) b b (r true) :=
      (mem_filter.mp m).2
    rw [extend_false,L.extend_true] at h
    exact h rfl
  have inj : Set.InjOn f D := by
    rintro (_|s) a (_|t) d eq
    · rfl
    · exact (ne none a rfl).elim
    · exact (ne none d rfl).elim
    · exact congrArg some (congrArg Prod.snd eq)
  have sub : D.image f⊆active L c := by
    intro z zm
    obtain ⟨s,sm,rfl⟩ := mem_image.mp zm
    cases s with
    | none => exact (ne none sm rfl).elim
    | some s =>
      obtain ⟨k,t⟩ := s
      have h : extend (colourOfCell c i) b b (r k)≠
        extend (colourOfCell c i) b b (L.port (k,t)).val := (mem_filter.mp sm).2
      rw [extend_piece] at h
      apply (mem_active L c).mpr
      change c (cell i (L.port (k,t)))≠c (control (route i (k,t)))
      rw [all]
      cases k
      · rw [extend_false] at h
        exact h.symm
      · rw [L.extend_true] at h
        exact h.symm
  have sz := card_le_card sub
  rw [card_image_of_injOn inj,L.active_card] at sz
  exact sz

private theorem sum_one (f : Point→ℕ) (i : Point) : f i≤∑ j,f j :=
  single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ i)

private theorem sum_two (f : Point→ℕ) {i j : Point} (ne : i≠j) :
    f i+f j≤∑ z,f z := by
  have b : (∑ z∈({i,j}:Finset Point),f z)≤∑ z,f z := sum_le_sum_of_subset (subset_univ _)
  simpa [sum_insert,ne] using b

include L in
omit [Fintype U] in
private theorem singleton_from_cap (i : Point) (b : Bool)
    (out : ∀ j≠i,∀ x : Piece r,c (cell j x)=b)
    (ctrl : ∀ l,c (control l)=b)
    (trivial : (∀ x y,extend (colourOfCell c i) b b x=true →
       extend (colourOfCell c i) b b y=true→x=y) ∨
     (∀ x y,extend (colourOfCell c i) b b x=false →
       extend (colourOfCell c i) b b y=false→x=y)) :
    ∀ x y : V r,c x= !b → c y= !b → x=y := by
  have where_at (x : V r) (hx : c x= !b) : ∃ z : Piece r,x=cell i z := by
    cases x with
    | inl x =>
      have e : x.1=i := by
        by_contra ne
        have e := out x.1 ne x.2
        change c (Sum.inl x)=b at e
        cases b <;> simp_all
      exact ⟨x.2,congrArg Sum.inl (Prod.ext e rfl)⟩
    | inr l =>
      have e : c (control l)=b := ctrl l
      cases b <;> simp_all
  intro x y cx cy
  obtain ⟨x,rfl⟩ := where_at x cx
  obtain ⟨y,rfl⟩ := where_at y cy
  have cxI : extend (colourOfCell c i) b b x.val= !b := by rwa [extend_piece]
  have cyI : extend (colourOfCell c i) b b y.val= !b := by rwa [extend_piece]
  have rootF := extend_false (colourOfCell c i) b b
  have rootT := L.extend_true (colourOfCell c i) b b
  apply congrArg (cell i)
  apply Subtype.ext
  rcases trivial with tr|tr <;> cases b
  · exact tr _ _ cxI cyI
  · exact (L.rootEdge.ne (tr _ _ rootF rootT)).elim
  · exact (L.rootEdge.ne (tr _ _ rootF rootT)).elim
  · exact tr _ _ cxI cyI

/-- The affine incidence host stays in the cubic cyclic-four
cut domain given a cyclic-four cap. -/
theorem preserves_small_trivial [DecidableRel A.Adj] (cub : ∀v,A.degree v=3)
    (small : SmallTrivial A) : SmallTrivial (graph L) := by
  classical
  intro c low
  have budget := boundary_lower L c
  have mixedTwo {i : Point} (m : MixedCell c i) : 2 ≤ bodyCut (A:=A) c i :=
    L.mixed_internal_two cub small (colourOfCell c i) m.1 m.2
  have uniform (ex : Option Point) (no : ∀ i,some i≠ex→¬MixedCell c i)
      (few : (active L c).card≤3) (ref : Point) (hr : some ref≠ex) :
      ∀ i,some i≠ex → ∀ x : Piece r,c (cell i x)=cellHue L c ref := by
    intro i hi x
    rw [healthy L c (no i hi)]
    refine Classical.byContradiction ?_
    intro ne
    have different (e : (∃ p,some p≠ex ∧ cellHue L c p=true) ∧
        (∃ p,some p≠ex ∧ cellHue L c p=false)) : False := by
      have four := mixed_at_least_four (cellHue L c) ex e.1 e.2
      have m := mixed_lines_le_active L c ex no
      omega
    cases a : cellHue L c i <;> cases b : cellHue L c ref
    · exact ne (a.trans b.symm)
    · exact different ⟨⟨ref,hr,b⟩,⟨i,hi,a⟩⟩
    · exact different ⟨⟨i,hi,a⟩,⟨ref,hr,b⟩⟩
    · exact ne (a.trans b.symm)
  by_cases mixed : ∃ i,MixedCell c i
  · obtain ⟨i,m⟩ := mixed
    have no : ∀ j,some j≠some i→¬MixedCell c j := by
      intro j neq mm
      have jneq : j≠i := fun e=>neq (congrArg some e)
      have s := sum_two (bodyCut (A:=A) c) jneq
      have t := mixedTwo m
      have u := mixedTwo mm
      omega
    have one : (active L c).card≤1 := by
      have s := sum_one (bodyCut (A:=A) c) i
      have t := mixedTwo m
      omega
    let j := if i=0 then (1:Point) else 0
    have jn : some j≠some i := by
      unfold j
      by_cases e : i=0
      · simp [e]
      · simp [e,ne_comm]
    let b := cellHue L c j
    have out (k : Point) (ne : k≠i) (x : Piece r) : c (cell k x)=b :=
      uniform (some i) no (by omega) j jn k (fun e=>ne (Option.some.inj e)) x
    have controlHue (l : Line) : c (control l)=b := by
      refine Classical.byContradiction ?_
      intro other
      have z := line_points_le_active L c (some i) l b (fun k h=>out k (fun e=>h (congrArg some e))) other
      have s : 2≤(univ.filter (fun k=>some k≠some i ∧ Incident k l)).card := by
        simpa using card_points_on_line_except l i
      have le := card_le_card (filter_subset (fun s=>route s.1 s.2=l) (active L c))
      change (activeAtLine L c l).card≤(active L c).card at le
      omega
    have cap := L.cap_cut_upper (colourOfCell c i) b b
    have ec := uniform_cost L c i b controlHue
    change extensionCost (fun s=>colourOfCell c i (L.port s)) b b≤(active L c).card at ec
    have s := sum_one (bodyCut (A:=A) c) i
    change (boundary (minor A r) (colourOfCell c i)).card≤_ at s
    have smallCap : (boundary A (extend (colourOfCell c i) b b)).card≤3 := by omega
    have t := singleton_from_cap L c i b out controlHue (small _ smallCap)
    cases eb : b
    · exact Or.inl (by simpa only [eb,Bool.not_false] using t)
    · exact Or.inr (by simpa only [eb,Bool.not_true] using t)
  · push_neg at mixed
    let b := cellHue L c 0
    have out : ∀ i, some i≠(none:Option Point)→∀ x : Piece r,c (cell i x)=b :=
      uniform none (fun i _=>mixed i) (by omega) 0 (by simp)
    have op_control (x : V r) (dif : c x= !b) : ∃ l,x=control l := by
      cases x with
      | inl coord =>
        obtain ⟨i,w⟩ := coord
        have d := out i (by simp) w
        change c (cell i w)= !b at dif
        rw [d] at dif
        cases be : b <;> simp [be] at dif
      | inr l => exact ⟨l,rfl⟩
    have single (x y : V r) (cx : c x= !b) (cy : c y= !b) : x=y := by
      obtain ⟨l,rfl⟩ := op_control x cx
      obtain ⟨m,rfl⟩ := op_control y cy
      refine Classical.byContradiction ?_
      intro ne
      have lm : l≠m := fun e=>ne (congrArg control e)
      have dl : c (control l)≠b := by rw [cx]; cases b <;> decide
      have dm : c (control m)≠b := by rw [cy]; cases b <;> decide
      have al := line_points_le_active L c none l b out dl
      have am := line_points_le_active L c none m b out dm
      have cl : (univ.filter (fun i=>some i≠(none:Option Point) ∧ Incident i l)).card=3 := by
        simpa using card_points_on_line l
      have cm : (univ.filter (fun i=>some i≠(none:Option Point) ∧ Incident i m)).card=3 := by
        simpa using card_points_on_line m
      have sub : activeAtLine L c l∪activeAtLine L c m⊆active L c :=
        union_subset (filter_subset _ _) (filter_subset _ _)
      have le := card_le_card sub
      rw [card_union_of_disjoint (disjoint_active_line L c lm)] at le
      omega
    cases eb : b
    · exact Or.inl (by simpa only [eb,Bool.not_false] using single)
    · exact Or.inr (by simpa only [eb,Bool.not_true] using single)

#print axioms boundary_lower
#print axioms preserves_small_trivial
end
end KelmansCactus.AtomicBridge.AffineHost
