import P8NoFive133

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133P8Heawood Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace Model
variable (M : Model G Graffiti133P8Heawood.Anchor)

def Far (v : V) : Prop := M.Fresh v ∧ ∀ i, ¬G.Adj v (M.f i)

private def singleLast (k : ℕ) (i : Fin (k+1)) : Bool := decide (i=Fin.last k)
@[simp] private theorem singleLast_old (k : ℕ) (i : Fin k) : singleLast k i.castSucc=false := by
  simp [singleLast,Fin.ne_of_lt (Fin.castSucc_lt_last i)]
@[simp] private theorem singleLast_last (k : ℕ) : singleLast k (Fin.last k)=true := by
  simp [singleLast]

private def doubleExtension (t : Fin 4) : Fin 12 → Fin 12 → Prop :=
  ext (ext (ext Graffiti133P8Heawood.Anchor (Profile t)) (singleLast 9)) (singleLast 10)

private instance (t : Fin 4) : DecidableRel (doubleExtension t) :=
  inferInstanceAs (DecidableRel (ext (ext (ext Graffiti133P8Heawood.Anchor (Profile t)) (singleLast 9)) (singleLast 10)))

private def eighthRoute (t : Fin 4) : Fin 8 → Fin 12 := match t.val with
  | 0 => ![11,10,9,1,0,7,4,3]
  | 1 => ![11,10,9,2,1,0,7,4]
  | 2 => ![11,10,9,7,0,8,6,5]
  | _ => ![11,10,9,8,0,7,4,5]

private lemma double_eighth : ∀ t : Fin 4,
    (Cert.eight (eighthRoute t)).Valid (doubleExtension t) False := by
  decide

private theorem ban_far_edge_type1 {x y : V} (hx : M.hasType x 1) (hy : M.Far y)
    (a : G.Adj y x) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) : False := by
  let T := M.extend x hx.1 hx.2
  have fy (i : Fin 10) : y ≠ T.f i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [T,Model.extend_f_new] using a.ne
    · simpa only [T,Model.extend_f_old] using hy.1 j
  have cy (i : Fin 10) : singleLast 9 i=true ↔ G.Adj y (T.f i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [singleLast_last,T,Model.extend_f_new,a,iff_true]
    · simp only [singleLast_old,T,Model.extend_f_old,Bool.false_eq_true,hy.2 j]
  have good := (T.extend y fy cy).good h4 h5 h8
  exact avoid_far_type_one good

private theorem ban_far_tail {x y z : V} {t : Fin 4} (hx : M.hasType x t)
    (hy : M.Far y) (hz : M.Far z) (a : G.Adj y x) (b : G.Adj z y)
    (no : ¬G.Adj z x) (nZ : z≠x) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) : False := by
  let T := M.extend x hx.1 hx.2
  have fy (i : Fin 10) : y ≠ T.f i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [T,Model.extend_f_new] using a.ne
    · simpa only [T,Model.extend_f_old] using hy.1 j
  have cy (i : Fin 10) : singleLast 9 i=true ↔ G.Adj y (T.f i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [singleLast_last,T,Model.extend_f_new,a,iff_true]
    · simp only [singleLast_old,T,Model.extend_f_old,Bool.false_eq_true,hy.2 j]
  let U := T.extend y fy cy
  have fz (i : Fin 11) : z ≠ U.f i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [U,Model.extend_f_new] using b.ne
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [U,T,Model.extend_f_old,Model.extend_f_new] using nZ
      · simpa only [U,T,Model.extend_f_old] using hz.1 k
  have cz (i : Fin 11) : singleLast 10 i=true ↔ G.Adj z (U.f i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [singleLast_last,U,Model.extend_f_new,b,iff_true]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [singleLast_old,U,T,Model.extend_f_old,Model.extend_f_new,Bool.false_eq_true,no]
      · simp only [singleLast_old,U,T,Model.extend_f_old,Bool.false_eq_true,hz.2 k]
  have h := (U.extend z fz cz).good h4 h5 h8
  exact (Cert.eight (eighthRoute t)).sound (double_eighth t) h

private theorem far_has_near (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    ∀ y, M.Far y → ∃ x t, t≠1 ∧ M.hasType x t ∧ G.Adj y x := by
  classical
  let P (y : V) : Prop := M.Far y → ∃ x t, t≠1 ∧ M.hasType x t ∧ G.Adj y x
  have step (a b : V) (e : G.Adj a b) (ha : P a) : P b := by
    intro hb
    by_cases fA : M.Far a
    · obtain ⟨x,t,nt,hx,ex⟩ := ha fA
      by_cases g : G.Adj b x
      · exact ⟨x,t,nt,hx,g⟩
      · have nb : b≠x := by
          intro eq
          have p : ∃ i : Fin 9, Profile t i = true := by
            have s : ∀ t : Fin 4, ∃ i : Fin 9, Profile t i = true := by decide
            exact s t
          obtain ⟨i,hi⟩ := p
          exact hb.2 i (eq.symm ▸ (hx.2 i).mp hi)
        exact (M.ban_far_tail hx fA hb ex e.symm g nb h4 h5 h8).elim
    · have off (i : Fin 9) : a≠M.f i := by
        intro eq
        exact hb.2 i (eq ▸ e.symm)
      have hit : ∃ i, G.Adj a (M.f i) := by
        by_contra no
        exact fA ⟨off,fun i h => no ⟨i,h⟩⟩
      obtain ⟨t,ht⟩ := M.classified off h4 h5 h8 hit
      have t1 : t≠1 := by
        intro he
        exact M.ban_far_edge_type1 (he ▸ ht) hb e.symm h4 h5 h8
      exact ⟨a,t,t1,ht,e.symm⟩
  have walk {a b : V} (w : G.Walk a b) (ha : P a) : P b := by
    induction w with
    | nil => exact ha
    | cons e w ih => exact ih (step _ _ e ha)
  intro y
  obtain ⟨w⟩ := hc (M.f 0) y
  exact walk w (fun h => (h.1 0 rfl).elim)

private def par (i : Fin 9) : Fin 9 := ![0,0,1,2,7,4,8,0,0] i
private def depth (i : Fin 9) : ℕ := ![0,1,2,3,2,3,2,1,1] i
private def site (i : Fin 4) : Fin 9 := ![1,2,7,8] i

private lemma par_ok : ∀ i : Fin 9, i≠0 → Graffiti133P8Heawood.Anchor (par i) i ∧
    depth i = depth (par i)+1 := by decide
private lemma depth_max : ∀ i : Fin 9, depth i≤3 := by decide
private lemma site_ok : ∀ t : Fin 4, Profile t (site t)=true ∧ depth (site t) ≤ 2 ∧
    (t≠1 → depth (site t) ≤ 1) := by decide

private theorem anchor_distance (hc : G.Connected) : ∀ i, G.dist (M.f 0) (M.f i) ≤ depth i := by
  have aux (d : ℕ) : ∀ i, depth i=d → G.dist (M.f 0) (M.f i) ≤ depth i := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i eq
      by_cases h : i=0
      · subst i
        simpa only [dist_self] using Nat.zero_le (depth 0)
      · obtain ⟨e,ee⟩ := par_ok i h
        have dd : depth (par i) < d := by omega
        have old := ih (depth (par i)) dd (par i) rfl
        have tri := hc.dist_triangle (u:=M.f 0) (v:=M.f (par i)) (w:=M.f i)
        rw [dist_eq_one_iff_adj.mpr ((M.adj ..).mp e)] at tri
        omega
  intro i
  exact aux (depth i) i rfl

private theorem radius_bound (G : SimpleGraph V) (v : V) {k : ℕ} (h : ∀ w,G.dist v w ≤ k) :
    radius G ≤ k := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  have ht : Finset.univ.sup (G.dist v) ≤ k := Finset.sup_le_iff.mpr (fun w _ => h w)
  cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d => have h' : d ≤ Finset.univ.sup (G.dist v) := by simpa [hmin] using hl
             exact h'.trans ht

include M in
theorem radius_le_three_of_anchor (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    radius G ≤ 3 := by
  classical
  apply radius_bound G (M.f 0)
  have step {x : V} {t : Fin 4} (hx : M.hasType x t) :
      G.dist (M.f 0) x ≤ depth (site t)+1 := by
    have h := hc.dist_triangle (u:=M.f 0) (v:=M.f (site t)) (w:=x)
    rw [dist_eq_one_iff_adj.mpr ((hx.2 _).mp (site_ok t).1).symm] at h
    exact h.trans (Nat.add_le_add_right (M.anchor_distance hc _) 1)
  intro y
  by_cases hy : M.Fresh y
  · by_cases hit : ∃ i,G.Adj y (M.f i)
    · obtain ⟨t,ht⟩ := M.classified hy h4 h5 h8 hit
      have bd := step ht
      have dm := (site_ok t).2.1
      omega
    · have ff : M.Far y := ⟨hy,fun i e => hit ⟨i,e⟩⟩
      obtain ⟨x,t,nt,hx,e⟩ := M.far_has_near hc h4 h5 h8 y ff
      have bd := step hx
      have dm := (site_ok t).2.2 nt
      have hj := hc.dist_triangle (u:=M.f 0) (v:=x) (w:=y)
      rw [dist_eq_one_iff_adj.mpr e.symm] at hj
      omega
  · have ex : ∃ i,y=M.f i := by
      apply Classical.byContradiction
      intro no
      exact hy (fun i e => no ⟨i,e⟩)
    obtain ⟨i,rfl⟩ := ex
    exact (M.anchor_distance hc i).trans (depth_max i)

end Model

theorem P8_or_radius_three_of_high_P7_end (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {f : Fin 7 → V} (hf : InducedPath G f)
    (hm : 3 ≤ localIndependence G (f 0)) :
    (∃ q : Fin 8 → V, InducedPath G q) ∨ radius G ≤ 3 := by
  by_cases h : ∃ q : Fin 8 → V, InducedPath G q
  · exact Or.inl h
  · obtain ⟨A⟩ := anchor_of_path7 hf hm h4 h5 h
    exact Or.inr (A.model.radius_le_three_of_anchor hc h4 h5 h)

#print axioms Model.radius_le_three_of_anchor
#print axioms P8_or_radius_three_of_high_P7_end
end Graffiti133Eighth
