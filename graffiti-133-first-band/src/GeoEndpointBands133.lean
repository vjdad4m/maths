import AfterSeventh133
import EighthNoSix133

namespace Graffiti133Endpoint
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Graffiti133Eighth Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private lemma take_length {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    (p.take i).length = i := by
  induction p generalizing i with
  | nil =>
    have ei : i = 0 := by simpa using hi
    subst i
    rfl
  | cons h q ih =>
    cases i with
    | zero => rfl
    | succ i =>
        change (q.take i).length + 1 = i + 1
        rw [ih i (by simp only [Walk.length_cons] at hi; omega)]

private lemma drop_length {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.drop]
  | cons h q ih =>
    cases i with
    | zero => simp [Walk.drop]
    | succ i =>
        change (q.drop i).length = (q.length + 1) - (i + 1)
        rw [ih i, Nat.add_sub_add_right]

private lemma prefix_level (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h₁ := G.dist_le (p.take i)
  rw [take_length p i hi] at h₁
  have h₂ := G.dist_le (p.drop i)
  rw [drop_length] at h₂
  have h₃ := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

/-- Extend one end of a geodesic by at least floor(d/2) vertices.
Four-cycle exclusion is the only small-cycle constraint. -/
theorem one_sided_geodesic_extension_on_endpoint_ball
    (G : SimpleGraph V) (hc : G.Connected) (h4 : FourCycleFree G) (d : ℕ)
    {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (hlen : 1 ≤ p.length)
    (s : ℕ) (hs : s ≤ d/2)
    (hdeg : ∀ w, G.dist u w < s → d ≤ localIndependence G w) :
    ∃ f : Fin (p.length+1+s) → V, InducedPath G f ∧
      G.dist u (f ⟨0,by omega⟩) ≤ s ∧
      (∀ i : Fin (p.length+1+s), i.val-s ≤ G.dist u (f i)) ∧
      ∀ i : Fin (p.length+1), f ⟨s+i.val,by have := i.isLt; omega⟩ = p.getVert i := by
  classical
  induction s with
  | zero =>
    refine ⟨fun i => p.getVert i,?_,by simp,?_,fun _ => by simp⟩
    · change InducedPath G (fun i : Fin (p.length+1) => p.getVert i)
      refine ⟨?_,?_⟩
      · intro i j h
        apply Fin.ext
        have hi := prefix_level hc p hp (i := i.val) (by have := i.isLt; omega)
        have hj := prefix_level hc p hp (i := j.val) (by have := j.isLt; omega)
        change p.getVert i.val = p.getVert j.val at h
        rw [h] at hi
        omega
      · intro i j hij
        constructor
        · intro hadj
          have hi := prefix_level hc p hp (i := i.val) (by have := i.isLt; omega)
          have hj := prefix_level hc p hp (i := j.val) (by have := j.isLt; omega)
          have hh := hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)
          rw [hi,hj,dist_eq_one_iff_adj.mpr hadj] at hh
          change i.val < j.val at hij
          omega
        · intro he
          change i.val+1 = j.val at he
          change G.Adj (p.getVert i.val) (p.getVert j.val)
          rw [← he]
          exact p.adj_getVert_succ (by have := j.isLt; omega)
    · intro i
      rw [Nat.sub_zero,prefix_level hc p hp (by have := i.isLt; omega)]
  | succ s ih =>
    obtain ⟨f,hf,hnear,hfar,horig⟩ := ih (by omega) (fun w hw => hdeg w (by omega))
    let k := p.length+1+s
    let i₀ : Fin k := ⟨0,by dsimp [k]; omega⟩
    let i₁ : Fin k := ⟨1,by dsimp [k]; omega⟩
    have h01 : G.Adj (f i₀) (f i₁) := (hf.2 _ _ (by change 0 < 1; decide)).mpr rfl
    obtain ⟨A,hA,hOne,hAC⟩ := max_local_set_with G h4 h01
    obtain ⟨hAN,hAI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
    let R := A.erase (f i₁)
    have ha (w : R) : G.Adj (f i₀) w.val := hAN _ (mem_erase.mp w.property).2
    have hn (w : R) : w.val ≠ f i₁ := (mem_erase.mp w.property).1
    have hnew (w : R) (i : Fin k) : w.val ≠ f i := by
      intro he
      have hh := ha w
      rw [he] at hh
      by_cases hi : i.val = 0
      · have e : i = i₀ := Fin.ext hi
        exact G.loopless _ (e ▸ hh)
      · have hi' : i₀ < i := by change 0 < i.val; omega
        have h := (hf.2 _ _ hi').mp hh
        have e : i = i₁ := Fin.ext h.symm
        exact hn w (he.trans (congrArg f e))
    have hext : ∃ w : R, ∀ j : Fin k, 0 < j.val → ¬ G.Adj w.val (f j) := by
      apply Classical.byContradiction
      intro hbad
      push_neg at hbad
      choose j hj hjadj using hbad
      have hlo (w : R) : 3 ≤ (j w).val := by
        have hpos := hj w
        by_cases hlt : 3 ≤ (j w).val
        · exact hlt
        exfalso
        by_cases h : (j w).val = 1
        · have e : j w = i₁ := Fin.ext h
          exact hAI _ (mem_erase.mp w.property).2 _ hOne (e ▸ hjadj w)
        · have hij : i₁ < j w := by change 1 < (j w).val; omega
          have e12 : G.Adj (f i₁) (f (j w)) :=
            (hf.2 _ _ hij).mpr (by change 1+1 = (j w).val; omega)
          have hne : f i₀ ≠ f (j w) := by
            intro e
            have e' := congrArg Fin.val (hf.1 e)
            change 0 = (j w).val at e'
            omega
          exact hn w (h4 _ _ _ _ hne (ha w) (hjadj w).symm h01 e12.symm)
      have hhi (w : R) : (j w).val ≤ 2*s+2 := by
        have h₁ := hc.dist_triangle (u := f i₀) (v := w.val) (w := f (j w))
        rw [dist_eq_one_iff_adj.mpr (ha w),dist_eq_one_iff_adj.mpr (hjadj w)] at h₁
        have h₂ := hc.dist_triangle (u := u) (v := f i₀) (w := f (j w))
        have h₃ := hfar (j w)
        change G.dist u (f i₀) ≤ s at hnear
        omega
      let idx (w : R) : Fin (2*s) := ⟨(j w).val-3, by
        have := hlo w
        have := hhi w
        omega⟩
      have hinj : Function.Injective idx := by
        intro a b e
        have e' := congrArg Fin.val e
        change (j a).val-3 = (j b).val-3 at e'
        have ha3 := hlo a
        have hb3 := hlo b
        have eq : j a = j b := Fin.ext (by omega)
        have hne : f i₀ ≠ f (j a) := by
          intro h
          have hx := congrArg Fin.val (hf.1 h)
          change 0 = (j a).val at hx
          omega
        exact Subtype.ext (h4 _ _ _ _ hne (ha a) (hjadj a).symm (ha b) (eq.symm ▸ (hjadj b).symm))
      have hcount := Fintype.card_le_of_injective idx hinj
      simp only [Fintype.card_fin,Fintype.card_coe] at hcount
      have hcard : R.card + 1 = localIndependence G (f i₀) :=
        (Finset.card_erase_add_one hOne).trans hAC
      have hl := hdeg (f i₀) (by
        exact Nat.lt_succ_of_le hnear)
      omega
    obtain ⟨w,hw⟩ := hext
    obtain ⟨ff,hff,hhead,htail⟩ :=
      prepend_induced_with_positions (by omega) hf w.val (hnew w) (ha w).symm hw
    have hheadDist : G.dist u w.val ≤ s+1 := by
      have h := hc.dist_triangle (u := u) (v := f i₀) (w := w.val)
      rw [dist_eq_one_iff_adj.mpr (ha w)] at h
      change G.dist u (f i₀) ≤ s at hnear
      omega
    refine ⟨ff,hff,by simpa only [hhead] using hheadDist,?_,?_⟩
    · intro i
      by_cases hi : 0 < i.val
      · rw [htail i hi]
        have h := hfar ⟨i.val-1,by have := i.isLt; dsimp [k] at *; omega⟩
        change i.val-1-s ≤ _ at h
        omega
      · omega
    · intro i
      have hx : 0 < s+1+i.val := by omega
      rw [htail _ hx]
      have e : (⟨s+1+i.val-1,by have := i.isLt; dsimp [k]; omega⟩ : Fin k) =
          ⟨s+i.val,by have := i.isLt; dsimp [k]; omega⟩ := Fin.ext (by change s+1+i.val-1=s+i.val; omega)
      rw [e,horig]

#print axioms one_sided_geodesic_extension_on_endpoint_ball

omit [Fintype V] in
private theorem induced_index_dist (hc : G.Connected) {k : ℕ}
    {f : Fin k → V} (hf : InducedPath G f) (i : Fin k) (t : ℕ)
    (ht : i.val+t < k) :
    G.dist (f i) (f ⟨i.val+t,ht⟩) ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    let j : Fin k := ⟨i.val+t,by omega⟩
    let j' : Fin k := ⟨i.val+(t+1),ht⟩
    have ha : G.Adj (f j) (f j') := (hf.2 _ _
      (by change i.val+t < i.val+(t+1); omega)).mpr
      (by change (i.val+t)+1 = i.val+(t+1); omega)
    have h := hc.dist_triangle (u := f i) (v := f j) (w := f j')
    rw [dist_eq_one_iff_adj.mpr ha] at h
    have hh : G.dist (f i) (f j) ≤ t := ih (by omega)
    exact le_trans h (Nat.add_le_add_right hh 1)

/-- Two independently constructed shortest-path extensions can be joined
as long as any cross edge between the new parts would shorten the geodesic. -/
theorem two_sided_geodesic_extension_on_endpoint_balls
    (G : SimpleGraph V) (hc : G.Connected) (h4 : FourCycleFree G) (d : ℕ)
    {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (a b : ℕ) (ha : a ≤ d/2) (hb : b ≤ d/2) (hgap : a+b+2 ≤ p.length)
    (hLball : ∀ w, G.dist u w < a → d ≤ localIndependence G w)
    (hRball : ∀ w, G.dist v w < b → d ≤ localIndependence G w) :
    ∃ f : Fin (p.length+1+a+b) → V, InducedPath G f := by
  let D := p.length
  have dlow : 1 ≤ p.length := by omega
  have hp' : p.reverse.length = G.dist v u := by
    rw [Walk.length_reverse,hp,SimpleGraph.dist_comm]
  obtain ⟨L,hL,_,_,hLp⟩ := one_sided_geodesic_extension_on_endpoint_ball G hc h4 d
    p hp dlow a ha hLball
  obtain ⟨R,hR,_,_,hRp⟩ := one_sided_geodesic_extension_on_endpoint_ball G hc h4 d
    p.reverse hp' (by simpa only [Walk.length_reverse] using dlow) b hb hRball
  let l (i : ℕ) (hi : i < D+1+a) : Fin (p.length+1+a) := ⟨i,hi⟩
  have rbound (i : ℕ) (hi : a ≤ i) : D+a+b-i < p.reverse.length+1+b := by
    rw [Walk.length_reverse]
    change D+a+b-i < D+1+b
    omega
  let r (i : ℕ) (hi : a ≤ i) : Fin (p.reverse.length+1+b) := ⟨D+a+b-i,rbound i hi⟩
  let f (i : Fin (p.length+1+a+b)) : V :=
    if h : i.val < a then L (l i.val (by omega)) else R (r i.val (by omega))
  have fl (i : Fin (p.length+1+a+b)) (hi : i.val < a) :
      f i = L (l i.val (by omega)) := dif_pos hi
  have fr (i : Fin (p.length+1+a+b)) (hi : a ≤ i.val) :
      f i = R (r i.val hi) := dif_neg (by omega)
  have hoverlap (i : ℕ) (hi : a ≤ i) (hD : i ≤ a+D) :
      R (r i hi) = L (l i (by omega)) := by
    have iL : i-a < p.length+1 := by change i-a < D+1; omega
    have iR : a+D-i < p.reverse.length+1 := by
      rw [Walk.length_reverse]
      change a+D-i < D+1
      omega
    have el : l i (by omega) = ⟨a+(i-a),by dsimp [D] at *; omega⟩ :=
      Fin.ext (by change i = a+(i-a); omega)
    have er : r i hi = ⟨b+(a+D-i),by have := iR; omega⟩ :=
      Fin.ext (by change D+a+b-i = b+(a+D-i); omega)
    rw [el,er,hLp ⟨i-a,iL⟩,hRp ⟨a+D-i,iR⟩,Walk.getVert_reverse]
    congr 1
    change D-(a+D-i) = i-a
    omega
  have left_dist (i : ℕ) (hi : i < a) : G.dist u (L (l i (by omega))) ≤ a-i := by
    have h := induced_index_dist hc hL (l i (by omega)) (a-i)
      (show i+(a-i) < p.length+1+a by omega)
    have e : (⟨i+(a-i),by omega⟩ : Fin (p.length+1+a)) =
        ⟨a+(0:ℕ),by omega⟩ := Fin.ext (by change i+(a-i) = a+0; omega)
    change G.dist (L (l i (by omega))) (L ⟨i+(a-i),by omega⟩) ≤ a-i at h
    rw [e,hLp ⟨0,by omega⟩,Walk.getVert_zero,SimpleGraph.dist_comm] at h
    exact h
  have right_dist (j : ℕ) (hj : a+D < j) (hj' : j < D+1+a+b) :
      G.dist (R (r j (by omega))) v ≤ b := by
    let t := D+a+b-j
    have ht : t ≤ b := by dsimp [t]; omega
    have h := induced_index_dist hc hR (r j (by omega)) (b-t)
      (show t+(b-t) < p.reverse.length+1+b by omega)
    have e : (⟨t+(b-t),by omega⟩ : Fin (p.reverse.length+1+b)) =
        ⟨b+(0:ℕ),by omega⟩ := Fin.ext (by change t+(b-t)=b+0; omega)
    change G.dist (R (r j (by omega))) (R ⟨t+(b-t),by omega⟩) ≤ b-t at h
    rw [e,hRp ⟨0,by omega⟩,Walk.getVert_zero] at h
    omega
  have cross (i j : Fin (p.length+1+a+b)) (hi : i.val < a) (hj : a+D < j.val) :
      f i ≠ f j ∧ ¬ G.Adj (f i) (f j) := by
    rw [fl i hi,fr j (by omega)]
    have hl := left_dist i.val hi
    have hr := right_dist j.val hj (show j.val < D+1+a+b from j.isLt)
    have h₁ := hc.dist_triangle (u := u) (v := L (l i.val (by omega))) (w := v)
    have h₂ := hc.dist_triangle (u := L (l i.val (by omega)))
      (v := R (r j.val (by omega))) (w := v)
    change p.length = G.dist u v at hp
    have hD : a+b+2 ≤ D := hgap
    constructor
    · intro he
      have h₀ : G.dist (L (l i.val (by omega))) (R (r j.val (by omega))) = 0 := by rw [he,dist_self]
      change D = G.dist u v at hp
      omega
    · intro he
      have h₀ := dist_eq_one_iff_adj.mpr he
      change D = G.dist u v at hp
      omega
  have distinct (i j : Fin (p.length+1+a+b)) (hij : i.val < j.val) : f i ≠ f j := by
    by_cases hi : i.val < a
    · by_cases hj : j.val < a
      · rw [fl i hi,fl j hj]
        intro h
        have he := congrArg Fin.val (hL.1 h)
        change i.val = j.val at he
        omega
      · by_cases hjD : j.val ≤ a+D
        · rw [fl i hi,fr j (by omega),hoverlap j.val (by omega) hjD]
          intro h
          have he := congrArg Fin.val (hL.1 h)
          change i.val = j.val at he
          omega
        · exact (cross i j hi (by omega)).1
    · rw [fr i (by omega),fr j (by omega)]
      intro h
      have he := congrArg Fin.val (hR.1 h)
      change D+a+b-i.val = D+a+b-j.val at he
      have hj := j.isLt
      change j.val < D+1+a+b at hj
      omega
  refine ⟨f,⟨?_,?_⟩⟩
  · intro i j h
    apply Fin.ext
    by_cases he : i.val = j.val
    · exact he
    exfalso
    rcases lt_or_gt_of_ne he with hij | hji
    · exact distinct i j hij h
    · exact distinct j i hji h.symm
  · intro i j hij
    change i.val < j.val at hij
    by_cases hi : i.val < a
    · by_cases hj : j.val < a
      · rw [fl i hi,fl j hj]
        exact hL.2 _ _ hij
      · by_cases hjD : j.val ≤ a+D
        · rw [fl i hi,fr j (by omega),hoverlap j.val (by omega) hjD]
          exact hL.2 _ _ hij
        · exact iff_of_false (cross i j hi (by omega)).2 (by
            have hD : 2 ≤ D := by have h : a+b+2 ≤ D := hgap; omega
            omega)
    · rw [fr i (by omega),fr j (by omega)]
      have hj := j.isLt
      change j.val < D+1+a+b at hj
      rw [adj_comm, hR.2 _ _ (show (r j.val (by omega)) < (r i.val (by omega)) by
        change D+a+b-j.val < D+a+b-i.val
        omega)]
      change D+a+b-j.val+1 = D+a+b-i.val ↔ i.val+1 = j.val
      omega

#print axioms two_sided_geodesic_extension_on_endpoint_balls

private theorem first_band_no_P8 (h4 : FourCycleFree G) (hr : radius G=4) (ha : averageLocal G ≤ 4)
    (bad : ¬ ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    ¬∃ f : Fin 8 → V, InducedPath G f := by
  intro e
  apply bad
  refine ⟨8,?_,e⟩
  simp only [rhs133,if_pos h4,pow_one,hr,Nat.cast_ofNat]
  linarith

theorem after_P7_first_band_endpoint_constraints (G : SimpleGraph V) (hc : G.Connected)
    (ha : averageLocal G ≤ 4)
    (bad : ¬ ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    (∀ u v, 5 ≤ G.dist u v → localIndependence G u ≤ 1 ∨ localIndependence G v ≤ 1) ∧
    (∀ u v, 6 ≤ G.dist u v → localIndependence G u ≤ 1) := by
  have ⟨h4,_,_,_,_,hr⟩ := after_P7_real_constraints G hc bad
  have no := first_band_no_P8 h4 (hr ha).1 ha bad
  have point (u : V) (hu : 2 ≤ localIndependence G u) (w : V) (hw : G.dist u w < 1) :
      2 ≤ localIndependence G w := by
    have he := hc.dist_eq_zero_iff.mp (show G.dist u w = 0 by omega)
    exact he ▸ hu
  constructor
  · intro u v dv
    by_contra! b
    have hU : 2 ≤ localIndependence G u := by omega
    have hV : 2 ≤ localIndependence G v := by omega
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
    obtain ⟨f,hf⟩ := two_sided_geodesic_extension_on_endpoint_balls G hc h4 2 p hp
      1 1 (by decide) (by decide) (by omega) (point u hU) (point v hV)
    exact no (trim_path (by omega : 8 ≤ p.length+1+1+1) hf)
  · intro u v dv
    by_contra! b
    have hU : 2 ≤ localIndependence G u := by omega
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
    obtain ⟨f,hf⟩ := two_sided_geodesic_extension_on_endpoint_balls G hc h4 2 p hp
      1 0 (by decide) (by decide) (by omega) (point u hU)
      (fun w hw => (Nat.not_lt_zero _ hw).elim)
    exact no (trim_path (by omega : 8 ≤ p.length+1+1+0) hf)

#print axioms after_P7_first_band_endpoint_constraints
end Graffiti133Endpoint
