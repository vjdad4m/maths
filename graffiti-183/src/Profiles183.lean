import DoubleShift183

namespace Graffiti183.Exceptional
open SimpleGraph Finset
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {m : ℕ} {V : Type*} {G : SimpleGraph V} {f : Fin m ↪ V}

private theorem cyc_symm {i j : Fin m} (h : CycleAdj i j) : CycleAdj j i := by
  unfold CycleAdj at *
  tauto

private theorem fne {i j : Fin m} (h : i.val ≠ j.val) : f i ≠ f j :=
  fun e => h (congrArg Fin.val (f.injective e))

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_tri_in_cycle (hm : 7 ≤ m) {a b c : Fin m}
    (hab : CycleAdj a b) (hac : CycleAdj a c) (hbc : CycleAdj b c) : False := by
  have ab := a.isLt
  have bb := b.isLt
  have cb := c.isLt
  unfold CycleAdj at hab hac hbc
  omega

theorem contacts_no_isolated (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hclaw : ClawFree G) {z : V} (hz : z ∉ indexSet f)
    (i : Fin m) (hi : G.Adj z (f i)) :
    ∃ j, G.Adj z (f j) ∧ CycleAdj i j := by
  obtain ⟨p,hp⟩ := rot_surjective (⟨1,by omega⟩ : Fin m) i
  let q := succFin i
  have e (j : Fin m) (hj : CycleAdj i j) : G.Adj (f i) (f j) := (hcyc _ _).mpr hj
  have ep : CycleAdj i p := by
    apply (cycleAdj_iff_succ (by omega)).mpr
    exact Or.inr (by simpa [succFin,rot,Nat.add_comm] using hp)
  have eq : CycleAdj i q := (cycleAdj_iff_succ (by omega)).mpr (Or.inl rfl)
  have hpq : p ≠ q := by
    intro h
    have a := i.isLt
    have b := p.isLt
    have h1 : (1+p.val)%m=i.val := congrArg Fin.val hp
    have h2 : (i.val+1)%m=p.val := (congrArg Fin.val h).symm
    by_cases h3 : 1+p.val<m
    · rw [Nat.mod_eq_of_lt h3] at h1
      by_cases h4 : i.val+1<m
      · rw [Nat.mod_eq_of_lt h4] at h2; omega
      · have he : i.val+1=m := by omega
        rw [he,Nat.mod_self] at h2; omega
    · have he : 1+p.val=m := by omega
      rw [he,Nat.mod_self] at h1
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega
  have hn : ¬ G.Adj (f p) (f q) := fun h =>
    no_tri_in_cycle hm ep eq ((hcyc _ _).mp h)
  classical
  by_contra he
  have nz (j : Fin m) : f j ≠ z := fun h => hz (mem_indexSet.mpr ⟨j,h⟩)
  have hd (j : Fin m) (hj : CycleAdj i j) : ¬ G.Adj z (f j) :=
    fun h => he ⟨j,h,hj⟩
  exact hd q eq (hclaw (e p ep) (e q eq) hi.symm
    (fun h => hpq (f.injective h)) (nz p) (nz q) hn
    (fun h => hd p ep h.symm)).symm

private theorem path_replace_first {z : V} (hz : z ∉ indexSet f) (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hprof : ∀ i, 0 < i.val → (G.Adj z (f i) ↔ i.val=1)) :
    ∃ g : Fin m ↪ V, (∀ i j, G.Adj (g i) (g j) ↔ PathAdj i j) ∧
      ∀ i : Fin m, 0 < i.val → ∃ j, g j = f i := by
  let g0 (i : Fin m) := if i.val=0 then z else f i
  have inj : Function.Injective g0 := by
    intro a b e
    unfold g0 at e
    by_cases ha : a.val=0 <;> by_cases hb : b.val=0
    · exact Fin.ext (ha.trans hb.symm)
    · exfalso; exact hz (mem_indexSet.mpr ⟨b,by simpa [ha,hb] using e.symm⟩)
    · exfalso; exact hz (mem_indexSet.mpr ⟨a,by simpa [ha,hb] using e⟩)
    · exact f.injective (by simpa [ha,hb] using e)
  refine ⟨⟨g0,inj⟩,?_,?_⟩
  · intro i j
    change G.Adj (g0 i) (g0 j) ↔ _
    unfold g0 PathAdj
    by_cases hi : i.val=0 <;> by_cases hj : j.val=0
    · simp [hi,hj]
    · rw [if_pos hi,if_neg hj,hprof j (by omega)]
      omega
    · rw [if_neg hi,if_pos hj, G.adj_comm, hprof i (by omega)]
      omega
    · rw [if_neg hi,if_neg hj,hcyc]
      unfold CycleAdj
      omega
  · intro i hi
    exact ⟨i,by change g0 i=f i; simp [g0, Nat.ne_of_gt hi]⟩

private theorem path_replace_last {z : V} (hz : z ∉ indexSet f) (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hprof : ∀ i, 0 < i.val → (G.Adj z (f i) ↔ i.val+1=m)) :
    ∃ g : Fin m ↪ V, (∀ i j, G.Adj (g i) (g j) ↔ PathAdj i j) ∧
      ∀ i : Fin m, 0 < i.val → ∃ j, g j = f i := by
  let g0 (i : Fin m) := if hi : i.val+1<m then f ⟨i.val+1,hi⟩ else z
  have inj : Function.Injective g0 := by
    intro a b e
    unfold g0 at e
    have ha' := a.isLt
    have hb' := b.isLt
    by_cases ha : a.val+1<m <;> by_cases hb : b.val+1<m
    · rw [dif_pos ha,dif_pos hb] at e
      have h := congrArg Fin.val (f.injective e)
      apply Fin.ext
      change a.val+1=b.val+1 at h
      omega
    · exfalso; exact hz (mem_indexSet.mpr ⟨⟨a.val+1,ha⟩,by simpa [ha,hb] using e⟩)
    · exfalso; exact hz (mem_indexSet.mpr ⟨⟨b.val+1,hb⟩,by simpa [ha,hb] using e.symm⟩)
    · exact Fin.ext (by omega)
  refine ⟨⟨g0,inj⟩,?_,?_⟩
  · intro i j
    change G.Adj (g0 i) (g0 j) ↔ _
    unfold g0 PathAdj
    have hi' := i.isLt
    have hj' := j.isLt
    by_cases hi : i.val+1<m <;> by_cases hj : j.val+1<m
    · rw [dif_pos hi,dif_pos hj,hcyc]
      unfold CycleAdj
      simp only
      omega
    · rw [dif_pos hi,dif_neg hj,G.adj_comm,hprof ⟨i.val+1,hi⟩ (by simp)]
      simp only
      omega
    · rw [dif_neg hi,dif_pos hj,hprof ⟨j.val+1,hj⟩ (by simp)]
      simp only
      omega
    · rw [dif_neg hi,dif_neg hj]
      have hn : ¬ G.Adj z z := G.loopless _
      exact ⟨fun h => (hn h).elim, fun h => by omega⟩
  · intro i hi
    let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
    have hj : j.val+1<m := by have := i.isLt; change i.val-1+1<m; omega
    refine ⟨j,?_⟩
    change g0 j=f i
    rw [show g0 j = f ⟨j.val+1,hj⟩ by simp [g0,hj]]
    congr 1
    exact Fin.ext (by change i.val-1+1=i.val; omega)


private theorem pair_cannot_touch {u v : Fin m}
    (hm : 7 ≤ m) (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hmarked : NoLargeMarked G (f u) (f v) m) (huv : ¬ G.Adj (f u) (f v))
    {z : V} (hz : z ∉ indexSet f) {a b : Fin m} (hab : CycleAdj a b)
    (hp : ∀ i : Fin m, G.Adj z (f i) ↔ i=a ∨ i=b) : False := by
  classical
  have pick : ∃ r t : Fin m, r ≠ u ∧ r ≠ v ∧ CycleAdj r t ∧
      (∀ i : Fin m, G.Adj z (f i) ↔ i=r ∨ i=t) := by
    by_cases hau : a=u
    · subst a
      have hb₁ : b ≠ u := by
        intro he; subst b
        exact G.loopless _ ((hcyc _ _).mpr hab)
      have hb₂ : b ≠ v := by
        intro he; subst b
        exact huv ((hcyc _ _).mpr hab)
      exact ⟨b,u,hb₁,hb₂,cyc_symm hab,fun i => (hp i).trans or_comm⟩
    by_cases hav : a=v
    · subst a
      have hb₁ : b ≠ u := by
        intro he; subst b
        exact huv ((hcyc _ _).mpr hab).symm
      have hb₂ : b ≠ v := by
        intro he; subst b
        exact G.loopless _ ((hcyc _ _).mpr hab)
      exact ⟨b,v,hb₁,hb₂,cyc_symm hab,fun i => (hp i).trans or_comm⟩
    exact ⟨a,b,hau,hav,hab,hp⟩
  obtain ⟨r,t,hru,hrv,hrt,hp'⟩ := pick
  let F := (rotEmb r).trans f
  let zero : Fin m := ⟨0,by omega⟩
  obtain ⟨a,ha⟩ := rot_surjective r t
  have hrot0 : rot r zero = r := rot_zero r (by omega)
  have h0 : CycleAdj zero a := by
    apply (cycleAdj_rotate (by omega) r zero a).mp
    rw [hrot0,ha]
    exact hrt
  have hod : a.val=1 ∨ a.val+1=m := by
    unfold CycleAdj at h0
    change 0+1=a.val ∨ a.val+1=0 ∨ (0=0 ∧ a.val+1=m) ∨
      (a.val=0 ∧ 0+1=m) at h0
    omega
  have hz' : z ∉ indexSet F := by
    simpa only [F,indexSet_rot] using hz
  have hf' (i j : Fin m) : G.Adj (F i) (F j) ↔ CycleAdj i j :=
    (hcyc _ _).trans (cycleAdj_rotate (by omega) r i j)
  have hi' (i : Fin m) (hi : 0 < i.val) : G.Adj z (F i) ↔ i=a := by
    change G.Adj z (f (rot r i)) ↔ i=a
    rw [hp']
    constructor
    · rintro (h|h)
      · have e := rot_injective r (h.trans hrot0.symm)
        have hh : i.val = 0 := congrArg Fin.val e
        omega
      · exact rot_injective r (h.trans ha.symm)
    · intro h; right; simpa [h] using ha
  have mark_inc {u : Fin m} (hru : r ≠ u)
      {g : Fin m ↪ V} (hg : ∀ i : Fin m, 0 < i.val → ∃ j, g j = F i) :
      ∃ i, g i = f u := by
    obtain ⟨k,hk⟩ := rot_surjective r u
    have hk' : 0 < k.val := by
      by_contra h
      have he : k = zero := Fin.ext (by change k.val = 0; omega)
      exact hru (hrot0.symm.trans (he ▸ hk))
    obtain ⟨j,hj⟩ := hg k hk'
    refine ⟨j,hj.trans ?_⟩
    exact congrArg f hk
  rcases hod with h1|hl
  · have hq (i : Fin m) (hi : 0 < i.val) : G.Adj z (F i) ↔ i.val=1 :=
      (hi' i hi).trans (by rw [Fin.ext_iff,h1])
    obtain ⟨g,hg,hmem⟩ := path_replace_first hz' hm hf' hq
    exact no_large_path hmarked g (by omega) hg (mark_inc hru hmem) (mark_inc hrv hmem)
  · have hq (i : Fin m) (hi : 0 < i.val) : G.Adj z (F i) ↔ i.val+1=m :=
      (hi' i hi).trans (by rw [Fin.ext_iff]; omega)
    obtain ⟨g,hg,hmem⟩ := path_replace_last hz' hm hf' hq
    exact no_large_path hmarked g (by omega) hg (mark_inc hru hmem) (mark_inc hrv hmem)

theorem contacts_large_if_touch (hm : 7 ≤ m) {u v : Fin m}
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hclaw : ClawFree G) (hmarked : NoLargeMarked G (f u) (f v) m)
    (huv : ¬ G.Adj (f u) (f v)) {z : V} (hz : z ∉ indexSet f)
    (ht : ∃ i : Fin m, G.Adj z (f i)) : 3 ≤ (contacts G f z).card := by
  classical
  obtain ⟨a,ha⟩ := ht
  obtain ⟨b,hb,hab⟩ := contacts_no_isolated hm hcyc hclaw hz a ha
  by_contra h
  have hne : a ≠ b := by intro e; subst b; exact G.loopless _ ((hcyc _ _).mpr hab)
  have hs : ({a,b} : Finset (Fin m)) ⊆ contacts G f z := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact mem_contacts.mpr ha
    · exact mem_contacts.mpr hb
  have hc : ({a,b} : Finset (Fin m)).card = 2 := by simp [hne]
  have he := Finset.eq_of_subset_of_card_le hs (by omega)
  exact pair_cannot_touch hm hcyc hmarked huv hz hab (fun i => by
    rw [← mem_contacts,← he]
    simp)

theorem cycle_contact_conditions (hm : 7 ≤ m) {u v : Fin m}
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hc : G.Connected) (hclaw : ClawFree G)
    (hmarked : NoLargeMarked G (f u) (f v) m)
    (huv : ¬ G.Adj (f u) (f v)) : ContactConditions G f := by
  classical
  let T (z : V) := ∃ i : Fin m, G.Adj z (f i)
  have hin (i : Fin m) : T (f i) :=
    ⟨succFin i,(hcyc _ _).mpr ((cycleAdj_iff_succ (by omega)).mpr (Or.inl rfl))⟩
  have hclose {x y : V} (e : G.Adj x y) (hx : T x) : T y := by
    by_cases hxi : x ∈ indexSet f
    · obtain ⟨i,hi⟩ := mem_indexSet.mp hxi
      exact ⟨i,hi.symm ▸ e.symm⟩
    by_contra hy
    have hbig := contacts_large_if_touch hm hcyc hclaw hmarked huv hxi hx
    obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp (by omega :
      2 < (contacts G f x).card)
    have has_pair : ∃ i j : Fin m, G.Adj x (f i) ∧ G.Adj x (f j) ∧ i ≠ j ∧
        ¬ G.Adj (f i) (f j) := by
      by_cases ab : G.Adj (f a) (f b)
      · by_cases ac : G.Adj (f a) (f c)
        · by_cases bc : G.Adj (f b) (f c)
          · exact (no_tri_in_cycle hm ((hcyc _ _).mp ab) ((hcyc _ _).mp ac)
              ((hcyc _ _).mp bc)).elim
          · exact ⟨b,c,mem_contacts.mp hb,mem_contacts.mp hc,hbc,bc⟩
        · exact ⟨a,c,mem_contacts.mp ha,mem_contacts.mp hc,hac,ac⟩
      · exact ⟨a,b,mem_contacts.mp ha,mem_contacts.mp hb,hab,ab⟩
    obtain ⟨i,j,hi,hj,hij,hn⟩ := has_pair
    have hny (k : Fin m) : y ≠ f k := by
      intro h; exact hy (h.symm ▸ hin k)
    have hna (k : Fin m) : ¬ G.Adj (f k) y := fun hh => hy ⟨k,hh.symm⟩
    exact hna j (hclaw hi hj e (fun h => hij (f.injective h))
      (hny i).symm (hny j).symm hn (hna i))
  have across {a b : V} (p : G.Walk a b) : T a → T b := by
    induction p with
    | nil => exact id
    | cons e p ih => exact fun hx => ih (hclose e hx)
  constructor
  · intro z hz
    let r : Fin m := ⟨0,by omega⟩
    obtain ⟨p⟩ := hc (f r) z
    exact contacts_large_if_touch hm hcyc hclaw hmarked huv hz (across p (hin r))
  · intro z hz i hi
    obtain ⟨j,hj,he⟩ := contacts_no_isolated hm hcyc hclaw hz i (mem_contacts.mp hi)
    exact ⟨j,mem_contacts.mpr hj,he⟩


private theorem no_three_independent_contacts (hcyc : ∀ i j,
    G.Adj (f i) (f j) ↔ CycleAdj i j) (hclaw : ClawFree G) {z : V}
    {a b c : Fin m} (ha : G.Adj z (f a)) (hb : G.Adj z (f b)) (hc : G.Adj z (f c))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (nab : ¬ CycleAdj a b) (nac : ¬ CycleAdj a c) (nbc : ¬ CycleAdj b c) : False :=
  nbc ((hcyc _ _).mp (hclaw ha hb hc (fun e => hab (f.injective e))
    (fun e => hac (f.injective e)) (fun e => hbc (f.injective e))
    (fun e => nab ((hcyc _ _).mp e)) (fun e => nac ((hcyc _ _).mp e))))

/-- After cutting at a missing vertex, the contact set is one interval of length 3 or 4,
or precisely two intervals of length 2 separated by a gap. -/
private theorem classify_linear (hm : 7 ≤ m) (S : Finset (Fin m))
    (h0 : ∀ i ∈ S, 0 < i.val) (hbig : 3 ≤ S.card)
    (hni : ∀ i ∈ S, ∃ j ∈ S, CycleAdj i j)
    (hno : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a.val+2 ≤ b.val → b.val+2 ≤ c.val → False) :
    ∃ a : Fin m, a ∈ S ∧
      ((∃ k : ℕ, (k=3 ∨ k=4) ∧ a.val+k ≤ m ∧
          ∀ i : Fin m, i ∈ S ↔ a.val ≤ i.val ∧ i.val < a.val+k) ∨
       ∃ b : Fin m, b ∈ S ∧ a.val+3 ≤ b.val ∧ b.val+1 < m ∧
          (∀ i : Fin m, i ∈ S ↔ i.val=a.val ∨ i.val=a.val+1 ∨
            i.val=b.val ∨ i.val=b.val+1)) := by
  classical
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image S Fin.val (Finset.card_pos.mp (by omega))
  obtain ⟨ap,hap,he⟩ := hni a ha
  have ha0 := h0 a ha
  have hap0 := h0 ap hap
  have hmn := hmin ap hap
  have h1 : ap.val=a.val+1 := by unfold CycleAdj at he; omega
  have apm := ap.isLt
  refine ⟨a,ha,?_⟩
  by_cases hh : ∃ y ∈ S, y.val = a.val+2
  · obtain ⟨q,hq,hqv⟩ := hh
    have hcap (i : Fin m) (hi : i ∈ S) : i.val ≤ a.val+3 := by
      by_contra hn
      exact hno a ha q hq i hi (by omega) (by omega)
    by_cases ht : ∃ y ∈ S, y.val=a.val+3
    · obtain ⟨r,hr,hrv⟩ := ht
      refine Or.inl ⟨4,Or.inr rfl,by have := r.isLt; omega,?_⟩
      intro i
      constructor
      · exact fun hi => ⟨hmin i hi,by have := hcap i hi; omega⟩
      · rintro ⟨hlo,hhi⟩
        have h : i=a ∨ i=ap ∨ i=q ∨ i=r := by
          simp only [Fin.ext_iff]
          omega
        rcases h with rfl|rfl|rfl|rfl <;> assumption
    · refine Or.inl ⟨3,Or.inl rfl,by have := q.isLt; omega,?_⟩
      intro i
      constructor
      · intro hi
        have hd : i.val ≠ a.val+3 := fun e => ht ⟨i,hi,e⟩
        exact ⟨hmin i hi,by have := hcap i hi; omega⟩
      · rintro ⟨hlo,hhi⟩
        have h : i=a ∨ i=ap ∨ i=q := by simp only [Fin.ext_iff]; omega
        rcases h with rfl|rfl|rfl <;> assumption
  · let T := S.filter (fun i => a.val+1 < i.val)
    have hT : T.Nonempty := by
      by_contra h
      have hsub : S ⊆ ({a,ap} : Finset (Fin m)) := by
        intro i hi
        have hlo := hmin i hi
        have hhi : ¬ a.val+1 < i.val := fun e =>
          h ⟨i,Finset.mem_filter.mpr ⟨hi,e⟩⟩
        simp only [mem_insert,mem_singleton,Fin.ext_iff]
        omega
      have hsmall := Finset.card_le_card hsub
      have hne : a ≠ ap := by intro e; have h := congrArg Fin.val e; omega
      rw [show ({a,ap} : Finset (Fin m)).card = 2 by simp [hne]] at hsmall
      omega
    obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image T Fin.val hT
    obtain ⟨hbs,hba⟩ := Finset.mem_filter.mp hb
    have hba' : a.val+3 ≤ b.val := by
      have hv : b.val ≠ a.val+2 := fun e => hh ⟨b,hbs,e⟩
      omega
    obtain ⟨bp,hbp,hbeb⟩ := hni b hbs
    have hb0 := h0 b hbs
    have hbp0 := h0 bp hbp
    have hbp' : bp.val = b.val+1 := by
      have hh₁ : ¬ bp.val+1=b.val := by
        intro e
        have hh₂ : bp.val ≠ a.val+2 := fun e => hh ⟨bp,hbp,e⟩
        have hmem : bp ∈ T := Finset.mem_filter.mpr ⟨hbp,by omega⟩
        have hc := hbmin bp hmem
        omega
      unfold CycleAdj at hbeb
      omega
    have hbpM := bp.isLt
    refine Or.inr ⟨b,hbs,hba',by omega,?_⟩
    intro i
    constructor
    · intro hi
      have hlo : a.val ≤ i.val := hmin i hi
      by_cases hi' : a.val+1 < i.val
      · have hlow := hbmin i (Finset.mem_filter.mpr ⟨hi,hi'⟩)
        change b.val ≤ i.val at hlow
        have hhi : i.val ≤ b.val+1 := by
          by_cases he : i.val ≤ b.val+1
          · exact he
          · exact (hno a ha b hbs i hi (by omega) (by omega)).elim
        omega
      · omega
    · intro hi
      have he : i=a ∨ i=ap ∨ i=b ∨ i=bp := by
        simp only [Fin.ext_iff]
        omega
      rcases he with rfl|rfl|rfl|rfl <;> assumption

theorem outside_profile_of_conditions (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hclaw : ClawFree G) (hcond : ContactConditions G f)
    {z : V} (hz : z ∉ indexSet f) :
    (∃ a : Fin m, ∃ k : ℕ, (k=3 ∨ k=4) ∧
      ∀ i : Fin m, G.Adj z (f (rot a i)) ↔ i.val < k) ∨
    ∃ a : Fin m, ∃ d : ℕ, 3 ≤ d ∧ d ≤ m-3 ∧
      (∀ i : Fin m, G.Adj z (f (rot a i)) ↔
        i.val=0 ∨ i.val=1 ∨ i.val=d ∨ i.val=d+1) := by
  classical
  let i0 : Fin m := ⟨0,by omega⟩
  let i2 : Fin m := ⟨2,by omega⟩
  let i4 : Fin m := ⟨4,by omega⟩
  have hmiss : ∃ s : Fin m, ¬ G.Adj z (f s) := by
    by_contra hn
    push_neg at hn
    exact no_three_independent_contacts hcyc hclaw (hn i0) (hn i2) (hn i4)
      (by intro e; have h := congrArg Fin.val e; dsimp [i0,i2] at h; omega)
      (by intro e; have h := congrArg Fin.val e; dsimp [i0,i4] at h; omega)
      (by intro e; have h := congrArg Fin.val e; dsimp [i2,i4] at h; omega)
      (by unfold CycleAdj; dsimp [i0,i2]; omega)
      (by unfold CycleAdj; dsimp [i0,i4]; omega)
      (by unfold CycleAdj; dsimp [i2,i4]; omega)
  obtain ⟨s,hs⟩ := hmiss
  let F := (rotEmb s).trans f
  have hf' (i j : Fin m) : G.Adj (F i) (F j) ↔ CycleAdj i j :=
    (hcyc _ _).trans (cycleAdj_rotate (by omega) s i j)
  have hc' := contact_conditions_rotate (by omega) f hcond s
  have hz' : z ∉ indexSet F := by simpa only [F,indexSet_rot] using hz
  let S := contacts G F z
  have hlo (i : Fin m) (hi : i ∈ S) : 0 < i.val := by
    by_cases hn : i.val=0
    · exfalso
      have he : i = i0 := Fin.ext hn
      have ht := mem_contacts.mp hi
      change G.Adj z (f (rot s i)) at ht
      rw [he,rot_zero] at ht
      exact hs ht
    · omega
  have hno (a : Fin m) (ha : a ∈ S) (b : Fin m) (hb : b ∈ S)
      (c : Fin m) (hc : c ∈ S) (hab : a.val+2 ≤ b.val) (hbc : b.val+2 ≤ c.val) : False := by
    have aux (i j : Fin m) (hi : i ∈ S) (hj : j ∈ S) (he : i.val+2 ≤ j.val) :
        i ≠ j ∧ ¬ CycleAdj i j := by
      constructor
      · intro e; have := congrArg Fin.val e; omega
      · intro e; have := hlo i hi; have := hlo j hj; unfold CycleAdj at e; omega
    obtain ⟨hne,hn⟩ := aux a b ha hb hab
    obtain ⟨hne',hn'⟩ := aux a c ha hc (by omega)
    obtain ⟨hne'',hn''⟩ := aux b c hb hc hbc
    exact no_three_independent_contacts hf' hclaw (mem_contacts.mp ha) (mem_contacts.mp hb)
      (mem_contacts.mp hc) hne hne' hne'' hn hn' hn''
  obtain ⟨a,ha,hclass⟩ := classify_linear hm S hlo (hc'.big z hz')
    (hc'.no_isolated z hz') hno
  have hval (i : Fin m) : (rot a i).val = (a.val+i.val)%m := rfl
  have hAdj (i : Fin m) : G.Adj z (f (rot (rot s a) i)) ↔ rot a i ∈ S := by
    rw [rot_assoc,mem_contacts]
    rfl
  rcases hclass with ⟨k,hk,hka,hprof⟩|⟨b,hb,hgap,hbm,hprof⟩
  · refine Or.inl ⟨rot s a,k,hk,fun i => (hAdj i).trans ?_⟩
    rw [hprof,hval]
    have hi := i.isLt
    by_cases hlt : a.val+i.val < m
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have eq : (a.val+i.val)%m = a.val+i.val-m := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by have := a.isLt; omega)]
      rw [eq]
      omega
  · refine Or.inr ⟨rot s a,b.val-a.val,by omega,by have := hlo a ha; omega,
      fun i => (hAdj i).trans ?_⟩
    rw [hprof,hval]
    have hi := i.isLt
    by_cases hlt : a.val+i.val < m
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have eq : (a.val+i.val)%m = a.val+i.val-m := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by have := a.isLt; omega)]
      rw [eq]
      omega

#print axioms cycle_contact_conditions
#print axioms outside_profile_of_conditions

end Graffiti183.Exceptional
