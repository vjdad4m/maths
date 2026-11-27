import RoundedBand133

namespace Graffiti133RevisitSix
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

private def hex (i j : Fin 6) : Prop := i + 1 = j ∨ j + 1 = i
private instance : DecidableRel hex := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private def reserved (b : Fin 6 → Bool) (i j : Fin 7) : Prop :=
  if hi : i.val < 6 then
    if hj : j.val < 6 then hex ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else b ⟨i.val,hi⟩ = true
  else if hj : j.val < 6 then b ⟨j.val,hj⟩ = true else False
private instance (b : Fin 6 → Bool) : DecidableRel (reserved b) := by
  intro i j
  unfold reserved
  split <;> split <;> infer_instance

private def spokePath (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6, i.castSucc, (i + (if positive then 1 else 5)).castSucc,
    (i + (if positive then 2 else 4)).castSucc, (i + 3).castSucc,
    (i + (if positive then 4 else 2)).castSucc]

private lemma computed_spokePath : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ u v : Fin 6, spokePath i pos u = spokePath i pos v → u = v) ∧
      ∀ u v : Fin 6, u < v → (reserved b (spokePath i pos u) (spokePath i pos v) ↔
        u.val + 1 = v.val) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An induced path remains induced when a new vertex is joined solely
to its first vertex. -/
theorem prepend_induced_with_positions {k : ℕ} (hk : 0 < k) {f : Fin k → V}
    (hf : InducedPath G f) (w : V) (hnew : ∀ i, w ≠ f i)
    (h₀ : G.Adj w (f ⟨0,hk⟩)) (h₁ : ∀ i : Fin k, 0 < i.val → ¬ G.Adj w (f i)) :
    ∃ ff : Fin (k+1) → V, InducedPath G ff ∧ ff ⟨0,by omega⟩ = w ∧
      ∀ i : Fin (k+1), ∀ hi : 0 < i.val, ff i = f ⟨i.val-1,by have := i.isLt; omega⟩ := by
  let F (i : Fin (k+1)) : V :=
    if h : i.val = 0 then w else f ⟨i.val-1,by omega⟩
  have head (i : Fin (k+1)) (hi : i.val = 0) : F i = w := dif_pos hi
  have tail (i : Fin (k+1)) (hi : i.val ≠ 0) :
      F i = f ⟨i.val-1,by have := i.isLt; omega⟩ := dif_neg hi
  refine ⟨F,⟨?_,?_⟩,head _ rfl, fun i hi => tail i (by omega)⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · rw [head _ hi,tail _ hj] at h
      exact (hnew _ h).elim
    · rw [tail _ hi,head _ hj] at h
      exact (hnew _ h.symm).elim
    · rw [tail _ hi,tail _ hj] at h
      have hh := congrArg Fin.val (hf.1 h)
      change i.val-1 = j.val-1 at hh
      omega
  · intro i j hij
    change i.val < j.val at hij
    have hji := j.isLt
    have hj : j.val ≠ 0 := by omega
    rw [tail _ hj]
    by_cases hi : i.val = 0
    · rw [head _ hi]
      by_cases h : j.val = 1
      · have hindex : (⟨j.val-1,by omega⟩ : Fin k) = ⟨0,hk⟩ :=
          Fin.ext (by change j.val-1=0; omega)
        rw [hindex]
        exact iff_of_true h₀ (by omega)
      · exact iff_of_false (h₁ _ (by change 0 < j.val-1; omega)) (by omega)
    · rw [tail _ hi,hf.2 _ _ (by change i.val-1 < j.val-1; omega)]
      change (i.val-1+1 = j.val-1) ↔ (i.val+1 = j.val)
      omega

private theorem neighbor_pair (v : V) (hv : 2 ≤ localIndependence G v) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ¬G.Adj x y := by
  classical
  have m (s : Finset V) : s ∈ localIndependentSets G v ↔
      (∀ x ∈ s, G.Adj v x) ∧ (∀ x ∈ s, ∀ y ∈ s, ¬G.Adj x y) := by
    simp [localIndependentSets, Finset.subset_iff]
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, m _ |>.mpr (by simp)⟩
  have hi : localIndependence G v ≤ A.card := Finset.sup_le_iff.mpr hM
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hA := (m _).mp hA
  exact ⟨x,y,hxy,hA.1 x hx,hA.1 y hy,hA.2 x hx y hy⟩

private theorem side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  obtain ⟨x,y,hne,hx,hy,hxy⟩ := neighbor_pair v hv
  by_cases ex : x = s
  · subst x
    exact ⟨y,hy,hne.symm,fun h => hxy h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,hx,hne,hxy⟩
  by_cases es : G.Adj x s
  · have no : ¬ G.Adj y s := by
      intro hb
      exact hne (h4 v s x y e.ne hx es.symm hy hb.symm)
    exact ⟨y,hy,ey,no⟩
  · exact ⟨x,hx,ex,es⟩

private theorem short_neighbor (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {k : ℕ} (hk : 2 ≤ k) {f : Fin k → V}
    (p : InducedPath G f) (hv : 2 ≤ localIndependence G (f ⟨0,by omega⟩)) :
    ∃ w, (∀ i, w ≠ f i) ∧ G.Adj w (f ⟨0,by omega⟩) ∧
      (∀ i : Fin k, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (f i)) := by
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have e : G.Adj (f a) (f b) := (p.2 a b (by change 0<1; decide)).mpr rfl
  obtain ⟨w,ew,hw,hwB⟩ := side_neighbor h4 e hv
  have off (i : Fin k) : w ≠ f i := by
    intro eq
    by_cases h : i = a
    · rw [h] at eq
      exact ew.ne eq.symm
    · have hlt : a < i := by
        change 0 < i.val
        apply Nat.pos_of_ne_zero
        intro he
        exact h (Fin.ext he)
      have j := (p.2 a i hlt).mp (eq ▸ ew)
      have eqi : i = b := Fin.ext j.symm
      exact hw (eq.trans (congrArg f eqi))
  have no2 {i : Fin k} (hi : i.val = 2) : ¬G.Adj w (f i) := by
    intro ewi
    have ebi := (p.2 b i (by change 1 < i.val; omega)).mpr (by change 2=i.val; omega)
    have eq := h4 (f a) (f i) w (f b) (fun h => by
      have hh := congrArg Fin.val (p.1 h)
      change 0 = i.val at hh
      omega) ew ewi.symm e ebi.symm
    exact hw eq
  refine ⟨w,off,ew.symm,?_⟩
  intro i hlo hhi
  rcases (show i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with h | h | h
  · have ei : i = b := Fin.ext h
    exact ei ▸ hwB
  · exact no2 h
  · intro ewi
    let j : Fin k := ⟨2,by have := i.isLt; omega⟩
    have eBj := (p.2 b j (by change 1<2; decide)).mpr rfl
    have eji := (p.2 j i (by change 2 < i.val; omega)).mpr (by change 3=i.val; omega)
    have hIndices : [a,b,j,i].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      constructor
      · intro neq
        rcases neq with q | q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
      · constructor
        · intro neq
          rcases neq with q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
        · refine ⟨?_, by trivial⟩
          intro q
          have hh := congrArg Fin.val q
          dsimp [j] at hh
          omega
    have hLists : [w,f a,f b,f j,f i].Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨by simp [off],?_⟩
      simpa using hIndices.map p.1
    exact h5 _ _ _ _ _ hLists ew.symm e eBj eji ewi.symm

private theorem short_path_through (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (mind : ∀ x, 2 ≤ localIndependence G x) (v : V) :
    ∃ f : Fin 5 → V, InducedPath G f ∧ ∃ i, f i = v := by
  have p2 : ∃ f : Fin 2 → V, InducedPath G f ∧ ∃ i, f i = v := by
    obtain ⟨x,y,hxy,hx,hy,no⟩ := neighbor_pair v (mind v)
    refine ⟨![v,x],⟨?_,?_⟩,0,rfl⟩
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [hx.ne,hx.ne.symm]
    · intro a b h
      fin_cases a <;> fin_cases b <;> first | contradiction | exact iff_of_true hx rfl
  have onward : ∀ d : ℕ, d ≤ 3 → ∃ f : Fin (d+2) → V, InducedPath G f ∧ ∃ i, f i = v := by
    intro d
    induction d with
    | zero => intro _; exact p2
    | succ d ih =>
      intro hD
      obtain ⟨f,hf,i,hi⟩ := ih (by omega)
      obtain ⟨w,hw,e,no⟩ := short_neighbor h4 h5 (by omega) hf (mind _)
      obtain ⟨g,hg,_,tail⟩ := prepend_induced_with_positions (by omega) hf w hw e
        (fun i hi => no i hi (by have := i.isLt; omega))
      let j : Fin (d+2+1) := ⟨i.val+1, by have := i.isLt; omega⟩
      have he := tail j (show 0 < j.val by dsimp [j]; omega)
      have hj : (⟨j.val-1,by have := i.isLt; dsimp [j]; omega⟩ : Fin (d+2)) = i :=
        Fin.ext (by dsimp [j])
      exact ⟨g,hg,j,he.trans (hj.symm ▸ hi)⟩
  exact onward 3 (by decide)


private theorem extend_hexagon (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) {c : Fin 6 → V}
    (inj : Function.Injective c) (hcycle : ∀ i j, G.Adj (c i) (c j) ↔ hex i j)
    (x : V) (hx : ∀ i, x ≠ c i) (ha : ∃ i, G.Adj x (c i)) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (c i))
  have btrue (i : Fin 6) : b i = true ↔ G.Adj x (c i) := by simp [b]
  have d2 (i : Fin 6) (h : b i = true) : b (i+2) = false := by
    cases e : b (i+2)
    · rfl
    · have e1 : hex i (i+1) := Or.inl rfl
      have e2 : hex (i+1) (i+2) := Or.inl (by fin_cases i <;> decide)
      have eq := h4 (c i) (c (i+2)) x (c (i+1))
        (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (inj w))
        ((btrue _).mp h).symm ((btrue _).mp e).symm
        ((hcycle _ _).mpr e1) ((hcycle _ _).mpr e2).symm
      exact False.elim (hx _ eq)
  have d3 (i : Fin 6) (h : b i = true) : b (i+3) = false := by
    cases e : b (i+3)
    · rfl
    · have ei : [i,i+1,i+2,i+3].Nodup :=
        (by decide : ∀ a : Fin 6, [a,a+1,a+2,a+3].Nodup) i
      have hh : [x,c i,c (i+1),c (i+2),c (i+3)].Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨by simp [hx],?_⟩
        simpa using ei.map inj
      exact (h5 _ _ _ _ _ hh ((btrue _).mp h) ((hcycle _ _).mpr (Or.inl rfl))
        ((hcycle _ _).mpr (Or.inl (by fin_cases i <;> decide)))
        ((hcycle _ _).mpr (Or.inl (by fin_cases i <;> decide)))
        ((btrue _).mp e).symm).elim
  obtain ⟨i,pos,hi,hs⟩ := computed_spokePath b (fun i h => ⟨d2 i h,d3 i h⟩) (by
    obtain ⟨i,he⟩ := ha
    exact ⟨i,(btrue _).mpr he⟩)
  let g (r : Fin 7) : V := if hr : r.val < 6 then c ⟨r.val,hr⟩ else x
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 6 <;> by_cases hB : b.val < 6
    · have he := inj (show c ⟨a.val,hA⟩ = c ⟨b.val,hB⟩ by simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun t : Fin 6 => t.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin 7) : G.Adj (g a) (g q) ↔ reserved b a q := by
    by_cases hA : a.val < 6 <;> by_cases hQ : q.val < 6
    · simpa only [g,reserved,dif_pos hA,dif_pos hQ] using hcycle ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,reserved,dif_pos hA,dif_neg hQ,G.adj_comm] using (btrue ⟨a.val,hA⟩).symm
    · simpa only [g,reserved,dif_neg hA,dif_pos hQ] using (btrue ⟨q.val,hQ⟩).symm
    · simp [g,reserved,hA,hQ]
  exact ⟨g ∘ spokePath i pos,ginj.comp hi,fun a q he => (hrel _ _).trans (hs a q he)⟩


private lemma hex_interior : ∀ i j : Fin 5,
    hex i.castSucc j.castSucc ↔ i.val+1=j.val ∨ j.val+1=i.val := by decide
private lemma hex_edge : ∀ i : Fin 5, hex i.castSucc (5 : Fin 6) ↔ i.val=0 ∨ i.val=4 := by decide
private lemma hex_diag : ∀ i : Fin 6, ¬hex i i := by decide
private lemma hex_neighbor_indices : ∀ i j : Fin 6, hex i j → j = i+1 ∨ j = i+5 := by decide
private theorem hex_symm (i j : Fin 6) : hex i j ↔ hex j i := or_comm

private theorem make_hex {p : Fin 5 → V} (hp : InducedPath G p) (w : V)
    (hw : ∀ i, w ≠ p i) (h0 : G.Adj w (p 0)) (h4 : G.Adj w (p 4))
    (hm : ∀ i : Fin 5, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (p i)) :
    ∃ c : Fin 6 → V, Function.Injective c ∧
      (∀ i j, G.Adj (c i) (c j) ↔ hex i j) ∧ ∀ i, c i.castSucc = p i := by
  let c (i : Fin 6) := if hi : i.val < 5 then p ⟨i.val,hi⟩ else w
  have cP (i : Fin 5) : c i.castSucc = p i := by simp [c,i.isLt]
  have cW : c 5 = w := by rfl
  have other (i : Fin 6) : (∃ a : Fin 5, i = a.castSucc) ∨ i = (5 : Fin 6) := by
    by_cases hi : i.val < 5
    · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by change i.val = 5; have := i.isLt; omega))
  have inj : Function.Injective c := by
    intro i j he
    rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
    · rw [cP,cP] at he
      exact congrArg Fin.castSucc (hp.1 he)
    · rw [cP,cW] at he
      exact (hw _ he.symm).elim
    · rw [cW,cP] at he
      exact (hw _ he).elim
    · rfl
  have interior (a b : Fin 5) : G.Adj (p a) (p b) ↔ a.val+1=b.val ∨ b.val+1=a.val := by
    rcases lt_trichotomy a b with lt | e | gt
    · rw [hp.2 a b lt]
      change a.val < b.val at lt
      omega
    · subst b
      simp [G.loopless]
    · rw [G.adj_comm,hp.2 b a gt]
      change b.val < a.val at gt
      omega
  have exterior (i : Fin 5) : G.Adj (p i) w ↔ i.val=0 ∨ i.val=4 := by
    constructor
    · intro e
      have := i.isLt
      by_cases h0 : i.val = 0
      · exact Or.inl h0
      · by_cases h4 : i.val = 4
        · exact Or.inr h4
        · exact (hm i (by omega) (by omega) e.symm).elim
    · rintro (he | he)
      · have hi : i = 0 := Fin.ext he
        exact hi ▸ h0.symm
      · have hi : i = 4 := Fin.ext he
        exact hi ▸ h4.symm
  refine ⟨c,inj,?_ ,cP⟩
  intro i j
  rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
  · rw [cP,cP,hex_interior]
    exact interior a b
  · rw [cP,cW,hex_edge]
    exact exterior a
  · rw [cW,cP,G.adj_comm,hex_symm,hex_edge]
    exact exterior b
  · exact iff_of_false (G.loopless _) (hex_diag _)

private theorem local_of_hex_no_P6 (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    {c : Fin 6 → V} (inj : Function.Injective c)
    (hs : ∀ i j, G.Adj (c i) (c j) ↔ hex i j)
    (no : ¬ ∃ f : Fin 6 → V, InducedPath G f) (i : Fin 6) :
    localIndependence G (c i) ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro s hs'
  have h := (Finset.mem_filter.mp hs').1
  have hN := Finset.mem_powerset.mp h
  have hsub : s ⊆ {c (i+1), c (i+5)} := by
    intro x hx
    have hadj := (Finset.mem_filter.mp (hN hx)).2
    by_cases he : ∃ j, c j = x
    · obtain ⟨j,rfl⟩ := he
      rcases hex_neighbor_indices i j ((hs _ _).mp hadj) with he | he <;> simp [he]
    · exact (no (extend_hexagon h4 h5 inj hs x
        (fun j he' => he ⟨j,he'.symm⟩) ⟨i,hadj.symm⟩)).elim
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

theorem six_path_of_min_and_high (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (mind : ∀ v, 2 ≤ localIndependence G v) (v : V) (high : 3 ≤ localIndependence G v) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨p,hp,i,hi⟩ := short_path_through h4 h5 mind v
  obtain ⟨w,hw,e,hn⟩ := short_neighbor h4 h5 (by decide) hp (mind _)
  have last : G.Adj w (p 4) := by
    apply Classical.byContradiction
    intro hn4
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp w hw e (by
      intro j hj
      by_cases j4 : j.val = 4
      · have he : j = 4 := Fin.ext j4
        exact he ▸ hn4
      · exact hn j hj (by have := j.isLt; omega))
    exact no ⟨q,hq⟩
  obtain ⟨c,inj,hs,hOld⟩ := make_hex hp w hw e last hn
  have hV : c i.castSucc = v := (hOld i).trans hi
  have low := local_of_hex_no_P6 h4 h5 inj hs no i.castSucc
  rw [hV] at low
  omega

/-- Local mean at least three yields an induced P6 when the graph has
neither a four-cycle nor a five-cycle. Connectivity is not required. -/
theorem P6_of_local_mean_three (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (hA : 3 ≤ averageLocal G) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  apply lift_local_density_path 6 1 3 (by decide) (by decide) G h4
    (nat_density_of_le_average G 3 hA)
  intro W _ _ J emb hj h4J hmin hD
  have h5J : NoSimpleFive133 J := by
    intro a b c d e hn e1 e2 e3 e4 e5
    have hx := hn.map emb.injective
    exact h5 _ _ _ _ _ (by simpa using hx) ((hj _ _).mp e1)
      ((hj _ _).mp e2) ((hj _ _).mp e3) ((hj _ _).mp e4) ((hj _ _).mp e5)
  obtain ⟨v,hv⟩ : ∃ v, 3 ≤ localIndependence J v := by
    apply Classical.byContradiction
    intro no
    have hBound (x : W) : localIndependence J x ≤ 2 := by
      have : localIndependence J x < 3 := Nat.lt_of_not_ge (fun h => no ⟨x,h⟩)
      omega
    have ht : (∑ x, localIndependence J x) ≤ 2 * Fintype.card W := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun x _ => hBound x)
      simpa [Nat.mul_comm] using hh
    have hpos := Fintype.card_pos (α:=W)
    omega
  exact six_path_of_min_and_high h4J h5J hmin v hv

#print axioms P6_of_local_mean_three

end Graffiti133RevisitSix
