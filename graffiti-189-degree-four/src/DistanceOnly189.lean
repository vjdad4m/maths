import Rigidity189

namespace Graffiti189LongestPath.DistanceOnly
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath Graffiti189LongestPath.Rigidity
set_option maxHeartbeats 3000000
variable {V : Type*} {G : SimpleGraph V}
private theorem no_endpoints {x a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) :
    ¬G.Adj x a ∧ ¬G.Adj x b := by
  constructor
  · intro h
    have hle := hp.2 x b (.cons h p) (hp.1.cons hx)
    simp at hle
  · intro h
    have hq : (Walk.cons h p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hx)).reverse
    have hle := hp.2 a x _ hq
    simp at hle

private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega


variable [Fintype V]
private theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]

variable [DecidableEq V] [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj] in
private theorem splice_walk {x y a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (hd : ∀ w ∈ q.support, w ∉ p.support) (i : ℕ) (hi : i < p.length)
    (h₀ : G.Adj (p.getVert i) x) (h₁ : G.Adj y (p.getVert (i + 1))) :
    ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length + q.length + 1 ∧
      ∀ w : V, w ∈ r.support ↔ w ∈ q.support ∨ w ∈ p.support := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons v w z hvw p ih =>
    cases i with
    | zero =>
      have hvx : G.Adj v x := h₀
      have hyw : G.Adj y w := by simpa using h₁
      have hv : v ∉ p.support := (cons_isPath_iff _ _).1 hp |>.2
      have hqapp : (q.append (.cons hyw p)).IsPath := by
        rw [isPath_def, support_append, List.nodup_append]
        refine ⟨hq.support_nodup, ?_, ?_⟩
        · simpa only [support_cons, List.tail_cons] using hp.of_cons.support_nodup
        · intro t ht ht'
          have hx' : t ∈ p.support := by simpa only [support_cons, List.tail_cons] using ht'
          exact hd t ht (by simp [hx'])
      refine ⟨.cons hvx _, hqapp.cons ?_, by simp; omega, ?_⟩
      · rw [mem_support_append_iff]
        intro hh
        rcases hh with hh | hh
        · exact hd v hh (by simp)
        · simp only [support_cons, List.mem_cons] at hh
          exact hh.elim (fun e => hd v (e.symm ▸ q.end_mem_support) (by simp)) hv
      · intro t
        simp only [support_cons, List.mem_cons, mem_support_append_iff]
        have hy : t = y → t ∈ q.support := fun e => e.symm ▸ q.end_mem_support
        tauto
    | succ i =>
      have hi' : i < p.length := by simp at hi; omega
      obtain ⟨r,hr,hlen,hsup⟩ := ih hp.of_cons
        (fun t ht hs => hd t ht (by simp [hs])) i hi' h₀ h₁
      refine ⟨.cons hvw r, hr.cons ?_, by simp [hlen]; omega, ?_⟩
      · rw [hsup]
        exact not_or.mpr ⟨fun e => hd v e (by simp), (cons_isPath_iff _ _).1 hp |>.2⟩
      · intro t
        simp only [support_cons, List.mem_cons, hsup]
        tauto

omit [Fintype V] [DecidableRel G.Adj] in
private theorem outside_edge {a b : V} (p : G.Walk a b) (hc : G.Connected)
    (hn : ∃ x, x ∉ p.support) :
    ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
  obtain ⟨x,hx⟩ := hn
  obtain ⟨q⟩ := hc x a
  have go {x z : V} (q : G.Walk x z) (hx : x ∉ p.support) (hz : z ∈ p.support) :
      ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
    induction q with
    | nil => exact (hx hz).elim
    | @cons u v w e q ih =>
      by_cases hv : v ∈ p.support
      · exact ⟨u,hx,v,hv,e⟩
      · exact ih hv hz
  exact go q hx p.start_mem_support

omit [Fintype V] [DecidableRel G.Adj] in
private theorem walk_in_star {a b x : V} (p : G.Walk a b) (hx : x ∉ p.support)
    {y z : V} (hy : y ∉ p.support ∧ (y = x ∨ G.Adj x y))
    (hz : z ∉ p.support ∧ (z = x ∨ G.Adj x z)) :
    ∃ q : G.Walk y z, q.IsPath ∧ ∀ w ∈ q.support, w ∉ p.support := by
  by_cases e : y = z
  · subst z
    exact ⟨.nil,IsPath.nil,by simpa using hy.1⟩
  rcases hy.2 with rfl|hy'
  · rcases hz.2 with e'|hz'
    · exact (e e'.symm).elim
    · exact ⟨hz'.toWalk,IsPath.of_adj hz',by simp [hx,hz.1]⟩
  rcases hz.2 with rfl|hz'
  · exact ⟨hy'.symm.toWalk,IsPath.of_adj hy'.symm,by simp [hx,hy.1]⟩
  refine ⟨.cons hy'.symm hz'.toWalk, (IsPath.of_adj hz').cons ?_, ?_⟩
  · simp [hy'.ne.symm,e]
  · simp [hx,hy.1,hz.1]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extra_predecessor (I : Finset ℕ) (hI : I.Nonempty)
    (i : ℕ) (hi : i ∈ I) (none : ∀ j ∈ I, i+2 ≠ j ∧ j+2 ≠ i)
    (many : ∃ j ∈ I, j ≠ i) :
    ∃ j ∈ I, j ≠ I.min' hI ∧ ∀ k ∈ I, k+1 ≠ j-1 := by
  let m := I.min' hI
  have hm := I.min'_mem hI
  by_cases e : i = m
  · subst i
    obtain ⟨u,hu,hne⟩ := many
    let J := I.erase m
    have ne : J.Nonempty := ⟨u,Finset.mem_erase.mpr ⟨hne,hu⟩⟩
    let j := J.min' ne
    obtain ⟨hjm,hj⟩ := Finset.mem_erase.mp (J.min'_mem ne)
    refine ⟨j,hj,hjm,?_⟩
    intro k hk h
    by_cases ekm : k = m
    · have hbad := (none j hj).1
      omega
    · have hkj := J.min'_le k (Finset.mem_erase.mpr ⟨ekm,hk⟩)
      omega
  · refine ⟨i,hi,e,?_⟩
    intro k hk h
    have hbad := (none k hk).2
    omega

private theorem small_separator_count_pins (hc : G.Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y) :
    ∃ (A B : Finset V), x ∈ A ∧ a ∉ A ∧ a ∉ B ∧ Disjoint A B ∧
      (∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) ∧ B.card < (DistanceTwo G x).card ∧
      (∀ i ∈ Pins p x, (∃ j ∈ Pins p x, j ≠ i) →
          (∀ j ∈ Pins p x, i+2 ≠ j ∧ j+2 ≠ i) → B.card+2 ≤ (DistanceTwo G x).card) ∧
      (∀ z, z ∈ A ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z)) ∧
      (∀ z, z ∈ B ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z) := by
  classical
  let A := Finset.univ.filter fun z => z ∉ p.support ∧ (z = x ∨ G.Adj x z)
  let B := Finset.univ.filter fun z => z ∉ A ∧ ∃ w ∈ A, G.Adj w z
  have memA (z : V) : z ∈ A ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [A]
  have memB (z : V) : z ∈ B ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [B]
  have hxA : x ∈ A := (memA _).mpr ⟨hx,Or.inl rfl⟩
  have notA {z : V} (h : z ∈ p.support) : z ∉ A := fun hh => ((memA _).mp hh).1 h
  have aa : a ∉ A := notA p.start_mem_support
  have noBends (z : V) (hz : z ∈ B) : z ≠ a ∧ z ≠ b := by
    obtain ⟨_,w,hw,h⟩ := (memB _).mp hz
    have he := no_endpoints hp ((memA _).mp hw).1
    exact ⟨fun q => he.1 (q ▸ h),fun q => he.2 (q ▸ h)⟩
  have noBcon (i : ℕ) (hi : i < p.length) (h₀ : p.getVert i ∈ B) :
      p.getVert (i + 1) ∉ B := by
    intro h₁
    obtain ⟨_,u,hu,hu'⟩ := (memB _).mp h₀
    obtain ⟨_,v,hv,hv'⟩ := (memB _).mp h₁
    obtain ⟨q,hq,hs⟩ := walk_in_star p hx ((memA _).mp hu) ((memA _).mp hv)
    obtain ⟨r,hr,hl,_⟩ := splice_walk p hp.1 q hq hs i hi hu'.symm hv'
    have hle := hp.2 a b r hr
    omega
  let I := Pins p x
  let F := I.image p.getVert
  have data (i : ℕ) (hi : i ∈ I) : i < p.length ∧ G.Adj x (p.getVert i) :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have findI {z : V} (hz : z ∈ p.support) (had : G.Adj x z) : ∃ i ∈ I, p.getVert i = z := by
    obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hz
    have hi : i < p.length := by
      by_contra! h
      have e : i = p.length := by omega
      rw [e,getVert_length] at he
      exact (no_endpoints hp hx).2 (he.symm ▸ had)
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ had⟩,he⟩
  have FB : F ⊆ B := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact (memB _).mpr ⟨notA (p.getVert_mem_support i),x,hxA,(data i hi).2⟩
  obtain ⟨i,hi,_⟩ := findI hy hxy
  let hI : I.Nonempty := ⟨i,hi⟩
  let m := I.min' hI
  have hm := data m (I.min'_mem hI)
  have hmpos : 0 < m := by
    by_contra h
    have e : m = 0 := Nat.eq_zero_of_not_pos h
    exact (no_endpoints hp hx).1 (by simpa [e] using hm.2)
  have memF (j : ℕ) (hj : j ∈ I) : p.getVert j ∈ F := Finset.mem_image.mpr ⟨j,hj,rfl⟩
  have hne (j : ℕ) : x ≠ p.getVert j := fun h => hx (h ▸ p.getVert_mem_support j)
  let S := I.image fun j => p.getVert (j+1)
  let t := p.getVert (m-1)
  have step (j : ℕ) (hj : j ∈ I) : p.getVert (j+1) ∉ B :=
    noBcon j (data j hj).1 (FB (memF j hj))
  have step2 (j : ℕ) (hj : j ∈ I) : p.getVert (j+1) ∈ DistanceTwo G x := by
    have hna : ¬G.Adj x (p.getVert (j+1)) := fun h => step j hj
      ((memB _).mpr ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
    exact mem_distanceTwo.mpr (dist_two hc (hne _) hna (data j hj).2 (p.adj_getVert_succ (data j hj).1))
  have hmshift : m-1+1 = m := by omega
  have tB : t ∉ B := by
    intro ht
    have bad := noBcon (m-1) (by omega) ht
    rw [hmshift] at bad
    exact bad (FB (memF m (I.min'_mem hI)))
  have tD : t ∈ DistanceTwo G x := by
    have hna : ¬G.Adj x t := fun h => tB ((memB _).mpr
      ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
    have h := p.adj_getVert_succ (i:=m-1) (by omega)
    rw [hmshift] at h
    exact mem_distanceTwo.mpr (dist_two hc (hne _) hna hm.2 h.symm)
  have tS : t ∉ S := by
    intro ht
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ht
    have hj' := (data j hj).1
    have hmj : m ≤ j := I.min'_le j hj
    have e := hp.1.getVert_injOn (show j+1 ≤ p.length by omega)
      (show m-1 ≤ p.length by omega) he
    omega
  have sc : S.card = I.card := by
    apply Finset.card_image_iff.mpr
    intro j hj k hk heq
    have hj' := (data j hj).1
    have hk' := (data k hk).1
    have e := hp.1.getVert_injOn (show j+1 ≤ p.length by omega)
      (show k+1 ≤ p.length by omega) heq
    omega
  have hbsub : B \ F ⊆ DistanceTwo G x := by
    intro z hz
    obtain ⟨hb,hf⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨out,w,hw,haw⟩ := (memB _).mp hb
    have hne' : x ≠ z := fun h => out (h ▸ hxA)
    have noadj : ¬G.Adj x z := by
      intro h
      by_cases hs : z ∈ p.support
      · obtain ⟨j,hj,rfl⟩ := findI hs h
        exact hf (memF j hj)
      · exact out ((memA _).mpr ⟨hs,Or.inr h⟩)
    rcases ((memA _).mp hw).2 with rfl|hw'
    · exact (noadj haw).elim
    · exact mem_distanceTwo.mpr (dist_two hc hne' noadj hw' haw)
  have hSsub : insert t S ⊆ DistanceTwo G x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact tD
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact step2 j hj
  have hd : Disjoint (insert t S) (B \ F) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hb := (Finset.mem_sdiff.mp hz').1
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact tB hb
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact step j hj hb
  have cnt := Finset.card_le_card (Finset.union_subset hSsub hbsub)
  rw [Finset.card_union_of_disjoint hd,Finset.card_insert_of_not_mem tS,sc] at cnt
  have fc : F.card ≤ I.card := Finset.card_image_le
  have bc := Finset.card_sdiff_add_card_eq_card FB
  have hbcount : B.card < (DistanceTwo G x).card := by omega
  refine ⟨A,B,hxA,aa,fun h => (noBends a h).1 rfl,?_,?_,hbcount,?_,memA,memB⟩
  · exact Finset.disjoint_left.mpr (fun z ha hz => ((memB _).mp hz).1 ha)
  · exact fun y hy z hz e => (memB _).mpr ⟨hz,y,hy,e⟩
  · intro i hi many none
    have pos (j : ℕ) (hj : j ∈ I) : 0 < j := by
      by_contra h
      have e : j = 0 := Nat.eq_zero_of_not_pos h
      exact (no_endpoints hp hx).1 (by simpa [e] using (data j hj).2)
    obtain ⟨j,hj,hjm,noj⟩ := extra_predecessor I hI i hi none many
    have hpos := pos j hj
    let u := p.getVert (j-1)
    have ju : j-1+1=j := by omega
    have hlu := (data j hj).1
    have hbu : u ∉ B := by
      intro h
      have hn := noBcon (j-1) (by omega) h
      rw [ju] at hn
      exact hn (FB (memF j hj))
    have hdu : u ∈ DistanceTwo G x := by
      have hna : ¬G.Adj x u := fun h => hbu ((memB _).mpr
        ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
      have h := p.adj_getVert_succ (i:=j-1) (by omega)
      rw [ju] at h
      exact mem_distanceTwo.mpr (dist_two hc (hne _) hna (data j hj).2 h.symm)
    have hu : u ∉ (insert t S) ∪ (B \ F) := by
      intro h
      rcases Finset.mem_union.mp h with h|h
      · rcases Finset.mem_insert.mp h with h|h
        · have e := hp.1.getVert_injOn (show j-1 ≤ p.length by omega)
            (show m-1 ≤ p.length by omega) h
          exact hjm (by omega)
        · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp h
          have hk' := (data k hk).1
          exact noj k hk (hp.1.getVert_injOn (show k+1 ≤ p.length by omega)
            (show j-1 ≤ p.length by omega) he)
      · exact hbu (Finset.mem_sdiff.mp h).1
    have big := Finset.card_le_card (Finset.insert_subset hdu (Finset.union_subset hSsub hbsub))
    rw [Finset.card_insert_of_not_mem hu,Finset.card_union_of_disjoint hd,
      Finset.card_insert_of_not_mem tS,sc] at big
    omega
set_option maxHeartbeats 1500000 in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem splice_gap_two {x y a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (hd : ∀ w ∈ q.support, w ∉ p.support) (i : ℕ) (hi : i+1 < p.length)
    (h₀ : G.Adj (p.getVert i) x) (h₁ : G.Adj y (p.getVert (i + 2))) :
    ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length + q.length ∧
      ∀ w : V, w ∈ r.support ↔ w ∈ q.support ∨ (w ∈ p.support ∧ w ≠ p.getVert (i+1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons a u b hau p ih =>
    cases i with
    | zero =>
      cases p with
      | nil => simp at hi
      | @cons u v b huv p =>
        have hax : G.Adj a x := h₀
        have hyv : G.Adj y v := by simpa using h₁
        have ha : a ∉ (cons huv p).support := (cons_isPath_iff _ _).1 hp |>.2
        have hu : u ∉ p.support := (cons_isPath_iff _ _).1 hp.of_cons |>.2
        have hqapp : (q.append (.cons hyv p)).IsPath := by
          rw [isPath_def, support_append, List.nodup_append]
          refine ⟨hq.support_nodup, ?_, ?_⟩
          · simpa only [support_cons, List.tail_cons] using hp.of_cons.of_cons.support_nodup
          · intro t ht ht'
            have hx' : t ∈ p.support := by simpa only [support_cons, List.tail_cons] using ht'
            exact hd t ht (by simp [hx'])
        refine ⟨.cons hax _, hqapp.cons ?_, by simp; omega, ?_⟩
        · rw [mem_support_append_iff]
          intro hh
          rcases hh with hh | hh
          · exact hd a hh (by simp)
          · simp only [support_cons, List.mem_cons] at hh
            exact hh.elim (fun e => hd a (e.symm ▸ q.end_mem_support) (by simp))
              (fun h => ha (by simp [h]))
        · intro w
          change w ∈ (cons hax _).support ↔ w ∈ q.support ∨
            (w ∈ (cons hau (cons huv p)).support ∧ w ≠ u)
          simp only [support_cons,List.mem_cons,mem_support_append_iff]
          have e : w = y → w ∈ q.support := fun h => h.symm ▸ q.end_mem_support
          have f : w = a → w ≠ u := fun h => h.symm ▸ hau.ne
          have k : w ∈ p.support → w ≠ u := fun h e => hu (e ▸ h)
          constructor
          · rintro (ha' | h | h | h)
            · exact Or.inr ⟨Or.inl ha', f ha'⟩
            · exact Or.inl h
            · exact Or.inl (e h)
            · exact Or.inr ⟨Or.inr (Or.inr h),k h⟩
          · rintro (h | ⟨(h | h | h),hn⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact (hn h).elim
            · exact Or.inr (Or.inr (Or.inr h))
    | succ i =>
      have hi' : i+1 < p.length := by simp at hi; omega
      obtain ⟨r,hr,hlen,hsup⟩ := ih hp.of_cons
        (fun t ht hs => hd t ht (by simp [hs])) i hi' h₀ h₁
      refine ⟨.cons hau r,hr.cons ?_,by simp [hlen]; omega,?_⟩
      · rw [hsup]
        intro h
        exact h.elim (fun e => hd a e (by simp))
          (fun e => ((cons_isPath_iff _ _).1 hp |>.2) e.1)
      · intro w
        change w ∈ (cons hau r).support ↔
          w ∈ q.support ∨ (w ∈ (cons hau p).support ∧ w ≠ p.getVert (i+1))
        simp only [support_cons,List.mem_cons,hsup]
        have e : w = a → w ≠ p.getVert (i+1) := by
          intro h h'
          have ht := p.getVert_mem_support (i+1)
          rw [←h',h] at ht
          exact (cons_isPath_iff _ _).1 hp |>.2 ht
        constructor
        · rintro (h | h | ⟨h,h'⟩)
          · exact Or.inr ⟨Or.inl h,e h⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h,h'⟩
        · rintro (h | ⟨(h | h),h'⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,h'⟩)


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem boundary_card_of_connectivity (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x a : V} {A B : Finset V} (hxa : x ∈ A) (haa : a ∉ A) (hab : a ∉ B)
    (hdis : Disjoint A B) (hbound : ∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) :
    k ≤ B.card := by
  by_contra! hsmall
  let W : Set V := (↑B : Set V)ᶜ
  let u : W := ⟨x,fun hb => Finset.disjoint_left.mp hdis hxa hb⟩
  let v : W := ⟨a,hab⟩
  have walk_closed {s t : W} (q : (G.induce W).Walk s t) (hs : (s : V) ∈ A) : (t : V) ∈ A := by
    induction q with
    | nil => exact hs
    | @cons a' b' c' e q ih =>
      apply ih
      by_contra h
      exact b'.prop (hbound a' hs b' h e)
  obtain ⟨q⟩ := (conn B hsmall) u v
  exact haa (walk_closed q hxa)

omit [Fintype V] [DecidableEq V] in
private theorem pin_data {a b : V} {p : G.Walk a b} {x : V} {i : ℕ}
    (hi : i ∈ Pins p x) : i < p.length ∧ G.Adj x (p.getVert i) :=
  ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

private theorem one_pin_or_no_omitted_neighbor (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p x) (hne : i ≠ j) :
    (∀ q ∈ Pins p x, ∃ r ∈ Pins p x, q+2=r ∨ r+2=q) ∧
    (∀ z, G.Adj x z → z ∈ p.support) := by
  classical
  obtain ⟨A,B,hxa,haa,hab,hdis,hbound,hcard,hgap,ha,hb⟩ :=
    small_separator_count_pins hc hp hx (p.getVert_mem_support i) (pin_data hi).2
  have lowB := boundary_card_of_connectivity k conn hxa haa hab hdis hbound
  have cap := bound x
  have eqB : B.card = k := by omega
  have partner (q : ℕ) (hq : q ∈ Pins p x) : ∃ r ∈ Pins p x, q+2=r ∨ r+2=q := by
    by_contra! hn
    have many : ∃ r ∈ Pins p x, r ≠ q := by
      by_cases he : i = q
      · exact ⟨j,hj,fun e => hne (he.trans e.symm)⟩
      · exact ⟨i,hi,he⟩
    have bad := hgap q hq many hn
    omega
  refine ⟨partner,?_⟩
  intro z hz
  by_contra hnot
  let A' := A.erase x
  let F := (Pins p x).image p.getVert
  let B' := insert x (B \ F)
  have zA' : z ∈ A' := Finset.mem_erase.mpr ⟨hz.ne.symm,(ha _).mpr ⟨hnot,Or.inr hz⟩⟩
  have naB' : a ∉ B' := by
    intro h
    rcases Finset.mem_insert.mp h with h|h
    · exact hx (h ▸ p.start_mem_support)
    · exact hab (Finset.mem_sdiff.mp h).1
  have naA' : a ∉ A' := fun h => haa (Finset.mem_erase.mp h).2
  have dis' : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro u hu hv
    obtain ⟨ex,au⟩ := Finset.mem_erase.mp hu
    rcases Finset.mem_insert.mp hv with hv|hv
    · exact ex hv
    · exact Finset.disjoint_left.mp hdis au (Finset.mem_sdiff.mp hv).1
  have exclusive (q : ℕ) (hq : q ∈ Pins p x) {u : V} (hu : u ∈ A') :
      ¬G.Adj u (p.getVert q) := by
    intro huq
    obtain ⟨nx,ua⟩ := Finset.mem_erase.mp hu
    have udata := (ha _).mp ua
    have xu : G.Adj x u := udata.2.resolve_left nx
    have both {s t : V} (h : G.Adj s t) (hs : s ∉ p.support) (ht : t ∉ p.support) :
        ∀ w ∈ h.toWalk.support, w ∉ p.support := by simp [hs,ht]
    obtain ⟨r,hr,he|he⟩ := partner q hq
    · have hrlen := (pin_data hr).1
      have lead := splice_gap_two p hp.1 xu.symm.toWalk (IsPath.of_adj xu.symm)
        (both xu.symm udata.1 hx) q (by omega) huq.symm (by simpa only [he] using (pin_data hr).2)
      obtain ⟨t,ht,htl,_⟩ := lead
      have l := hp.2 a b t ht
      simp at htl
      omega
    · have hqlen := (pin_data hq).1
      have lead := splice_gap_two p hp.1 xu.toWalk (IsPath.of_adj xu)
        (both xu hx udata.1) r (by omega) (pin_data hr).2.symm (by simpa only [he] using huq)
      obtain ⟨t,ht,htl,_⟩ := lead
      have l := hp.2 a b t ht
      simp at htl
      omega
  have border : ∀ y ∈ A', ∀ t ∉ A', G.Adj y t → t ∈ B' := by
    intro u hu v hv e
    by_cases he : v = x
    · exact Finset.mem_insert.mpr (Or.inl he)
    have vna : v ∉ A := fun ht => hv (Finset.mem_erase.mpr ⟨he,ht⟩)
    have vb : v ∈ B := hbound u (Finset.mem_erase.mp hu).2 v vna e
    have vnf : v ∉ F := by
      intro hvf
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hvf
      exact exclusive t ht hu e
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨vb,vnf⟩))
  have fsub : F ⊆ B := by
    intro u hu
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
    have out : p.getVert l ∉ A := fun h => ((ha _).mp h).1 (p.getVert_mem_support l)
    exact hbound x hxa _ out (pin_data hl).2
  have fbig : 2 ≤ F.card := by
    have en : p.getVert i ≠ p.getVert j := fun h =>
      hne (hp.1.getVert_injOn (Nat.le_of_lt (pin_data hi).1) (Nat.le_of_lt (pin_data hj).1) h)
    have sub : ({p.getVert i, p.getVert j} : Finset V) ⊆ F := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
      · rw [Finset.mem_singleton] at hu
        subst u
        exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
    have cc := Finset.card_le_card sub
    simp [en] at cc
    exact cc
  have xx : x ∉ B \ F := by
    intro h
    exact Finset.disjoint_left.mp hdis hxa (Finset.mem_sdiff.mp h).1
  have upper : B'.card < k := by
    have eq := Finset.card_sdiff_add_card_eq_card fsub
    rw [Finset.card_insert_of_not_mem xx]
    omega
  have lower := boundary_card_of_connectivity k conn zA' naA' naB' dis' border
  omega

#print axioms one_pin_or_no_omitted_neighbor

omit [Fintype V] [DecidableEq V] in
private theorem pin_of_neighbor_mem {a b x y : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) (hy : y ∈ p.support) (e : G.Adj x y) :
    ∃ i ∈ Pins p x, p.getVert i = y := by
  obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hy
  have hi : i < p.length := by
    by_contra! h
    have ee : i = p.length := by omega
    rw [ee,getVert_length] at he
    exact (no_endpoints hp hx).2 (he.symm ▸ e)
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ e⟩,he⟩

/-- At connectivity `d−1`, every vertex off a longest path has at most one
neighbor on it, provided that at most one vertex has degree below `d`. -/
theorem unique_omitted_pin_at_near_connectivity_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    ∀ i ∈ Pins p x, ∀ j ∈ Pins p x, i = j := by
  classical
  intro i hi j hj
  by_contra ne
  obtain ⟨partner,closed⟩ :=
    one_pin_or_no_omitted_neighbor hc k bound conn hp hx hi hj ne
  obtain ⟨r,hr,he⟩ := partner i hi
  obtain ⟨m,hm,hm2⟩ : ∃ m, m ∈ Pins p x ∧ (m+2) ∈ Pins p x := by
    rcases he with h|h
    · exact ⟨i,hi,h.symm ▸ hr⟩
    · exact ⟨r,hr,h.symm ▸ hi⟩
  have ml := (pin_data hm2).1
  let z := p.getVert (m+1)
  have xz : x ≠ z := fun e => hx (e ▸ p.getVert_mem_support (m+1))
  have hq : ∀ w ∈ (Walk.nil : G.Walk x x).support, w ∉ p.support := by simpa using hx
  obtain ⟨q,hqpath,hqlen,hqsup⟩ := splice_gap_two p hp.1 (Walk.nil : G.Walk x x) IsPath.nil
    hq m (by omega) (pin_data hm).2.symm (pin_data hm2).2
  have len : q.length = p.length := by simpa using hqlen
  have hqmax : IsLongest q := ⟨hqpath,fun u v s hs => len.symm ▸ hp.2 u v s hs⟩
  have znot : z ∉ q.support := by
    intro hz
    rcases (hqsup z).mp hz with h|h
    · exact xz.symm (by simpa using h)
    · exact h.2 rfl
  have hm1le : m+1 ≤ p.length := by omega
  have qmem (t : ℕ) (ht : t ≤ p.length) (hne : t ≠ m+1) : p.getVert t ∈ q.support :=
    (hqsup _).mpr (Or.inr ⟨p.getVert_mem_support t,fun e =>
      hne (hp.1.getVert_injOn ht hm1le e)⟩)
  have hmz := p.adj_getVert_succ (i:=m) (by omega : m < p.length)
  have hzm := p.adj_getVert_succ (i:=m+1) (by omega : m+1 < p.length)
  obtain ⟨u,hu,huv⟩ := pin_of_neighbor_mem hqmax znot (qmem m (by omega) (by omega)) hmz.symm
  obtain ⟨v,hv,hvv⟩ := pin_of_neighbor_mem hqmax znot (qmem (m+2) (by omega) (by omega)) hzm
  have uv : u ≠ v := by
    intro e
    subst v
    have heq := huv.symm.trans hvv
    have bad := hp.1.getVert_injOn (show m ≤ p.length by omega) (show m+2 ≤ p.length by omega) heq
    omega
  have zclosed := (one_pin_or_no_omitted_neighbor hc k bound conn hqmax znot hu hv uv).2
  have capx := bound x
  have capz := bound z
  have smallx := degree_lt_distanceTwo_of_omitted_isolated hc hp hx closed ⟨_,(pin_data hm).2⟩
  have smallz := degree_lt_distanceTwo_of_omitted_isolated hc hqmax znot zclosed ⟨_,hmz.symm⟩
  rcases degree x z xz with h|h <;> omega

#print axioms unique_omitted_pin_at_near_connectivity_of_d2
private lemma mem_omittedStar {a b x z : V} {p : G.Walk a b} :
    z ∈ OmittedStar p x ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [OmittedStar]

private lemma mem_external {A : Finset V} {z : V} :
    z ∈ External G A ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [External]

theorem rigid_flanks_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) :
    DistanceTwo G x \ External G (OmittedStar p x) =
      {p.getVert (i-1), p.getVert (i+1)} := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let pin := p.getVert i
  let t := p.getVert (i-1)
  let u := p.getVert (i+1)
  have hxA : x ∈ A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have offA {z : V} (hm : z ∈ p.support) : z ∉ A := fun zz => (mem_omittedStar.mp zz).1 hm
  have offB {z : V} (endpt : z = a ∨ z = b) : z ∉ B := by
    intro h
    obtain ⟨_,w,hw,e⟩ := mem_external.mp h
    have hn := no_endpoints hp (mem_omittedStar.mp hw).1
    rcases endpt with rfl|rfl
    · exact hn.1 e
    · exact hn.2 e
  have hdis : Disjoint A B :=
    disjoint_left.mpr (fun _ ha hb => (mem_external.mp hb).1 ha)
  have hB := boundary_card_of_connectivity k conn hxA (offA p.start_mem_support)
    (offB (Or.inl rfl)) hdis (fun y hy z hz e => mem_external.mpr ⟨hz,y,hy,e⟩)
  have noncon (j : ℕ) (hj : j < p.length) (h₁ : p.getVert j ∈ B) : p.getVert (j+1) ∉ B := by
    intro h₂
    obtain ⟨_,y,hy,hya⟩ := mem_external.mp h₁
    obtain ⟨_,z,hz,hza⟩ := mem_external.mp h₂
    obtain ⟨q,hq,hqs⟩ := walk_in_star p hx (mem_omittedStar.mp hy) (mem_omittedStar.mp hz)
    obtain ⟨r,hr,hrlen,_⟩ := splice_walk p hp.1 q hq hqs j hj hya.symm hza
    have hle := hp.2 a b r hr
    omega
  have pind := pin_data hi
  have hip : 0 < i := by
    by_contra h
    have e : i = 0 := Nat.eq_zero_of_not_pos h
    exact (no_endpoints hp hx).1 (by simpa [e] using pind.2)
  have pB : pin ∈ B := mem_external.mpr ⟨offA (p.getVert_mem_support i),x,hxA,pind.2⟩
  have isub : i-1+1=i := by omega
  have tB : t ∉ B := by
    intro h
    have h' := noncon (i-1) (by omega) h
    rw [isub] at h'
    exact h' pB
  have uB : u ∉ B := noncon i pind.1 pB
  have tAdj : G.Adj t pin := by
    have h := p.adj_getVert_succ (i:=i-1) (by omega)
    rwa [isub] at h
  have uAdj : G.Adj pin u := p.adj_getVert_succ pind.1
  have td : t ∈ DistanceTwo G x := by
    apply mem_distanceTwo.mpr
    have hn : x ≠ t := fun e => hx (e ▸ p.getVert_mem_support (i-1))
    apply dist_two hc hn ?_ pind.2 tAdj.symm
    exact fun e => tB (mem_external.mpr ⟨offA (p.getVert_mem_support _),x,hxA,e⟩)
  have ud : u ∈ DistanceTwo G x := by
    apply mem_distanceTwo.mpr
    have hn : x ≠ u := fun e => hx (e ▸ p.getVert_mem_support (i+1))
    apply dist_two hc hn ?_ pind.2 uAdj
    exact fun e => uB (mem_external.mpr ⟨offA (p.getVert_mem_support _),x,hxA,e⟩)
  have tnu : t ≠ u := by
    intro e
    have h := hp.1.getVert_injOn (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) e
    omega
  have cutd : B.erase pin ⊆ DistanceTwo G x := by
    intro w hw
    obtain ⟨wnp,wb⟩ := mem_erase.mp hw
    obtain ⟨wna,z,hz,ez⟩ := mem_external.mp wb
    have wx : x ≠ w := fun e => wna (e ▸ hxA)
    have nxw : ¬G.Adj x w := by
      intro e
      by_cases h : w ∈ p.support
      · obtain ⟨j,hj,rv⟩ := pin_of_neighbor_mem hp hx h e
        have eq := unique_omitted_pin_at_near_connectivity_of_d2 hc k bound conn degree hp hx j hj i hi
        subst j
        exact wnp rv.symm
      · exact wna (mem_omittedStar.mpr ⟨h,Or.inr e⟩)
    rcases (mem_omittedStar.mp hz).2 with rfl|ez'
    · exact (nxw ez).elim
    · exact mem_distanceTwo.mpr (dist_two hc wx nxw ez' ez)
  change DistanceTwo G x \ B = {t,u}
  have inc : ({t,u} : Finset V) ⊆ DistanceTwo G x \ B := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact mem_sdiff.mpr ⟨td,tB⟩
    · rw [mem_singleton] at hz
      subst z
      exact mem_sdiff.mpr ⟨ud,uB⟩
  symm
  apply eq_of_subset_of_card_le inc
  have ds : Disjoint (DistanceTwo G x \ B) (B.erase pin) :=
    disjoint_left.mpr (fun _ m n => (mem_sdiff.mp m).2 (mem_erase.mp n).2)
  have ad : (DistanceTwo G x \ B) ∪ B.erase pin ⊆ DistanceTwo G x := by
    exact union_subset (fun _ h => (mem_sdiff.mp h).1) cutd
  have cap := bound x
  have cutlen := card_erase_add_one pB
  have upto := card_le_card ad
  rw [card_union_of_disjoint ds] at upto
  simp only [card_insert_of_not_mem (show t ∉ ({u} : Finset V) by simpa using tnu),card_singleton]
  omega

#print axioms rigid_flanks_of_d2

/-- Same-support reordering cannot change the unordered two flanks of a pin. -/
theorem same_support_rigid_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b c e : V} {p : G.Walk a b} {q : G.Walk c e} (hp : IsLongest p) (hq : IsLongest q)
    (same : ∀ z : V, z ∈ p.support ↔ z ∈ q.support)
    {x : V} (hx : x ∉ p.support) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins q x) :
    ({p.getVert (i-1),p.getVert (i+1)} : Finset V) = {q.getVert (j-1),q.getVert (j+1)} := by
  have star : OmittedStar p x = OmittedStar q x := by
    ext z
    rw [mem_omittedStar,mem_omittedStar,same z]
  have f := rigid_flanks_of_d2 hc k bound conn degree hp hx hi
  have g := rigid_flanks_of_d2 hc k bound conn degree hq (fun h => hx ((same _).mpr h)) hj
  rw [star] at f
  exact f.symm.trans g

theorem start_not_adj_pin_of_two_le_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) (h₂ : 2 ≤ i) :
    ¬G.Adj a (p.getVert i) := by
  intro h
  have hil := (pin_data hi).1
  have isub : i-1+1=i := by omega
  obtain ⟨q,hq,hs,hql,hqa,hqp⟩ := rotate_start hp (i-1) (by omega) (by simpa only [isub] using h)
  rw [isub] at hqp
  have hia : G.Adj x (q.getVert i) := by rw [hqp]; exact (pin_data hi).2
  have hj : i ∈ Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),hia⟩
  have hf := same_support_rigid_of_d2 hc k bound conn degree hp hq hs hx hi hj
  have ha : a ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V) := by
    rw [hf]
    have e := mem_insert_self (q.getVert (i-1)) ({q.getVert (i+1)} : Finset V)
    simpa only [hqa] using e
  have haa : p.getVert 0 = a := p.getVert_zero
  have clash (j : ℕ) (hj : j ≤ p.length) (pos : 0 < j) (e : p.getVert 0 = p.getVert j) : False := by
    have z := hp.1.getVert_injOn (show 0 ≤ p.length by omega) hj e
    omega
  rcases mem_insert.mp ha with h|h
  · exact clash (i-1) (by omega) (by omega) (haa.trans h)
  · exact clash (i+1) (by omega) (by omega) (haa.trans (mem_singleton.mp h))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem reverse_longest {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    IsLongest p.reverse := ⟨hp.1.reverse,fun u v q hq => by simpa using hp.2 u v q hq⟩

omit [Fintype V] [DecidableEq V] in
private lemma pin_pos {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : 0 < i := by
  by_contra h
  have e : i=0 := Nat.eq_zero_of_not_pos h
  exact (no_endpoints hp hx).1 (by simpa only [e,getVert_zero] using (pin_data hi).2)

omit [Fintype V] [DecidableEq V] in
private theorem pin_reverse {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : p.length-i ∈ Pins p.reverse x := by
  have h := (pin_data hi).1
  have hi' := pin_pos hp hx hi
  apply mem_filter.mpr
  constructor
  · rw [mem_range,length_reverse]
    omega
  · rw [getVert_reverse]
    have eq : p.length-(p.length-i)=i := by omega
    rw [eq]
    exact (pin_data hi).2

theorem end_not_adj_pin_of_two_le_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) (h₂ : i+2 ≤ p.length) :
    ¬G.Adj b (p.getVert i) := by
  have h := start_not_adj_pin_of_two_le_of_d2 hc k bound conn degree (reverse_longest hp)
    (by simpa using hx) (pin_reverse hp hx hi) (by omega)
  rw [getVert_reverse] at h
  have eq : p.length-(p.length-i)=i := by omega
  rwa [eq] at h

private def LeftMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj a (p.getVert (i+1))

private def RightMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj b (p.getVert i)

private theorem card_leftMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (LeftMarks p).card = G.degree a := by
  classical
  have eq : (LeftMarks p).image (fun i => p.getVert (i+1)) = G.neighborFinset a := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).1 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : 0<i := by
        by_contra h
        have he : i=0 := by omega
        rw [he,getVert_zero] at ei
        exact e.ne ei
      have iq : i-1+1=i := by omega
      exact ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [iq,ei]⟩,by rwa [iq]⟩
  have inj : ((LeftMarks p).image (fun i => p.getVert (i+1))).card = (LeftMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    have h := hp.1.getVert_injOn (show i+1≤p.length by omega) (show j+1≤p.length by omega) e
    omega
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

private theorem card_rightMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (RightMarks p).card = G.degree b := by
  classical
  have eq : (RightMarks p).image p.getVert = G.neighborFinset b := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).2 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : i < p.length := by
        by_contra h
        have he : i=p.length := by omega
        rw [he,getVert_length] at ei
        exact e.ne ei
      exact ⟨i,mem_filter.mpr ⟨mem_range.mpr ip,by rwa [ei]⟩,ei⟩
  have inj : ((RightMarks p).image p.getVert).card = (RightMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    exact hp.1.getVert_injOn il.le jl.le e
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

/-- There are two unused endpoint-indices for each separated pin, except
possibly the first and last index. -/
theorem endpoint_marks_bound_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (I : Finset ℕ) (non : I.Nonempty)
    (active : ∀ i ∈ I, ∃ x, x ∉ p.support ∧ i ∈ Pins p x)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i < j → i+2 ≤ j) :
    G.degree a + G.degree b + 2*I.card ≤ p.length+2 := by
  classical
  let L := LeftMarks p
  let R := RightMarks p
  have ip (i : ℕ) (hi : i ∈ I) : 0<i ∧ i<p.length := by
    obtain ⟨x,hx,h⟩ := active i hi
    exact ⟨pin_pos hp hx h,(pin_data h).1⟩
  let J := I.image (·-1)
  have JC : J.card = I.card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have := (ip i hi).1
    change i-1=j-1 at e
    have := (ip j hj).1
    omega
  have IJ : Disjoint I J := by
    rw [disjoint_left]
    intro i hi h
    obtain ⟨j,hj,e⟩ := mem_image.mp h
    have := (ip j hj).1
    change j-1=i at e
    have ds := sep i hi j hj (by omega)
    omega
  let U := I ∪ J
  let T := (U.erase 0).erase (p.length-1)
  have UC : U.card = 2*I.card := by
    rw [card_union_of_disjoint IJ,JC]
    omega
  have TC : U.card ≤ T.card+2 := by
    have h (S : Finset ℕ) (i : ℕ) : S.card ≤ (S.erase i).card+1 := by
      by_cases hi : i ∈ S
      · rw [card_erase_add_one hi]
      · rw [erase_eq_of_not_mem hi]
        omega
    have a₁ := h U 0
    have a₂ : (U.erase 0).card ≤ T.card+1 := h (U.erase 0) (p.length-1)
    omega
  have disLR : Disjoint L R := by
    rw [disjoint_left]
    intro i h₁ h₂
    obtain ⟨j,hj⟩ := non
    obtain ⟨x,hx,ha⟩ := active j hj
    have di := mem_filter.mp h₁
    exact not_adj_both_end_marks hp hx (p.getVert_mem_support j) (pin_data ha).2
      (mem_range.mp di.1) di.2 (mem_filter.mp h₂).2
  have Tdata (i : ℕ) (hi : i ∈ T) : i ≠ 0 ∧ i ≠ p.length-1 ∧ i ∈ U := by
    obtain ⟨last,h⟩ := mem_erase.mp hi
    obtain ⟨zero,hu⟩ := mem_erase.mp h
    exact ⟨zero,last,hu⟩
  have allowed (i : ℕ) (hi : i ∈ T) : i < p.length ∧ i ∉ L ∧ i ∉ R := by
    obtain ⟨n0,nlast,hu⟩ := Tdata i hi
    rcases mem_union.mp hu with hf|hf
    · obtain ⟨x,hx,ha⟩ := active i hf
      have il := (pin_data ha).1
      refine ⟨il,?_,?_⟩
      · exact fun h => start_not_adj_pin_successor hp hx ha (mem_filter.mp h).2
      · exact fun h => end_not_adj_pin_of_two_le_of_d2 hc k bound conn degree hp hx ha
          (by omega) (mem_filter.mp h).2
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hf
      obtain ⟨x,hx,ha⟩ := active j hj
      have jp := pin_pos hp hx ha
      have jl := (pin_data ha).1
      refine ⟨by omega,?_,?_⟩
      · intro h
        have e := (mem_filter.mp h).2
        have jj : j-1+1=j := by omega
        rw [jj] at e
        exact start_not_adj_pin_of_two_le_of_d2 hc k bound conn degree hp hx ha (by omega) e
      · exact fun h => end_not_adj_pin_predecessor hp hx ha (mem_filter.mp h).2
  have disT : Disjoint (L ∪ R) T := by
    rw [disjoint_left]
    intro x hu ht
    have wh := allowed x ht
    exact (mem_union.mp hu).elim wh.2.1 wh.2.2
  have big : (L ∪ R) ∪ T ⊆ range p.length := by
    intro i hi
    rcases mem_union.mp hi with h|h
    · rcases mem_union.mp h with h|h
      · exact (mem_filter.mp h).1
      · exact (mem_filter.mp h).1
    · exact mem_range.mpr (allowed i h).1
  have card := card_le_card big
  rw [card_union_of_disjoint disT,card_union_of_disjoint disLR,card_range,card_leftMarks hp,card_rightMarks hp] at card
  omega

#print axioms endpoint_marks_bound_of_d2

/-- An omitted component forces many punctures in the endpoint-index count. -/
theorem component_and_length_bound_of_d2 (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : Finset V) (nonH : H.Nonempty)
    (off : ∀ z ∈ H, z ∉ p.support)
    (closed : ∀ z ∈ H, ∀ w ∉ H, G.Adj z w → w ∈ p.support)
    (joined : ∀ x ∈ H, ∀ y ∈ H, ∃ q : G.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, z ∈ H) :
    k+1 ≤ H.card ∧ G.degree a + G.degree b + 2*k ≤ p.length+2 := by
  classical
  let I := (range p.length).filter fun i => ∃ x ∈ H, G.Adj x (p.getVert i)
  have idata (i : ℕ) (hi : i ∈ I) : ∃ x ∈ H, i ∈ Pins p x := by
    obtain ⟨il,x,hx,ha⟩ := mem_filter.mp hi
    exact ⟨x,hx,mem_filter.mpr ⟨il,ha⟩⟩
  let F := I.image p.getVert
  have covers : ∀ z ∈ H, ∀ w ∉ H, G.Adj z w → w ∈ F := by
    intro z hz w hw e
    obtain ⟨i,hi,e'⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz w hw e) e
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,z,hz,(pin_data hi).2⟩,e'⟩
  have hdis : Disjoint H F := by
    rw [disjoint_left]
    intro z hz hf
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hf
    exact off _ hz (p.getVert_mem_support i)
  have aH : a ∉ H := fun h => off a h p.start_mem_support
  have aF : a ∉ F := by
    intro h
    obtain ⟨i,hi,e⟩ := mem_image.mp h
    obtain ⟨z,hz,hi'⟩ := idata i hi
    have en : G.Adj z a := by rw [←e]; exact (pin_data hi').2
    exact (no_endpoints hp (off z hz)).1 en
  obtain ⟨t,ht⟩ := nonH
  have fcard := boundary_card_of_connectivity k conn ht aH aF hdis covers
  have fsmall : F.card ≤ I.card := card_image_le
  have icard : k ≤ I.card := le_trans fcard fsmall
  have iH : I.card ≤ H.card := by
    let f (i : I) : H := ⟨Classical.choose (idata i i.prop),(Classical.choose_spec (idata i i.prop)).1⟩
    have hf (i : I) : (i : ℕ) ∈ Pins p (f i : V) :=
      (Classical.choose_spec (idata i i.prop)).2
    have inj : Function.Injective f := by
      intro i j e
      have e' : (f i : V) = (f j : V) := congrArg Subtype.val e
      have m : (j : ℕ) ∈ Pins p (f i : V) := e'.symm ▸ hf j
      exact Subtype.ext (unique_omitted_pin_at_near_connectivity_of_d2 hc k bound conn degree hp
        (off (f i) (f i).prop) i (hf i) j m)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
  have hmore : k+1 ≤ H.card := by
    by_contra! hsmall
    have many : 1 < H.card := by omega
    obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp many
    have each (z : V) (hz : z ∈ H) : G.degree z ≤ H.card := by
      let O := (G.neighborFinset z).filter fun w => w ∉ H
      have OS : O.card ≤ 1 := by
        apply card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha₀,ha₁⟩ := mem_filter.mp ha
        obtain ⟨hb₀,hb₁⟩ := mem_filter.mp hb
        have e₁ := (G.mem_neighborFinset _ _).mp ha₀
        have e₂ := (G.mem_neighborFinset _ _).mp hb₀
        obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz a ha₁ e₁) e₁
        obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz b hb₁ e₂) e₂
        have eq := unique_omitted_pin_at_near_connectivity_of_d2 hc k bound conn degree hp (off z hz) i hi j hj
        subst j
        exact ei.symm.trans ej
      have N : G.neighborFinset z ⊆ H.erase z ∪ O := by
        intro w hw
        by_cases wh : w ∈ H
        · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hw).ne.symm,wh⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hw,wh⟩))
      have c := card_le_card N
      have c' := card_union_le (H.erase z) O
      rw [G.card_neighborFinset_eq_degree] at c
      have hh := card_erase_add_one hz
      omega
    have du := each u hu
    have dv := each v hv
    rcases degree u v uv with h|h <;> omega
  have non : I.Nonempty := card_pos.mp (by omega)
  have active (i : ℕ) (hi : i ∈ I) : ∃ x, x ∉ p.support ∧ i ∈ Pins p x := by
    obtain ⟨x,hx,hd⟩ := idata i hi
    exact ⟨x,off x hx,hd⟩
  have sep (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) (lt : i<j) : i+2 ≤ j := by
    obtain ⟨x,hx,hd⟩ := idata i hi
    obtain ⟨y,hy,he⟩ := idata j hj
    have dxy : x ≠ y := by
      intro e
      subst y
      exact (Nat.ne_of_lt lt)
        (unique_omitted_pin_at_near_connectivity_of_d2 hc k bound conn degree hp (off x hx) i hd j he)
    obtain ⟨q,hq,hqs⟩ := joined x hx y hy
    have qpos : 0<q.length := by
      cases q with
      | nil => contradiction
      | cons edge q => simp
    have g := gap_three_of_linked_pins hp hd he lt q hq qpos
      (fun z hz => off z (hqs z hz))
    omega
  have c := endpoint_marks_bound_of_d2 hc k bound conn degree hp I non active sep
  exact ⟨hmore,by omega⟩

#print axioms component_and_length_bound_of_d2

omit [DecidableRel G.Adj] in
private theorem path_d2_mem (hc : G.Connected) {a b u v w : V}
    {p : G.Walk a b} (hw : w ∈ p.support) (hne : u ≠ w)
    (hn : ¬ G.Adj u w) (uv : G.Adj u v) (vw : G.Adj v w) :
    w ∈ (DistanceTwo G u).filter (· ∈ p.support) := by
  have lower := hc.one_lt_dist_of_ne_of_not_adj hne hn
  have upper := G.dist_le (Walk.cons uv (Walk.cons vw .nil))
  simp only [length_cons,length_nil] at upper
  have eq : G.dist u w = 2 := by omega
  classical
  simp [DistanceTwo,hw,eq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem endpoint_neighbors_on_path {a b z : V} {p : G.Walk a b} (hp : IsLongest p)
    (hz : G.Adj a z ∨ G.Adj b z) : z ∈ p.support := by
  by_contra hm
  rcases hz with e|e
  · have m := hp.2 z b (.cons e.symm p) (hp.1.cons hm)
    simp at m
  · have path : (Walk.cons e.symm p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hm)).reverse
    have m := hp.2 a z _ path
    simp at m

private theorem atLeastTwo_from_endpoint (hc : G.Connected)
    {a b v e : V} {p : G.Walk a b} (hp : IsLongest p) (he : e = a ∨ e = b)
    (degree : 3 ≤ G.degree e) (adj : G.Adj e v)
    (no : ∀ z, G.Adj e z → z ≠ v → ¬G.Adj v z) :
    2 ≤ ((DistanceTwo G v).filter (· ∈ p.support)).card := by
  let S := (G.neighborFinset e).erase v
  have hv : v ∈ G.neighborFinset e := (G.mem_neighborFinset _ _).mpr adj
  have ns : 2 ≤ S.card := by
    rw [show S.card = (G.neighborFinset e).card-1 from card_erase_of_mem hv,
      card_neighborFinset_eq_degree]
    omega
  apply ns.trans (Finset.card_le_card ?_)
  intro z hz
  obtain ⟨hn,hm⟩ := mem_erase.mp hz
  have ez := (G.mem_neighborFinset _ _).mp hm
  have zpath := endpoint_neighbors_on_path hp (he.elim (fun h => Or.inl (h ▸ ez))
    (fun h => Or.inr (h ▸ ez)))
  exact path_d2_mem hc zpath (Ne.symm hn) (no z ez hn) adj.symm ez

/-- When no path neighbor of a pin is available beyond the two flanks and
well-separated additional pins, there are at least two path vertices at
distance two from this pin, even if a flank is a path endpoint. -/
theorem pin_has_two_on_path_general_of_d2 (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (ha : 3 ≤ G.degree a) (hb : 3 ≤ G.degree b)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x)
    (hN : ∀ j ≤ p.length, G.Adj (p.getVert i) (p.getVert j) →
      j=i-1 ∨ j=i+1 ∨ ∃ y ∉ p.support, j∈Pins p y ∧ (i+3≤j ∨ j+3≤i)) :
    2 ≤ ((DistanceTwo G (p.getVert i)).filter (· ∈ p.support)).card := by
  have hil : i < p.length := mem_range.mp (mem_filter.mp hi).1
  have hip : 0 < i := by
    by_contra! h
    have eq : i=0 := by omega
    have e : G.Adj x (p.getVert i) := (mem_filter.mp hi).2
    rw [eq,getVert_zero] at e
    exact hx (endpoint_neighbors_on_path hp (Or.inl e.symm))
  by_cases left : i = 1
  · have ei : G.Adj a (p.getVert i) := by
      have e := p.adj_getVert_succ (i:=0) (by omega)
      rw [getVert_zero] at e
      rwa [left]
    apply atLeastTwo_from_endpoint hc hp (Or.inl rfl) ha ei
    intro z ez nez ep
    have zpath := endpoint_neighbors_on_path hp (Or.inl ez)
    obtain ⟨j,ej,hj⟩ := mem_support_iff_exists_getVert.mp zpath
    rcases hN j hj (ej.symm ▸ ep) with eq|eq|⟨y,hy,yp,hgap⟩
    · have j0 : j=0 := by omega
      rw [j0,getVert_zero] at ej
      exact ez.ne ej
    · exact start_not_adj_pin_successor hp hx hi (by rwa [← eq,ej])
    · exact start_not_adj_pin_of_two_le_of_d2 hc k bound conn degree hp hy yp (by omega) (by rwa [ej])
  by_cases right : i+1 = p.length
  · have ei : G.Adj b (p.getVert i) := by
      have e := p.adj_getVert_succ (i:=i) hil
      rw [right,getVert_length] at e
      exact e.symm
    apply atLeastTwo_from_endpoint hc hp (Or.inr rfl) hb ei
    intro z ez nez ep
    have zpath := endpoint_neighbors_on_path hp (Or.inr ez)
    obtain ⟨j,ej,hj⟩ := mem_support_iff_exists_getVert.mp zpath
    rcases hN j hj (ej.symm ▸ ep) with eq|eq|⟨y,hy,yp,hgap⟩
    · exact end_not_adj_pin_predecessor hp hx hi (by rwa [← eq,ej])
    · rw [eq,right,getVert_length] at ej
      exact ez.ne ej
    · exact end_not_adj_pin_of_two_le_of_d2 hc k bound conn degree hp hy yp (by omega) (by rwa [ej])
  have ineq : 2 ≤ i := by omega
  have istep : i+2 ≤ p.length := by omega
  have e₀ (j : ℕ) (hj : j ≤ p.length) (hne : i ≠ j) : p.getVert i ≠ p.getVert j :=
    fun h => hne (hp.1.getVert_injOn hil.le hj h)
  have hnot₁ : ¬ G.Adj (p.getVert i) (p.getVert (i-2)) := by
    intro e
    rcases hN (i-2) (by omega) e with h|h|⟨_,_,_,h⟩ <;> omega
  have hnot₂ : ¬ G.Adj (p.getVert i) (p.getVert (i+2)) := by
    intro e
    rcases hN (i+2) istep e with h|h|⟨_,_,_,h⟩ <;> omega
  have eprev : G.Adj (p.getVert (i-1)) (p.getVert i) := by
    have e := p.adj_getVert_succ (i:=i-1) (by omega)
    have eq : i-1+1=i := by omega
    rwa [eq] at e
  have eprev₂ : G.Adj (p.getVert (i-2)) (p.getVert (i-1)) := by
    have e := p.adj_getVert_succ (i:=i-2) (by omega)
    have eq : i-2+1=i-1 := by omega
    rwa [eq] at e
  have D₁ := path_d2_mem hc (p.getVert_mem_support (i-2))
    (e₀ (i-2) (by omega) (by omega)) hnot₁ eprev.symm eprev₂.symm
  have D₂ := path_d2_mem hc (p.getVert_mem_support (i+2))
    (e₀ (i+2) istep (by omega)) hnot₂
    (p.adj_getVert_succ hil) (p.adj_getVert_succ (by omega : i+1 < p.length))
  have distinct : p.getVert (i-2) ≠ p.getVert (i+2) := by
    intro h
    have he := hp.1.getVert_injOn (by omega : i-2≤p.length) istep h
    omega
  have sub : {p.getVert (i-2),p.getVert (i+2)} ⊆
      (DistanceTwo G (p.getVert i)).filter (· ∈ p.support) := by
    simp [insert_subset,D₁,D₂]
  have cnt := Finset.card_le_card sub
  simpa [distinct] using cnt

#print axioms pin_has_two_on_path_general_of_d2

end Graffiti189LongestPath.DistanceOnly
