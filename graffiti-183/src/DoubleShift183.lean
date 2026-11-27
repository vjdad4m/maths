import Cyclic183

namespace Graffiti183.Exceptional
open SimpleGraph Finset

set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {m : ℕ}

/-- No connected dominating set with fewer than m−2 vertices. -/
def NoSmallCore (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ D : Finset V, Graffiti177.Con G D →
    (∀ x ∉ D, Graffiti177.Dominates G D x) → m-2 ≤ D.card

def contacts (G : SimpleGraph V) [DecidableRel G.Adj] (f : Fin m ↪ V) (z : V) :
    Finset (Fin m) := univ.filter (fun i => G.Adj z (f i))

@[simp] lemma mem_contacts {f : Fin m ↪ V} {z : V} {i : Fin m} :
    i ∈ contacts G f z ↔ G.Adj z (f i) := by simp [contacts]

lemma contacts_rotate_card (f : Fin m ↪ V) (a : Fin m) (z : V) :
    (contacts G ((rotEmb a).trans f) z).card = (contacts G f z).card := by
  have he : (contacts G ((rotEmb a).trans f) z).map (rotEmb a) = contacts G f z := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,hji⟩ := mem_map.mp hi
      subst i
      exact mem_contacts.mpr ((mem_contacts (f := (rotEmb a).trans f)).mp hj)
    · intro hi
      obtain ⟨j,hj⟩ := rot_surjective a i
      refine mem_map.mpr ⟨j,mem_contacts.mpr ?_,hj⟩
      change G.Adj z (f (rot a j))
      rw [hj]
      exact mem_contacts.mp hi
  exact (Finset.card_map (f := rotEmb a)).symm.trans (congrArg Finset.card he)

structure ContactConditions (G : SimpleGraph V) [DecidableRel G.Adj] (f : Fin m ↪ V) : Prop where
  big : ∀ z ∉ indexSet f, 3 ≤ (contacts G f z).card
  no_isolated : ∀ z ∉ indexSet f, ∀ i ∈ contacts G f z,
    ∃ j ∈ contacts G f z, CycleAdj i j

lemma contact_conditions_rotate (hm : 2 ≤ m) (f : Fin m ↪ V)
    (h : ContactConditions G f) (a : Fin m) :
    ContactConditions G ((rotEmb a).trans f) := by
  constructor
  · intro z hz
    rw [contacts_rotate_card]
    rw [indexSet_rot f a] at hz
    exact h.big z hz
  · intro z hz i hi
    have hz' : z ∉ indexSet f := by simpa only [indexSet_rot] using hz
    have hi' : rot a i ∈ contacts G f z := mem_contacts.mpr ((mem_contacts (f := (rotEmb a).trans f)).mp hi)
    obtain ⟨j,hj,he⟩ := h.no_isolated z hz' _ hi'
    obtain ⟨k,hk⟩ := rot_surjective a j
    refine ⟨k,mem_contacts.mpr ?_,(cycleAdj_rotate hm a i k).mp (hk.symm ▸ he)⟩
    change G.Adj z (f (rot a k))
    rw [hk]
    exact mem_contacts.mp hj

/-- Extend interval reachability to either order of the two endpoints. -/
lemma interval_any (f : Fin m ↪ V)
    (hstep : ∀ i j, i.val+1=j.val → G.Adj (f i) (f j))
    {D : Finset V} {a b : Fin m} {ha : f a ∈ D} {hb : f b ∈ D}
    (hmem : ∀ i, min a.val b.val ≤ i.val → i.val ≤ max a.val b.val → f i ∈ D) :
    (G.induce (D : Set V)).Reachable ⟨f a,ha⟩ ⟨f b,hb⟩ := by
  rcases le_total a.val b.val with hab | hba
  · exact interval_reach f hstep hab (by simpa [min_eq_left hab,max_eq_right hab] using hmem)
  · exact (interval_reach f hstep hba (by simpa [min_eq_right hba,max_eq_left hba] using hmem)).symm

/-- If the allowed exterior contacts are the four vertices of two separated
cycle edges, at least three contacts and no isolated contact force all four. -/
lemma contact_two_edges (f : Fin m ↪ V) (h : ContactConditions G f) {y : V}
    (hy : y ∉ indexSet f) (a b c d : Fin m)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : ¬CycleAdj a c) (had : ¬CycleAdj a d)
    (hbc : ¬CycleAdj b c) (hbd : ¬CycleAdj b d)
    (sub : contacts G f y ⊆ {a,b,c,d}) :
    ∀ i, i ∈ contacts G f y ↔ i ∈ ({a,b,c,d} : Finset (Fin m)) := by
  let P := contacts G f y
  have big : 3 ≤ P.card := h.big y hy
  have nonsingle (i : Fin m) (hi : i ∈ P) := h.no_isolated y hy i hi
  have hself (i : Fin m) : ¬CycleAdj i i := by
    unfold CycleAdj
    have := i.isLt
    omega
  have hsym {i j : Fin m} : CycleAdj i j → CycleAdj j i := by
    unfold CycleAdj
    tauto
  have mAB : a ∈ P ↔ b ∈ P := by
    constructor
    · intro ha
      obtain ⟨j,hj,hij⟩ := nonsingle a ha
      have hsub := sub hj
      simp only [mem_insert,mem_singleton] at hsub
      rcases hsub with rfl | rfl | rfl | rfl
      · exact (hself _ hij).elim
      · exact hj
      · exact (hac hij).elim
      · exact (had hij).elim
    · intro hb
      obtain ⟨j,hj,hij⟩ := nonsingle b hb
      have hsub := sub hj
      simp only [mem_insert,mem_singleton] at hsub
      rcases hsub with rfl | rfl | rfl | rfl
      · exact hj
      · exact (hself _ hij).elim
      · exact (hbc hij).elim
      · exact (hbd hij).elim
  have mCD : c ∈ P ↔ d ∈ P := by
    constructor
    · intro hc
      obtain ⟨j,hj,hij⟩ := nonsingle c hc
      have hsub := sub hj
      simp only [mem_insert,mem_singleton] at hsub
      rcases hsub with rfl | rfl | rfl | rfl
      · exact (hac (hsym hij)).elim
      · exact (hbc (hsym hij)).elim
      · exact (hself _ hij).elim
      · exact hj
    · intro hd
      obtain ⟨j,hj,hij⟩ := nonsingle d hd
      have hsub := sub hj
      simp only [mem_insert,mem_singleton] at hsub
      rcases hsub with rfl | rfl | rfl | rfl
      · exact (had (hsym hij)).elim
      · exact (hbd (hsym hij)).elim
      · exact hj
      · exact (hself _ hij).elim
  have ha : a ∈ P := by
    by_cases hna : a ∈ P
    · exact hna
    exfalso
    have hnb : b ∉ P := fun hb => hna (mAB.mpr hb)
    have hsub : P ⊆ {c,d} := by
      intro i hi
      have hh := sub hi
      simp only [mem_insert,mem_singleton] at hh ⊢
      rcases hh with rfl | rfl | rfl | rfl
      · exact (hna hi).elim
      · exact (hnb hi).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hf := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have hc : c ∈ P := by
    by_cases hnc : c ∈ P
    · exact hnc
    exfalso
    have hnd : d ∉ P := fun hd => hnc (mCD.mpr hd)
    have hsub : P ⊆ {a,b} := by
      intro i hi
      have hh := sub hi
      simp only [mem_insert,mem_singleton] at hh ⊢
      rcases hh with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hnc hi).elim
      · exact (hnd hi).elim
    have hf := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  intro i
  refine ⟨fun hi => sub hi,?_⟩
  intro hi
  simp only [mem_insert,mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ha
  · exact mAB.mp ha
  · exact hc
  · exact mCD.mp hc


def clipped (f : Fin m ↪ V) (z : V) (R : Finset (Fin m)) : Finset V :=
  insert z (((univ : Finset (Fin m)) \ R).map f)

lemma clipped_root {f : Fin m ↪ V} {z : V} {R : Finset (Fin m)} :
    z ∈ clipped f z R := by simp [clipped]

lemma clipped_index {f : Fin m ↪ V} {z : V} {R : Finset (Fin m)} {i : Fin m} (hi : i ∉ R) :
    f i ∈ clipped f z R := by simp [clipped, Finset.mem_map',hi]

lemma clipped_member_cases {f : Fin m ↪ V} {z y : V} {R : Finset (Fin m)}
    (h : y ∈ clipped f z R) : y = z ∨ ∃ i, i ∉ R ∧ f i = y := by
  rcases mem_insert.mp h with h | h
  · exact Or.inl h
  · obtain ⟨i,hi,he⟩ := mem_map.mp h
    exact Or.inr ⟨i,(mem_sdiff.mp hi).2,he⟩

lemma clipped_card {f : Fin m ↪ V} {z : V} (hz : z ∉ indexSet f)
    (R : Finset (Fin m)) : (clipped f z R).card = m - R.card + 1 := by
  have hz' : z ∉ ((univ : Finset (Fin m)) \ R).map f := by
    intro h
    obtain ⟨i,_,e⟩ := mem_map.mp h
    exact hz (mem_indexSet.mpr ⟨i,e⟩)
  rw [clipped, card_insert_of_not_mem hz',Finset.card_map,card_sdiff (subset_univ R),card_univ]
  simp

lemma exists_clipped_contact {f : Fin m ↪ V} {z : V}
    (hm : 7 ≤ m) (hcore : NoSmallCore G m) (hz : z ∉ indexSet f)
    (R : Finset (Fin m)) (hr : R.card = 4)
    (hconn : Graffiti177.Con G (clipped f z R))
    (hcover : ∀ i, f i ∈ clipped f z R ∨ Graffiti177.Dominates G (clipped f z R) (f i)) :
    ∃ y, y ∉ indexSet f ∧ ¬G.Adj y z ∧ contacts G f y ⊆ R := by
  let D := clipped f z R
  have hbad : ¬ ∀ y ∉ D, Graffiti177.Dominates G D y := by
    intro hh
    have hb := hcore D hconn hh
    have c := clipped_card hz R
    change D.card = m-R.card+1 at c
    omega
  push_neg at hbad
  obtain ⟨y,hy,hd⟩ := hbad
  have hzadj : ¬G.Adj y z := fun he => hd ⟨z,clipped_root,he⟩
  have hout : y ∉ indexSet f := by
    intro h
    obtain ⟨i,rfl⟩ := mem_indexSet.mp h
    exact (hcover i).elim hy hd
  refine ⟨y,hout,hzadj,?_⟩
  intro i hi
  by_contra hn
  exact hd ⟨f i,clipped_index hn,mem_contacts.mp hi⟩

lemma card_four {α : Type*} [DecidableEq α] (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a,b,c,d} : Finset α).card = 4 := by
  rw [card_insert_of_not_mem (by simp [hab,hac,had]),
      card_insert_of_not_mem (by simp [hbc,hbd]), card_pair hcd]

/-- One local shift, written with the first old pair starting at index zero.
The marked graph argument later rotates this lemma to any start. -/
theorem shift_two_pairs_normal {f : Fin m ↪ V}
    (hm : 7 ≤ m) (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hcontact : ContactConditions G f) (hcore : NoSmallCore G m)
    {z : V} (hz : z ∉ indexSet f) {d s t : ℕ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hds : s+2 ≤ d) (hmt : d+t+2 ≤ m)
    (hsep : s+3 ≤ d+t) (_hsep' : d+t+3 ≤ m+s)
    (hz0 : ∀ i : Fin m, i.val = 0 → G.Adj z (f i))
    (hzd : ∀ i : Fin m, i.val = d → G.Adj z (f i)) :
    ∃ y ∉ indexSet f, ∀ i : Fin m, G.Adj y (f i) ↔
      i.val = s ∨ i.val = s+1 ∨ i.val = d+t ∨ i.val = d+t+1 := by
  let a : Fin m := ⟨s,by omega⟩
  let b : Fin m := ⟨s+1,by omega⟩
  let c : Fin m := ⟨d+t,by omega⟩
  let e : Fin m := ⟨d+t+1,by omega⟩
  let R : Finset (Fin m) := {a,b,c,e}
  let D := clipped f z R
  let o : Fin m := ⟨0,by omega⟩
  let k : Fin m := ⟨d,by omega⟩
  have memR (i : Fin m) : i ∈ R ↔
      i.val = s ∨ i.val = s+1 ∨ i.val = d+t ∨ i.val = d+t+1 := by
    simp only [R,mem_insert,mem_singleton,Fin.ext_iff,a,b,c,e]
  have keep (i : Fin m) (hi : i.val < s ∨ (s+2 ≤ i.val ∧ i.val < d+t) ∨ d+t+2 ≤ i.val) :
      f i ∈ D := clipped_index (fun h => by have hh := (memR i).mp h; omega)
  have oz : G.Adj z (f o) := hz0 o rfl
  have kz : G.Adj z (f k) := hzd k rfl
  have mo : f o ∈ D := keep o (Or.inl (by change 0 < s; omega))
  have mk : f k ∈ D := keep k (Or.inr (Or.inl (by change s+2 ≤ d ∧ d < d+t; omega)))
  have mz : z ∈ D := clipped_root
  have hstep (i j : Fin m) (h : i.val+1=j.val) : G.Adj (f i) (f j) :=
    (hcyc i j).mpr (Or.inl h)
  have reach_o : (G.induce (D : Set V)).Reachable ⟨z,mz⟩ ⟨f o,mo⟩ :=
    (show (G.induce (D : Set V)).Adj ⟨z,mz⟩ ⟨f o,mo⟩ from oz).reachable
  have reach_k : (G.induce (D : Set V)).Reachable ⟨z,mz⟩ ⟨f k,mk⟩ :=
    (show (G.induce (D : Set V)).Adj ⟨z,mz⟩ ⟨f k,mk⟩ from kz).reachable
  have con : Graffiti177.Con G D := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨z,mz⟩,?_⟩
    intro v
    rcases clipped_member_cases v.prop with h | ⟨i,hi,he⟩
    · have h' : v = ⟨z,mz⟩ := Subtype.ext h
      subst v
      exact SimpleGraph.Reachable.rfl
    have hv : v = ⟨f i,clipped_index hi⟩ := Subtype.ext he.symm
    rw [hv]
    have hh : i.val < s ∨ (s+2 ≤ i.val ∧ i.val < d+t) ∨ d+t+2 ≤ i.val := by
      have hh := mt (memR i).mpr hi
      omega
    rcases hh with low | mid | high
    · apply reach_o.trans (interval_any f hstep (a:=o) (b:=i) ?_)
      intro j lo hi
      apply keep j (Or.inl ?_)
      change j.val ≤ max 0 i.val at hi
      omega
    · apply reach_k.trans (interval_any f hstep (a:=k) (b:=i) ?_)
      intro j lo hi
      change min d i.val ≤ j.val at lo
      change j.val ≤ max d i.val at hi
      apply keep j (Or.inr (Or.inl (by omega)))
    · let l : Fin m := ⟨m-1,by omega⟩
      have hl : f l ∈ D := keep l (Or.inr (Or.inr (by have := i.isLt; change d+t+2 ≤ m-1; omega)))
      have hwrap : G.Adj (f o) (f l) := (hcyc o l).mpr
        (Or.inr (Or.inr (Or.inl ⟨rfl,by change m-1+1=m; omega⟩)))
      have hW : (G.induce (D : Set V)).Adj ⟨f o,mo⟩ ⟨f l,hl⟩ := hwrap
      apply (reach_o.trans hW.reachable).trans (interval_any f hstep (a:=l) (b:=i) ?_)
      intro j lo _
      change min (m-1) i.val ≤ j.val at lo
      have := i.isLt
      exact keep j (Or.inr (Or.inr (by omega)))
  have cov (i : Fin m) : f i ∈ D ∨ Graffiti177.Dominates G D (f i) := by
    by_cases hi : i ∈ R
    · right
      have h := (memR i).mp hi
      rcases h with ha | hb | hc | hd
      · let j : Fin m := ⟨s-1,by omega⟩
        exact ⟨f j,keep j (Or.inl (by change s-1<s; omega)),
          (hstep j i (by change s-1+1=i.val; omega)).symm⟩
      · let j : Fin m := ⟨s+2,by omega⟩
        exact ⟨f j,keep j (Or.inr (Or.inl (by change s+2≤s+2 ∧ s+2<d+t; omega))),
          hstep i j (by change i.val+1=s+2; omega)⟩
      · let j : Fin m := ⟨d+t-1,by omega⟩
        exact ⟨f j,keep j (Or.inr (Or.inl (by change s+2≤d+t-1 ∧ d+t-1<d+t; omega))),
          (hstep j i (by change d+t-1+1=i.val; omega)).symm⟩
      · by_cases hh : d+t+2 < m
        · let j : Fin m := ⟨d+t+2,hh⟩
          exact ⟨f j,keep j (Or.inr (Or.inr (by rfl))),hstep i j
            (by change i.val+1=d+t+2; omega)⟩
        · exact ⟨f o,mo,(hcyc i o).mpr (Or.inr (Or.inr (Or.inr ⟨rfl,by omega⟩)))⟩
    · exact Or.inl (clipped_index hi)
  have nab : a ≠ b := fun eq => by have h := congrArg Fin.val eq; change s=s+1 at h; omega
  have nac : a ≠ c := fun eq => by have h := congrArg Fin.val eq; change s=d+t at h; omega
  have nae : a ≠ e := fun eq => by have h := congrArg Fin.val eq; change s=d+t+1 at h; omega
  have nbc : b ≠ c := fun eq => by have h := congrArg Fin.val eq; change s+1=d+t at h; omega
  have nbe : b ≠ e := fun eq => by have h := congrArg Fin.val eq; change s+1=d+t+1 at h; omega
  have nce : c ≠ e := fun eq => by have h := congrArg Fin.val eq; change d+t=d+t+1 at h; omega
  have rcard : R.card = 4 := card_four a b c e nab nac nae nbc nbe nce
  obtain ⟨y,hy,_,hsub⟩ := exists_clipped_contact hm hcore hz R rcard con cov
  have hac : ¬CycleAdj a c := by unfold CycleAdj; dsimp [a,c]; omega
  have hae : ¬CycleAdj a e := by unfold CycleAdj; dsimp [a,e]; omega
  have hbc : ¬CycleAdj b c := by unfold CycleAdj; dsimp [b,c]; omega
  have hbe : ¬CycleAdj b e := by unfold CycleAdj; dsimp [b,e]; omega
  have he := contact_two_edges f hcontact hy a b c e nab nce hac hae hbc hbe hsub
  refine ⟨y,hy,fun i => ?_⟩
  exact (mem_contacts (f:=f) (z:=y) (i:=i)).symm.trans ((he i).trans (memR i))

#print axioms shift_two_pairs_normal


/-- A normalized two-pair contact profile, with cyclic start a and gap d. -/
def HasDouble (G : SimpleGraph V) (f : Fin m ↪ V) (a : Fin m) (d : ℕ) : Prop :=
  ∃ z ∉ indexSet f, ∀ i : Fin m, G.Adj z (f (rot a i)) ↔
    i.val = 0 ∨ i.val = 1 ∨ i.val = d ∨ i.val = d+1

lemma shift_double {f : Fin m ↪ V} (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hcontact : ContactConditions G f) (hcore : NoSmallCore G m)
    {a : Fin m} {d s t : ℕ} (hp : HasDouble G f a d)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hds : s+2 ≤ d) (hmt : d+t+2 ≤ m)
    (hsep : s+3 ≤ d+t) (hsep' : d+t+3 ≤ m+s) :
    HasDouble G f (rot a ⟨s,by omega⟩) (d+t-s) := by
  obtain ⟨z,hz,hp⟩ := hp
  let F := (rotEmb a).trans f
  have hF : ∀ i j, G.Adj (F i) (F j) ↔ CycleAdj i j := fun i j =>
    (hcyc _ _).trans (cycleAdj_rotate (by omega) a i j)
  have hcontact' : ContactConditions G F := contact_conditions_rotate (by omega) f hcontact a
  have hz' : z ∉ indexSet F := by simpa only [F,indexSet_rot] using hz
  obtain ⟨y,hy,hprof⟩ := shift_two_pairs_normal hm hF hcontact' hcore hz'
    hs ht hds hmt hsep hsep'
    (fun i hi => (hp i).mpr (Or.inl hi))
    (fun i hi => (hp i).mpr (Or.inr (Or.inr (Or.inl hi))))
  refine ⟨y,by simpa only [F,indexSet_rot] using hy,fun i => ?_⟩
  let ss : Fin m := ⟨s,by omega⟩
  change G.Adj y (f (rot (rot a ss) i)) ↔ _
  rw [rot_assoc]
  change G.Adj y (F (rot ss i)) ↔ _
  rw [hprof]
  change (s+i.val)%m = s ∨ (s+i.val)%m = s+1 ∨
    (s+i.val)%m = d+t ∨ (s+i.val)%m = d+t+1 ↔ _
  by_cases hh : s+i.val < m
  · rw [Nat.mod_eq_of_lt hh]
    omega
  · have hsub : (s+i.val)%m = s+i.val-m := by
      have := i.isLt
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    have := i.isLt
    omega

theorem no_two_pair_profiles {f : Fin m ↪ V} (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hcontact : ContactConditions G f) (hcore : NoSmallCore G m)
    {u v : Fin m} (hfar : 2 < G.dist (f u) (f v)) :
    ∀ a : Fin m, ∀ d, 3 ≤ d → d ≤ m-3 → ¬ HasDouble G f a d := by
  intro a d hd hd' hpd
  obtain ⟨q,hq,hq',hrot⟩ := separated_index_of_dist f hcyc (by omega) hfar
  let move (a : Fin m) (d s t : ℕ) (hpd : HasDouble G f a d)
      (hs : 1 ≤ s) (ht : 1 ≤ t) (hds : s+2 ≤ d) (hmt : d+t+2 ≤ m)
      (hsep : s+3 ≤ d+t) (hsep' : d+t+3 ≤ m+s) :=
    shift_double hm hcyc hcontact hcore hpd hs ht hds hmt hsep hsep'
  have hUp (k : ℕ) (dk : d ≤ k) (kk : k ≤ m-3) : ∃ b, HasDouble G f b k := by
    induction k,dk using Nat.le_induction with
    | base => exact ⟨a,hpd⟩
    | succ j dj ih =>
      obtain ⟨b,hb⟩ := ih (by omega)
      have e := move b j 1 2 hb (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hrew : j+2-1=j+1 := by omega
      rw [hrew] at e
      exact ⟨_,e⟩
  have hDown (k : ℕ) (hk : k ≤ m-3) (b : Fin m) (hb : HasDouble G f b k)
      (j : ℕ) (hj : 3 ≤ j) (hjk : j ≤ k) : ∃ b, HasDouble G f b j := by
    induction k using Nat.strong_induction_on generalizing b j with
    | h k ih =>
      by_cases e : k = j
      · subst k; exact ⟨b,hb⟩
      · have hh : k-1 < k := by omega
        have hp := move b k 2 1 hb (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hrew : k+1-2=k-1 := by omega
        rw [hrew] at hp
        exact ih (k-1) hh (by omega) _ hp j hj (by omega)
  have htarg : ∃ b, HasDouble G f b q.val := by
    by_cases h : d ≤ q.val
    · exact hUp q.val h hq'
    · exact hDown d hd' a hpd q.val hq (by omega)
  obtain ⟨b,hb⟩ := htarg
  obtain ⟨j,hj⟩ := rot_surjective b u
  have allr (k : ℕ) (hk : k < m) : HasDouble G f (rot b ⟨k,hk⟩) q.val := by
    induction k with
    | zero =>
      simpa only [rot_zero b hk] using hb
    | succ k ih =>
      have hh : k < m := by omega
      have h0 := move (rot b ⟨k,hh⟩) q.val 1 1 (ih hh)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hnum : q.val + 1 - 1 = q.val := by omega
      rw [hnum,rot_assoc] at h0
      have hR : rot (⟨k,hh⟩ : Fin m) ⟨1,by omega⟩ = ⟨k+1,hk⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hk
      rw [hR] at h0
      exact h0
  have hh := allr j.val j.isLt
  change HasDouble G f (rot b j) q.val at hh
  rw [hj] at hh
  obtain ⟨z,_,hz⟩ := hh
  have e0 := (hz ⟨0,by omega⟩).mpr (Or.inl rfl)
  have e1 := (hz q).mpr (Or.inr (Or.inr (Or.inl rfl)))
  rw [rot_zero] at e0
  rw [hrot] at e1
  have test : G.dist (f u) (f v) ≤ 2 :=
    G.dist_le (SimpleGraph.Walk.cons e0.symm e1.toWalk)
  omega

#print axioms no_two_pair_profiles
end Graffiti183.Exceptional
