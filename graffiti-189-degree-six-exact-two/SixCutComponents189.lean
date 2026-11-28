import SixCutLowSingleton189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts aTwos bTwos two_local_counts from SixCutFar189
open private port_cost each_foreign_port_is_distance_two distinct_shore_twos_dis from SixCutHighShore189
open private Vis vis_card_ge_two degree_le_shore_add_one from AdjacentCutFiveComponents189
open private a_sub_vis b_sub_vis b_port_cost singleton_low_of_three two_other_shores two_has_dark
  dark_shore_size no_two_common_shores from SixCutLowSingleton189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem local_universal_of_no_local_two (hc : G.Connected)
    (C : Cmp G a b) {x : V} (xc : x∈Shore C)
    (forbid : ∀ z∈Shore C,z∉DistanceTwo G x) : ∀ z∈Shore C,z=x ∨ G.Adj x z := by
  intro z zc
  let A : Set V := ↑(Shore C)
  obtain ⟨p⟩ := (shore_connected C).preconnected (⟨x,xc⟩ : A) (⟨z,zc⟩ : A)
  have Q {u v : A} (q : (G.induce A).Walk u v) :
      (u.val=x ∨ G.Adj x u.val) → (v.val=x ∨ G.Adj x v.val) := by
    induction q with
    | nil => exact id
    | @cons u w v uw q ih =>
      intro h
      apply ih
      by_cases wx : w.val=x
      · exact .inl wx
      right
      change G.Adj u.val w.val at uw
      rcases h with xu|xu
      · exact xu ▸ uw
      by_contra nq
      exact forbid w.val (Finset.mem_coe.mp w.property) (d2 hc (Ne.symm wx) nq xu uw)
  exact Q p (.inl rfl)

private theorem no_exclusive_only_shore (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    {S C D : Cmp G a b} (sc : S≠C) (sd : S≠D) (cd : C≠D)
    {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (v6 : (Vis C).card+(Vis D).card≤6) (m2 : 2≤(Vis C).card)
    (C7 : 7≤(Shore C).card)
    (highC : ∀ z∈Shore C,6≤G.degree z) (highD : ∀ z∈Shore D,6≤G.degree z)
    (no : ¬∃ x∈Shore C,G.Adj a x ∧ G.Adj b x) : False := by
  classical
  have a₁ := card_le_card (a_sub_vis C)
  have a₂ := card_le_card (a_sub_vis D)
  have b₁ := card_le_card (b_sub_vis C)
  have b₂ := card_le_card (b_sub_vis D)
  have AC := distanceTwo_le_of_even 6 a (even a)
  have BC := distanceTwo_le_of_even 6 b (even b)
  have qa := two_local_counts _ _ (distinct_shore_twos_dis cd) (DistanceTwo G a)
    inter_subset_right inter_subset_right
  have qb : (bTwos C).card+(bTwos D).card≤(DistanceTwo G b).card :=
    two_local_counts _ _ ((shore_disjoint cd).mono inter_subset_left inter_subset_left)
      (DistanceTwo G b) inter_subset_right inter_subset_right
  have ueq : aPorts C∪bPorts C=Vis C := by
    ext z
    simp [aPorts,bPorts,Vis,and_or_left]
  have ud : Disjoint (aPorts C) (bPorts C) := by
    apply disjoint_left.mpr
    intro z zm zn
    exact no ⟨z,(mem_filter.mp zm).1,(mem_filter.mp zm).2,(mem_filter.mp zn).2⟩
  have m := card_union_of_disjoint ud
  rw [ueq] at m
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yc,by'⟩ := shore_hit_b ab conn C
  obtain ⟨u,ud',au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vd,bv⟩ := shore_hit_b ab conn D
  have bx : ¬G.Adj b x := fun h=>no ⟨x,xc,ax,h⟩
  have ay : ¬G.Adj a y := fun h=>no ⟨y,yc,h,by'⟩
  have lo (p q d : ℕ) (h : 6≤d) (j : d≤p+q+1) : 5≤p+q := by omega
  have costx := port_cost hc C (mem_filter.mpr ⟨xc,ax⟩)
  have costy := b_port_cost hc C (mem_filter.mpr ⟨yc,by'⟩)
  simp only [if_neg bx,if_neg ay,add_zero] at costx costy
  have costu : 5≤(aPorts D).card+(aTwos D).card := by
    have j := port_cost hc D (mem_filter.mpr ⟨ud',au⟩)
    split at j <;> exact lo _ _ _ (highD u ud') (by omega)
  have costv : 5≤(bPorts D).card+(bTwos D).card := by
    have j := b_port_cost hc D (mem_filter.mpr ⟨vd,bv⟩)
    split at j <;> exact lo _ _ _ (highD v vd) (by omega)
  have xhigh := highC x xc
  have yhigh := highC y yc
  have oneA : (aPorts C).card=1 := by omega
  have aFour : (aPorts D).card=4 := by omega
  have bsD : s∉Shore D := by
    have h : s∈Shore S := by simp [sS]
    exact fun t=>disjoint_left.mp (shore_disjoint sd) h t
  have adj : G.Adj a b := by
    by_contra bad
    have ba := d2 hc ab bad as' bs'.symm
    let Q := aTwos C∪aTwos D
    have bq : b∉Q := by
      intro t
      rcases mem_union.mp t with t|t
      · exact (shore_off C).2 (mem_inter.mp t).1
      exact (shore_off D).2 (mem_inter.mp t).1
    have sub : insert b Q⊆DistanceTwo G a :=
      insert_subset ba (union_subset inter_subset_right inter_subset_right)
    have k := card_le_card sub
    rw [card_insert_of_not_mem bq] at k
    have u := card_union_of_disjoint (distinct_shore_twos_dis cd)
    change Q.card=_ at u
    omega
  have xp : x∈aPorts C := mem_filter.mpr ⟨xc,ax⟩
  let F := insert b (insert s (aPorts D))
  have F6 : F.card=6 := by
    have n : s∉aPorts D := fun p=>bsD (mem_filter.mp p).1
    have n' : b∉insert s (aPorts D) := by
      intro h
      rcases mem_insert.mp h with h|h
      · exact bs'.ne h
      exact (shore_off D).2 (mem_filter.mp h).1
    dsimp only [F]
    rw [card_insert_of_not_mem n',card_insert_of_not_mem n,aFour]
  have sub : F⊆DistanceTwo G x := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact d2 hc (fun e=>(shore_off C).2 (e ▸ xc)) (fun k=>bx k.symm) ax.symm adj
    rcases mem_insert.mp zm with rfl|zm
    · have ss : z∈aPorts S := mem_filter.mpr ⟨by simp [sS],as'⟩
      exact each_foreign_port_is_distance_two hc sc.symm xp ss
    exact each_foreign_port_is_distance_two hc cd xp zm
  have sat : F=DistanceTwo G x :=
    eq_of_subset_of_card_le sub (by have n := distanceTwo_le_of_even 6 x (even x); omega)
  have noD2 : ∀ z∈Shore C,z∉DistanceTwo G x := by
    intro z zc zm
    rw [←sat] at zm
    rcases mem_insert.mp zm with rfl|zm
    · exact (shore_off C).2 zc
    rcases mem_insert.mp zm with rfl|zm
    · exact disjoint_left.mp (shore_disjoint sc) (by simp [sS]) zc
    exact disjoint_left.mp (shore_disjoint cd) zc (mem_filter.mp zm).1
  have uni := local_universal_of_no_local_two hc C xc noD2
  have sx : aPorts C={x} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr xp) (by simp [oneA])).symm
  have inc : (Shore C).erase x⊆aTwos C := by
    intro z zm
    have ⟨zx,zc⟩ := mem_erase.mp zm
    have az : ¬G.Adj a z := by
      intro e
      have g : z∈aPorts C := mem_filter.mpr ⟨zc,e⟩
      exact zx (mem_singleton.mp (sx ▸ g))
    have an : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc an az ax ((uni z zc).resolve_left zx)⟩
  have cnt := card_le_card inc
  have er := card_erase_add_one xc
  omega

/-- At degree six, with at most seven even-distance vertices at each vertex,
deleting a separating pair always leaves exactly two components. -/
theorem component_card_eq_two_at_six (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) : Nat.card (Cmp G a b)=2 := by
  classical
  by_contra h
  have big : 3≤Nat.card (Cmp G a b) := by omega
  obtain ⟨S,s,sS,as',bs',low⟩ := singleton_low_of_three hc ab even conn degree big
  obtain ⟨C,D,sc,sd,cd⟩ := two_other_shores S big
  have high (K : Cmp G a b) (sk : S≠K) : ∀ z∈Shore K,6≤G.degree z := by
    intro z zk
    have ne : z≠s := fun e=>disjoint_left.mp (shore_disjoint sk) (by simp [sS]) (e ▸ zk)
    exact (degree z s ne).resolve_right (by omega)
  have v6 : (Vis C).card+(Vis D).card≤6 := by
    have ss : s∈Shore S := by simp [sS]
    have sub (K : Cmp G a b) (sk : S≠K) : Vis K⊆DistanceTwo G s := by
      intro z zh
      have ⟨zk,p⟩ := mem_filter.mp zh
      have ne : s≠z := fun e=>disjoint_left.mp (shore_disjoint sk) ss (e.symm ▸ zk)
      have nz : ¬G.Adj s z := by
        intro j
        rcases shore_closed S s ss z j with z|z|z
        · exact (shore_off K).1 (z ▸ zk)
        · exact (shore_off K).2 (z ▸ zk)
        exact disjoint_left.mp (shore_disjoint sk) z zk
      rcases p with az|bz
      · exact d2 hc ne nz as'.symm az
      exact d2 hc ne nz bs'.symm bz
    exact (two_local_counts _ _ ((shore_disjoint cd).mono (fun _ h=>(mem_filter.mp h).1)
      (fun _ h=>(mem_filter.mp h).1)) _ (sub C sc) (sub D sd)).trans
      (distanceTwo_le_of_even 6 s (even s))
  obtain ⟨x,xc,_⟩ := shore_hit_a ab conn C
  obtain ⟨y,yd,_⟩ := shore_hit_a ab conn D
  have hx := high C sc x xc
  have hy := high D sd y yd
  have rC := degree_le_shore_add_one C xc
  have rD := degree_le_shore_add_one D yd
  have cv := vis_card_ge_two ab conn C (by omega)
  have dv := vis_card_ge_two ab conn D (by omega)
  obtain ⟨u,uc,un⟩ := two_has_dark C (high C sc) (by omega) ⟨x,xc⟩
  obtain ⟨v,vd,vn⟩ := two_has_dark D (high D sd) (by omega) ⟨y,yd⟩
  have c7 := dark_shore_size C uc un (high C sc u uc)
  have d7 := dark_shore_size D vd vn (high D sd v vd)
  by_cases hC : ∃ x∈Shore C,G.Adj a x ∧ G.Adj b x
  · by_cases hD : ∃ y∈Shore D,G.Adj a y ∧ G.Adj b y
    · obtain ⟨q,qc,aq,bq⟩ := hC
      obtain ⟨r,rd,ar,br⟩ := hD
      exact no_two_common_shores hc ab even sc sd cd sS as' bs' v6 c7 d7
        (high C sc) (high D sd) qc rd aq bq ar br
    exact no_exclusive_only_shore hc ab even conn sd sc cd.symm sS as' bs' (by omega)
      dv d7 (high D sd) (high C sc) hD
  exact no_exclusive_only_shore hc ab even conn sc sd cd sS as' bs' v6 cv c7
    (high C sc) (high D sd) hC

#print axioms component_card_eq_two_at_six
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
