import PendantAudit
namespace Graffiti384b.OddStars.LeafCritical
open Finset SimpleGraph PositivePalette
open private Graffiti384b.cut Graffiti384b.cut_symm Graffiti384b.cut_insert Graffiti384b.nbr_partition Graffiti384b.maximal_side from Proof384b
open private Repair.omit_set Repair.nbr_mono Repair.triangles_le_choose from Repair384b
open private OddStars.crossing OddStars.crossing_compl OddStars.translated from CutAtVertex
open private Prune.links from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Maximum (A : Finset V) := ∀ S, Graffiti384b.cut G S Sᶜ ≤ Graffiti384b.cut G A Aᶜ
def crossed (A : Finset V) (v : V) := (G.neighborFinset v).filter (fun w => ¬(v∈A ↔ w∈A))
def critical (A : Finset V) := (high G).filter (fun v => (crossed G A v).card = 2)
def active (A : Finset V) := (high G).filter (fun v => 2≤nbr G v (if v∈A then A else Aᶜ))

private theorem max_compl {A : Finset V} (m : Maximum G A) : Maximum G Aᶜ := by
  intro S; simpa only [compl_compl,Graffiti384b.cut_symm G Aᶜ A] using m S

private theorem max_covers {A : Finset V} (m : Maximum G A) :
    ∀v∈high G, v∈A → 2≤nbr G v Aᶜ := by
  intro v h va
  have := Graffiti384b.maximal_side G m va
  have := Graffiti384b.nbr_partition G v A
  have := (mem_filter.mp h).2
  omega

private theorem balanced (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (l : ∀v∈high (patch G ∅),v∈A → 2≤nbr (patch G ∅) v Aᶜ)
    (r : ∀v∈high (patch G ∅),v∈Aᶜ → 2≤nbr (patch G ∅) v A) :
    2*((high (patch G ∅))∩A).card=(high (patch G ∅)).card := by
  let J := patch G ∅
  let W := high J
  have mono := Prerequisites.gamma_mono G J (fun _ _ h => h.1)
  have a := Repair.omit_set J (W∩A) (fun v vm => (l v (mem_inter.mp vm).1 (mem_inter.mp vm).2).trans
    (Repair.nbr_mono J _ (fun _ h => mem_compl.mpr (fun k => mem_compl.mp h (mem_inter.mp k).2))))
  have b := Repair.omit_set J (W\A) (fun v vm => (r v (mem_sdiff.mp vm).1 (mem_compl.mpr (mem_sdiff.mp vm).2)).trans
    (Repair.nbr_mono J _ (fun _ h => mem_compl.mpr (fun k => (mem_sdiff.mp k).2 h))))
  have pc := card_sdiff_add_card_inter W A
  change W.card+1=(types G).card at size
  change 2*(W∩A).card=W.card
  unfold bound at bad
  omega

private theorem moved {A : Finset V} {v : V} (inA : v∈A)
    (eq : nbr G v A=nbr G v Aᶜ) (m : Maximum G A) : Maximum G (A.erase v) := by
  intro S
  apply (m S).trans
  rw [compl_erase,Graffiti384b.cut_symm G (A.erase v),Graffiti384b.cut_insert G (by simpa using inA),Graffiti384b.cut_symm G Aᶜ (A.erase v)]
  have t := Graffiti384b.cut_insert G (not_mem_erase v A) Aᶜ
  rw [insert_erase inA] at t
  have e : nbr G v (A.erase v)=nbr G v A := by
    unfold nbr; congr 1; ext y; by_cases h : y=v
    · subst y; simp
    · simp [h]
  omega

private theorem balance_max (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) :
    2*(high (patch G ∅)∩A).card=(high (patch G ∅)).card :=
  balanced G bad size (max_covers _ m) (by simpa only [compl_compl] using max_covers _ (max_compl _ m))

omit [Fintype V] in
private theorem erase_diff (W A : Finset V) {x : V} (wh : x∈W) (wa : x∈A) :
    (W∩A.erase x).card < (W∩A).card := by
  have e : W∩A.erase x=(W∩A).erase x := by ext; simp; tauto
  rw [e]; exact card_erase_lt_of_mem (mem_inter.mpr ⟨wh,wa⟩)

theorem strict_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {v : V} (vh : v∈high (patch G ∅)) (va : v∈A) :
    nbr (patch G ∅) v A < nbr (patch G ∅) v Aᶜ := by
  apply lt_of_le_of_ne (Graffiti384b.maximal_side _ m va)
  intro e
  have a := balance_max G bad size m
  have b := balance_max G bad size (moved _ va e m)
  have c := erase_diff _ _ vh va
  omega

omit [Fintype V] in
private theorem nbr_erase {A : Finset V} {x : V} (xa : x∈A) (v : V) :
    nbr G v A = nbr G v (A.erase x) + (if G.Adj v x then 1 else 0) := by
  have ex : nbr G v (insert x (A.erase x)) = nbr G v (A.erase x) + (if G.Adj v x then 1 else 0) := by
    by_cases edge : G.Adj v x <;> simp [nbr,Finset.filter_insert,edge,Nat.add_comm]
  rwa [insert_erase xa] at ex

theorem active_contact_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {x : V} (xh : x∈high (patch G ∅)) (xa : x∈A)
    (two : 2≤nbr (patch G ∅) x A) :
    ∃y∈high (patch G ∅), y∈Aᶜ ∧ (patch G ∅).Adj y x ∧ nbr (patch G ∅) y A=2 := by
  classical
  let J := patch G ∅
  by_contra! no
  have r := max_covers J (max_compl J m)
  rw [compl_compl] at r
  have q := balanced G bad size (A:=A.erase x) (by
    intro v vh va
    exact (max_covers J m v vh (mem_of_mem_erase va)).trans (Repair.nbr_mono J _ (fun _ hm =>
      mem_compl.mpr (fun hm' => mem_compl.mp hm (mem_of_mem_erase hm'))))) (by
    intro v vh va
    by_cases same : v=x
    · subst v
      have h := nbr_erase J xa x
      simp only [SimpleGraph.irrefl,if_false,Nat.add_zero] at h
      change 2≤nbr J x (A.erase x)
      rw [←h]; exact two
    · have outside : v∈Aᶜ := mem_compl.mpr (fun vin => mem_compl.mp va (mem_erase.mpr ⟨same,vin⟩))
      change 2≤nbr J v (A.erase x)
      have a := r v vh outside
      have b := nbr_erase J xa v
      by_cases yx : J.Adj v x
      · have c := no v vh outside yx
        change nbr J v A ≠ 2 at c
        rw [if_pos yx] at b; omega
      · rw [if_neg yx,Nat.add_zero] at b; omega)
  have h := balance_max G bad size m
  have k := erase_diff _ _ xh xa
  omega

/-- Every edge of the empty patch belongs to an incident triangle. -/
theorem skeleton_degree_bound (v : V) : (patch G ∅).degree v≤2*trianglesAt G v := by
  let L := Prune.links G v
  have sub : (patch G ∅).neighborFinset v⊆L.biUnion id := by
    intro w wm
    have edge := ((patch G ∅).mem_neighborFinset ..).mp wm
    obtain ⟨y,vy,wy⟩ := edge.2.resolve_right (by simp)
    have h : ({w,y} : Finset V)∈L := by
      apply mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset ((G.mem_neighborFinset ..).mpr edge.1)
        (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr vy)),card_pair wy.ne⟩,?_⟩
      intro i im j jm ne
      simp only [mem_insert,mem_singleton] at im jm
      rcases im with rfl|rfl <;> rcases jm with rfl|rfl <;> first | exact (ne rfl).elim | exact wy | exact wy.symm
    exact mem_biUnion.mpr ⟨_,h,mem_insert_self ..⟩
  have total : (∑p ∈ L,p.card)=L.card*2 := by
    calc
      _ = ∑_p ∈ L,2 := sum_congr rfl (fun p pm => (mem_powersetCard.mp (mem_filter.mp pm).1).2)
      _ = _ := by simp
  have b := (card_le_card sub).trans (card_biUnion_le (s:=L) (t:=id))
  rw [card_neighborFinset_eq_degree] at b
  change (patch G ∅).degree v≤∑p ∈ L,p.card at b
  change (patch G ∅).degree v≤2*L.card
  omega

private theorem crit_cubic_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {v : V} (vh : v∈high (patch G ∅)) (va : v∈A)
    (cross : nbr (patch G ∅) v Aᶜ=2) : (patch G ∅).degree v=3 := by
  have s := strict_side G bad size m vh va
  have p := Graffiti384b.nbr_partition (patch G ∅) v A
  have := (mem_filter.mp vh).2
  omega

theorem critical_cubic (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {v : V} (vm : v∈critical (patch G ∅) A) :
    (patch G ∅).degree v=3 := by
  obtain ⟨vh,two⟩ := mem_filter.mp vm
  change (OddStars.crossing (patch G ∅) A v).card=2 at two
  rw [OddStars.translated] at two
  by_cases va : v∈A
  · exact crit_cubic_side G bad size m vh va (by simpa [va] using two)
  · apply crit_cubic_side G bad size (max_compl _ m) vh (mem_compl.mpr va)
    simpa [va] using two

theorem at_most_two_critical (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) : (critical (patch G ∅) A).card≤2 := by
  let C := critical (patch G ∅) A
  have range {v : V} (vm : v∈C) : 2≤trianglesAt G v ∧ trianglesAt G v≤3 := by
    have deg := critical_cubic G bad size m vm
    have low := skeleton_degree_bound G v
    have up := Repair.triangles_le_choose (patch G ∅) v
    rw [deg,patch_scores] at up
    have val : Nat.choose 3 2=3 := by decide
    omega
  have inj : Set.InjOn (trianglesAt G) (C : Set V) := fun _ xm _ _ e => distinct_rich G bad (range xm).1 e
  have inc : C.image (trianglesAt G) ⊆ {2,3} := by
    intro k km; obtain ⟨v,vm,rfl⟩ := mem_image.mp km
    have lr := range vm
    simp only [mem_insert,mem_singleton]; omega
  have h := card_le_card inc
  rw [card_image_iff.mpr inj,card_pair (by decide : (2:ℕ)≠3)] at h
  exact h

theorem at_most_four_active (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) : (active (patch G ∅) A).card≤4 := by
  let J := patch G ∅
  let C := critical J A
  have inc : active J A ⊆ C.biUnion (crossed J A) := by
    intro x xm
    obtain ⟨xh,two⟩ := mem_filter.mp xm
    by_cases xa : x∈A
    · rw [if_pos xa] at two
      obtain ⟨y,yh,yo,yx,yt⟩ := active_contact_side G bad size m xh xa two
      have yoff := mem_compl.mp yo
      refine mem_biUnion.mpr ⟨y,mem_filter.mpr ⟨yh,?_⟩,mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr yx,?_⟩⟩
      · change (OddStars.crossing J A y).card=2
        simpa only [OddStars.translated,if_neg yoff] using yt
      · exact fun e => yoff (e.mpr xa)
    · rw [if_neg xa] at two
      obtain ⟨y,yh,yo,yx,yt⟩ := active_contact_side G bad size (max_compl _ m) xh (mem_compl.mpr xa) two
      rw [compl_compl] at yo
      refine mem_biUnion.mpr ⟨y,mem_filter.mpr ⟨yh,?_⟩,mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr yx,?_⟩⟩
      · change (OddStars.crossing J A y).card=2
        simpa only [OddStars.translated,if_pos yo] using yt
      · exact fun e => xa (e.mp yo)
  have h := (card_le_card inc).trans (card_biUnion_le (s:=C) (t:=crossed J A))
  have sum : (∑y ∈ C,(crossed J A y).card)=C.card*2 := by
    calc
      _ = ∑_y ∈ C,2 := sum_congr rfl (fun _ ym => (mem_filter.mp ym).2)
      _ = _ := by simp
  have cap : C.card≤2 := at_most_two_critical G bad size m
  change (active J A).card≤4
  omega

end Graffiti384b.OddStars.LeafCritical
#print axioms Graffiti384b.OddStars.LeafCritical.strict_side
#print axioms Graffiti384b.OddStars.LeafCritical.active_contact_side

#print axioms Graffiti384b.OddStars.LeafCritical.skeleton_degree_bound
#print axioms Graffiti384b.OddStars.LeafCritical.critical_cubic
#print axioms Graffiti384b.OddStars.LeafCritical.at_most_two_critical
#print axioms Graffiti384b.OddStars.LeafCritical.at_most_four_active
