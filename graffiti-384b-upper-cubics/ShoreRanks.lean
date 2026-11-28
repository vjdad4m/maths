import ShoreCounts
namespace Graffiti384b.OddStars.ShoreRanks
open Finset SimpleGraph LeafCritical ShorePairs ShoreCounts
open private OddStars.crossing OddStars.translated from CutAtVertex
open private OddStars.ShoreCounts.in_high from ShoreCounts
open private OddStars.LeafCritical.balance_max OddStars.LeafCritical.max_compl OddStars.LeafCritical.max_covers from LeafCritical
open private Repair.nbr_mono Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem two_centers (e f : V) (R : Finset V) (pos : R.Nonempty)
    (deg : ∀x∈R,x≠e → x≠f → nbr G x R≤1) : (pairs G R).card<R.card := by
  classical
  induction R using Finset.strongInduction with
  | H S ih =>
    by_cases sm : S.card≤2
    · have v := (card_filter_le (s:=S.powersetCard 2) (fun p => ∀ x∈p,∀y∈p,x≠y → G.Adj x y))
      rw [card_powersetCard] at v
      change (pairs G S).card≤_ at v
      have positive := card_pos.mpr pos
      rcases (show S.card=1 ∨ S.card=2 by omega) with eq|eq
      · have k : Nat.choose 1 2=0 := by decide
        rw [eq,k] at v; rw [eq]; omega
      · have k : Nat.choose 2 2=1 := by decide
        rw [eq,k] at v; rw [eq]; omega
    have sz := card_insert_le e ({f}:Finset V)
    obtain ⟨x,xm,off⟩ := exists_mem_not_mem_of_card_lt_card (s:=({e,f}:Finset V)) (t:=S)
      (by simp only [card_singleton] at sz; omega)
    have ne : x≠e ∧ x≠f := by simpa using off
    let U := S.erase x
    have uc : U.card+1=S.card := card_erase_add_one xm
    have posU : U.Nonempty := card_pos.mp (by omega)
    have sub : U⊆S := erase_subset ..
    have cost := ih U (erase_ssubset xm) posU (fun y ym ye yf => (Repair.nbr_mono G _ sub).trans (deg y (sub ym) ye yf))
    have low := (Repair.nbr_mono G x sub).trans (deg x xm ne.1 ne.2)
    have st := pairs_insert G (not_mem_erase x S)
    rw [insert_erase xm] at st
    change (pairs G S).card=(pairs G U).card+nbr G x U at st
    omega

private theorem six_high (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    (has : (high (patch G ∅)).Nonempty) {A : Finset V} (m : Maximum (patch G ∅) A) :
    6≤(high (patch G ∅)).card := by
  let J := patch G ∅
  let H := high J
  have even := OddStars.LeafCritical.balance_max G bad size m
  change 2*(H∩A).card=H.card at even
  by_contra! sm
  change H.card<6 at sm
  have deg {v : V} (vh : v∈H) : J.degree v<H.card := by
    have sub : J.neighborFinset v⊆H.erase v := fun w wm =>
      let vw := (J.mem_neighborFinset ..).mp wm
      mem_erase.mpr ⟨vw.ne.symm,OddStars.ShoreCounts.in_high G bad size vw⟩
    have b := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem vh] at b
    have pos : 0<H.card := card_pos.mpr ⟨v,vh⟩
    omega
  have range {v : V} (vm : v∈H) : 2≤trianglesAt G v ∧ trianglesAt G v≤3 := by
    have low := skeleton_degree_bound G v
    have d := deg vm
    have ge : 3≤J.degree v := (mem_filter.mp vm).2
    have eq : J.degree v=3 := by omega
    have up := Repair.triangles_le_choose J v
    change J.degree v≤_ at low
    rw [eq] at up
    change trianglesAt (patch G ∅) v≤_ at up
    rw [patch_scores] at up
    have : Nat.choose 3 2=3 := by decide
    omega
  have inj : Set.InjOn (trianglesAt G) (H : Set V) := fun _ xm _ _ eq => distinct_rich G bad (range xm).1 eq
  have inc : H.image (trianglesAt G)⊆{2,3} := by
    intro k km; obtain ⟨v,vm,rfl⟩ := mem_image.mp km
    have := range vm; simp only [mem_insert,mem_singleton]; omega
  have c := card_le_card inc
  rw [card_image_iff.mpr inj,card_pair (by decide : (2:ℕ)≠3)] at c
  obtain ⟨v,vm⟩ := has
  have h := deg vm
  have ge : 3≤J.degree v := (mem_filter.mp vm).2
  omega

private theorem sharp_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) (e f : V)
    (sparse : ∀x∈Aᶜ,x≠e → x≠f → nbr (patch G ∅) x Aᶜ≤1)
    (thin : (∀x∈A,nbr (patch G ∅) x A≤1) ∨ (∀x∈Aᶜ,nbr (patch G ∅) x Aᶜ≤1))
    {v : V} (va : v∈A) (vh : v∈high (patch G ∅)) (same : nbr (patch G ∅) v A≤1) :
    trianglesAt G v+1<(high (patch G ∅)).card := by
  classical
  let J := patch G ∅
  let H := high J
  let N := J.neighborFinset v
  let R := N\A
  let L := N∩A
  let B := H∩Aᶜ
  have num : L.card=nbr J v A := by
    change (N∩A).card=(A.filter (J.Adj v)).card
    congr 1; ext; simp [N,and_comm]
  have across : R.card=nbr J v Aᶜ := by
    change (N\A).card=(Aᶜ.filter (J.Adj v)).card
    congr 1; ext; simp [N,and_comm]
  have inc : R⊆B := fun w wm => mem_inter.mpr
    ⟨OddStars.ShoreCounts.in_high G bad size ((J.mem_neighborFinset ..).mp (mem_sdiff.mp wm).1),mem_compl.mpr (mem_sdiff.mp wm).2⟩
  have portion := card_le_card inc
  have eq := OddStars.LeafCritical.balance_max G bad size (OddStars.LeafCritical.max_compl J m)
  change 2*B.card=H.card at eq
  have six : 6≤H.card := six_high G bad size ⟨v,vh⟩ m
  have two := OddStars.LeafCritical.max_covers J m v vh va
  have pos : R.Nonempty := card_pos.mp (by rw [across]; omega)
  have off : R⊆Aᶜ := fun _ h => mem_compl.mpr (mem_sdiff.mp h).2
  have low := two_centers J e f R pos (fun x xm xe xf => (Repair.nbr_mono J _ off).trans (sparse x (off xm) xe xf))
  have un : L∪R=N := by ext; simp [L,R]; tauto
  have links : trianglesAt G v=(pairs J N).card := (patch_scores G ∅ v).symm
  change trianglesAt G v+1<H.card
  by_contra! rank
  have lc : L.card≤1 := num ▸ same
  by_cases empty : L=∅
  · rw [empty,empty_union] at un
    rw [←un] at links; omega
  have one : L.card=1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega
  obtain ⟨u,lu⟩ := card_eq_one.mp one
  have ul : u∈L := lu ▸ mem_singleton_self _
  obtain ⟨unb,ua⟩ := mem_inter.mp ul
  have vu := (J.mem_neighborFinset ..).mp unb
  have ur : u∉R := fun k => (mem_sdiff.mp k).2 ua
  have si : ({u}:Finset V)∪R=insert u R := by ext; simp
  rw [lu,si] at un
  rw [←un,pairs_insert J ur] at links
  have small : nbr J u R≤R.card := card_filter_le ..
  have Rall : R=B := eq_of_subset_of_card_le inc (by omega)
  have rich : 2≤trianglesAt G v := by omega
  rcases thin with our|their
  · have full : R.filter (J.Adj u)=R := eq_of_subset_of_card_le (filter_subset ..) (by change R.card≤nbr J u R; omega)
    have uN : J.neighborFinset u=insert v R := by
      ext w
      constructor
      · intro wm
        have uw := (J.mem_neighborFinset ..).mp wm
        by_cases wa : w∈A
        · have card := our u ua
          change (A.filter (J.Adj u)).card≤1 at card
          exact mem_insert.mpr (Or.inl (card_le_one.mp card w (mem_filter.mpr ⟨wa,uw⟩) v (mem_filter.mpr ⟨va,vu.symm⟩)))
        · exact mem_insert_of_mem (Rall ▸ mem_inter.mpr ⟨OddStars.ShoreCounts.in_high G bad size uw,mem_compl.mpr wa⟩)
      · intro wm; rcases mem_insert.mp wm with rfl|wr
        · exact (J.mem_neighborFinset ..).mpr vu.symm
        · exact (J.mem_neighborFinset ..).mpr (mem_filter.mp (full ▸ wr)).2
    have vr : v∉R := fun k => (mem_sdiff.mp k).2 va
    have unit : nbr J v R=R.card := by
      unfold nbr
      rw [filter_eq_self.mpr (fun w wm => (J.mem_neighborFinset ..).mp (mem_sdiff.mp wm).1)]
    have compare : trianglesAt G u=(pairs J (J.neighborFinset u)).card := (patch_scores G ∅ u).symm
    rw [uN,pairs_insert J vr,unit] at compare
    exact vu.ne (distinct_rich G bad rich (by omega))
  · have sum := degree_sum J R
    have cap : (∑ x∈R,nbr J x R)≤∑ _x∈R,1 := sum_le_sum (fun x xm => (Repair.nbr_mono J _ off).trans (their x (off xm)))
    have double : 2*(pairs J R).card≤R.card := by rw [←sum]; simpa using cap
    omega

/-- Two possible branching vertices confined to one shore cannot supply all the
distinct positive triangle counts required by equality. -/
theorem forbidden_pair (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    (has : (high (patch G ∅)).Nonempty) {A : Finset V} (m : Maximum (patch G ∅) A)
    (e f : V) (only : ∀x∈active (patch G ∅) A,x=e ∨ x=f)
    (thin : (∀x∈A,nbr (patch G ∅) x A≤1) ∨ (∀x∈Aᶜ,nbr (patch G ∅) x Aᶜ≤1)) : False := by
  classical
  let J := patch G ∅
  let H := high J
  let U := H\{e,f}
  have sides (x : V) (xe : x≠e) (xf : x≠f) : nbr J x (if x∈A then A else Aᶜ)≤1 := by
    by_contra! two
    have up : nbr J x (if x∈A then A else Aᶜ)≤J.degree x := by
      rw [←card_neighborFinset_eq_degree]
      exact card_le_card (fun _ h => (J.mem_neighborFinset ..).mpr (mem_filter.mp h).2)
    have pos := skeleton_degree_bound G x
    change J.degree x≤_ at pos
    have xh := (PendantAudit.upper_branch G bad size).1 x (by omega)
    exact (only x (mem_filter.mpr ⟨xh,two⟩)).elim xe xf
  have ord (x : V) (xm : x∈U) : trianglesAt G x+1<H.card := by
    obtain ⟨xh,off⟩ := mem_sdiff.mp xm
    have ne : x≠e ∧ x≠f := by simpa using off
    by_cases xa : x∈A
    · refine sharp_side G bad size m e f (fun y ym ye yf => by simpa [mem_compl.mp ym] using sides y ye yf)
        thin xa xh ?_
      simpa [xa] using sides x ne.1 ne.2
    · refine sharp_side G bad size (OddStars.LeafCritical.max_compl J m) e f ?_ ?_ (mem_compl.mpr xa) xh ?_
      · intro y ym ye yf; rw [compl_compl] at ym ⊢; simpa [ym] using sides y ye yf
      · rw [compl_compl]; exact thin.symm
      · simpa [xa] using sides x ne.1 ne.2
  have rich {x : V} (xh : x∈H) : 2≤trianglesAt G x := by
    have d : 3≤J.degree x := (mem_filter.mp xh).2
    have l := skeleton_degree_bound G x; change J.degree x≤_ at l; omega
  have inj : Set.InjOn (trianglesAt G) (U : Set V) :=
    fun _ xm _ _ eq => distinct_rich G bad (rich (mem_sdiff.mp xm).1) eq
  let P := ((range (H.card-1)).erase 0).erase 1
  have inc : U.image (trianglesAt G)⊆P := by
    intro k km; obtain ⟨x,xm,rfl⟩ := mem_image.mp km
    have sm := ord x xm; have ge := rich (mem_sdiff.mp xm).1
    exact mem_erase.mpr ⟨by omega,mem_erase.mpr ⟨by omega,mem_range.mpr (by omega)⟩⟩
  have cap := card_le_card inc
  rw [card_image_iff.mpr inj] at cap
  have six : 6≤H.card := six_high G bad size has m
  have z : 0∈range (H.card-1) := mem_range.mpr (by omega)
  have o : 1∈(range (H.card-1)).erase 0 := mem_erase.mpr ⟨by decide,mem_range.mpr (by omega)⟩
  have pc : P.card=H.card-1-1-1 := by dsimp only [P]; rw [card_erase_of_mem o,card_erase_of_mem z,card_range]
  have part : U.card+(H∩{e,f}).card=H.card := card_sdiff_add_card_inter H _
  have sub := card_le_card (inter_subset_right (s₁:=H) (s₂:=({e,f}:Finset V)))
  have two := card_insert_le e ({f}:Finset V)
  rw [card_singleton] at two
  omega

private theorem active_hit (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {x : V} (xm : x∈active (patch G ∅) A) :
    ∃c∈critical (patch G ∅) A,x∈crossed (patch G ∅) A c := by
  let J := patch G ∅
  obtain ⟨xh,two⟩ := mem_filter.mp xm
  by_cases xa : x∈A
  · rw [if_pos xa] at two
    obtain ⟨y,yh,yo,yx,yt⟩ := active_contact_side G bad size m xh xa two
    have yoff := mem_compl.mp yo
    refine ⟨y,mem_filter.mpr ⟨yh,?_⟩,mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr yx,fun e => yoff (e.mpr xa)⟩⟩
    change (OddStars.crossing J A y).card=2
    simpa only [OddStars.translated,if_neg yoff] using yt
  · rw [if_neg xa] at two
    obtain ⟨y,yh,yo,yx,yt⟩ := active_contact_side G bad size (OddStars.LeafCritical.max_compl _ m) xh (mem_compl.mpr xa) two
    rw [compl_compl] at yo
    refine ⟨y,mem_filter.mpr ⟨yh,?_⟩,mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr yx,fun e => xa (e.mp yo)⟩⟩
    change (OddStars.crossing J A y).card=2
    simpa only [OddStars.translated,if_pos yo] using yt

theorem exactly_two_critical (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    (has : (high (patch G ∅)).Nonempty) {A : Finset V} (m : Maximum (patch G ∅) A) :
    (critical (patch G ∅) A).card=2 := by
  classical
  let J := patch G ∅
  have upper := at_most_two_critical G bad size m
  apply le_antisymm upper
  by_contra! small
  change (critical J A).card<2 at small
  have many : 2≤(active J A).card := at_least_two_active G bad size has m
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(active J A).card by omega)
  obtain ⟨c,cm,_⟩ := active_hit G bad size m xm
  have only (u : V) (um : u∈active J A) : u∈crossed J A c := by
    obtain ⟨v,vm,uv⟩ := active_hit G bad size m um
    have eq := card_le_one.mp (by omega : (critical J A).card≤1) v vm c cm
    exact eq ▸ uv
  have cc : (crossed J A c).card=2 := (mem_filter.mp cm).2
  obtain ⟨e,f,_,ef⟩ := card_eq_two.mp cc
  have cover (u : V) (um : u∈active J A) : u=e ∨ u=f := by simpa [ef] using only u um
  refine forbidden_pair G bad size has m e f cover ?_
  have thin (u : V) (same : c∈A ↔ u∈A) : nbr J u (if u∈A then A else Aᶜ)≤1 := by
    apply Nat.le_of_not_gt
    intro large
    have up : nbr J u (if u∈A then A else Aᶜ)≤J.degree u := by
      rw [←card_neighborFinset_eq_degree]
      exact card_le_card (fun _ h => (J.mem_neighborFinset ..).mpr (mem_filter.mp h).2)
    have p := skeleton_degree_bound G u; change J.degree u≤_ at p
    have uh := (PendantAudit.upper_branch G bad size).1 u (by omega)
    exact (mem_filter.mp (only u (mem_filter.mpr ⟨uh,large⟩))).2 same
  by_cases ca : c∈A
  · exact Or.inl (fun u ua => by simpa [ua] using thin u (iff_of_true ca ua))
  · exact Or.inr (fun u uo => by have ua := mem_compl.mp uo; simpa [ua] using thin u (iff_of_false ca ua))

end Graffiti384b.OddStars.ShoreRanks

#print axioms Graffiti384b.OddStars.ShoreRanks.two_centers
#print axioms Graffiti384b.OddStars.ShoreRanks.forbidden_pair
#print axioms Graffiti384b.OddStars.ShoreRanks.exactly_two_critical
