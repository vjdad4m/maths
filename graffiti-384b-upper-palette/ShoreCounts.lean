import LeafExposure
import ShorePairs

namespace Graffiti384b.OddStars.ShoreCounts
open Finset SimpleGraph LeafCritical ShorePairs
open private OddStars.LeafCritical.balance_max OddStars.LeafCritical.max_compl OddStars.LeafCritical.max_covers from LeafCritical
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set where all but one vertex have at most one neighbor has fewer
internal edges than vertices whenever nonempty. -/
theorem sparse_pairs (e : V) (R : Finset V) (pos : R.Nonempty)
    (deg : ∀x∈R,x≠e → nbr G x R≤1) : (pairs G R).card<R.card := by
  classical
  induction R using Finset.strongInduction with
  | H S ih =>
    by_cases one : S.card=1
    · have off : S.powersetCard 2=∅ := powersetCard_eq_empty.mpr (by omega)
      simp [pairs,off,one]
    have large : 1<S.card := by have := card_pos.mpr pos; omega
    obtain ⟨x,xm,xe⟩ := exists_ne_of_one_lt_card large e
    let U := S.erase x
    have ucard : U.card+1=S.card := card_erase_add_one xm
    have nonempty : U.Nonempty := card_pos.mp (by omega)
    have sub : U⊆S := erase_subset ..
    have cost := ih U (erase_ssubset xm) nonempty (fun y ym ey =>
      (Repair.nbr_mono G _ sub).trans (deg y (sub ym) ey))
    have capped := (Repair.nbr_mono G x sub).trans (deg x xm xe)
    have step := pairs_insert G (not_mem_erase x S)
    rw [insert_erase xm] at step
    change (pairs G S).card=(pairs G U).card+nbr G x U at step
    omega

private theorem in_high (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {x y : V} (edge : (patch G ∅).Adj x y) : y∈high (patch G ∅) := by
  have d := ((patch G ∅).degree_pos_iff_exists_adj y).mpr ⟨x,edge.symm⟩
  have p := skeleton_degree_bound G y
  exact (PendantAudit.upper_branch G bad size).1 y (by omega)

private theorem cap_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) (e : V)
    (sparse : ∀x∈Aᶜ,x≠e → nbr (patch G ∅) x Aᶜ≤1)
    {v : V} (va : v∈A) (vh : v∈high (patch G ∅)) (same : nbr (patch G ∅) v A≤1) :
    trianglesAt G v<(high (patch G ∅)).card := by
  classical
  let J := patch G ∅
  let H := high J
  let N := J.neighborFinset v
  let R := N\A
  let L := N∩A
  have num : L.card=nbr J v A := by
    change (N∩A).card=(A.filter (J.Adj v)).card
    congr 1; ext; simp [N,and_comm]
  have across : R.card=nbr J v Aᶜ := by
    change (N\A).card=(Aᶜ.filter (J.Adj v)).card
    congr 1; ext; simp [N,and_comm]
  have boundR : R⊆H∩Aᶜ := fun w wm => mem_inter.mpr
    ⟨in_high G bad size ((J.mem_neighborFinset ..).mp (mem_sdiff.mp wm).1),mem_compl.mpr (mem_sdiff.mp wm).2⟩
  have portion := card_le_card boundR
  have balanced := OddStars.LeafCritical.balance_max G bad size (OddStars.LeafCritical.max_compl J m)
  change 2*(H∩Aᶜ).card=H.card at balanced
  have two := OddStars.LeafCritical.max_covers J m v vh va
  have pos : R.Nonempty := card_pos.mp (by rw [across]; omega)
  have low := sparse_pairs J e R pos (fun w wm we => (Repair.nbr_mono J _ (fun _ h =>
    mem_compl.mpr (mem_sdiff.mp h).2)).trans (sparse w (mem_compl.mpr (mem_sdiff.mp wm).2) we))
  have un : L∪R=N := by ext; simp [L,R]; tauto
  have links : trianglesAt G v=(pairs J N).card := (patch_scores G ∅ v).symm
  rw [links]
  change (pairs J N).card<H.card
  have lc : L.card≤1 := num ▸ same
  by_cases empty : L=∅
  · rw [empty,empty_union] at un
    rw [←un]; omega
  · have one : L.card=1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega
    obtain ⟨u,lu⟩ := card_eq_one.mp one
    have ul : u∈L := lu ▸ mem_singleton_self _
    have ur : u∉R := fun k => (mem_sdiff.mp k).2 (mem_inter.mp ul).2
    have si : ({u}:Finset V)∪R=insert u R := by ext; simp
    rw [lu,si] at un
    rw [←un,pairs_insert J ur]
    have small : nbr J u R≤R.card := card_filter_le ..
    omega

/-- The triangle-skeleton shore decomposition requires two genuinely branching
same-shore vertices in each maximum cut, counted across the two shores.
The nonempty high-set assumption excludes empty positive palettes. -/
theorem at_least_two_active (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    (nonempty : (high (patch G ∅)).Nonempty) {A : Finset V} (m : Maximum (patch G ∅) A) :
    2≤(active (patch G ∅) A).card := by
  classical
  let J := patch G ∅
  let H := high J
  let W := active J A
  by_contra! little
  change W.card<2 at little
  obtain ⟨e,only⟩ : ∃e : V, ∀u∈W,u=e := by
    by_cases ex : W.Nonempty
    · obtain ⟨e,em⟩ := ex
      exact ⟨e,fun u um => (card_le_one.mp (by omega : W.card≤1)) u um e em⟩
    · obtain ⟨e,_⟩ := nonempty
      exact ⟨e,fun u um => (ex ⟨u,um⟩).elim⟩
  have sides (x : V) (xe : x≠e) : nbr J x (if x∈A then A else Aᶜ)≤1 := by
    by_contra! two
    have up : nbr J x (if x∈A then A else Aᶜ)≤J.degree x := by
      rw [←card_neighborFinset_eq_degree]
      exact card_le_card (fun _ h => (J.mem_neighborFinset ..).mpr (mem_filter.mp h).2)
    have pos := skeleton_degree_bound G x
    change J.degree x≤2*trianglesAt G x at pos
    have xh := (PendantAudit.upper_branch G bad size).1 x (by omega)
    exact xe (only x (mem_filter.mpr ⟨xh,two⟩))
  have ordinary (x : V) (xh : x∈H) (xe : x≠e) : trianglesAt G x<H.card := by
    by_cases xa : x∈A
    · apply cap_side G bad size m e (fun y ym ye => by simpa [mem_compl.mp ym] using sides y ye) xa xh
      simpa [xa] using sides x xe
    · refine cap_side G bad size (OddStars.LeafCritical.max_compl J m) e ?_ (mem_compl.mpr xa) xh ?_
      · intro y ym ye; rw [compl_compl] at ym ⊢; simpa [ym] using sides y ye
      · simpa [xa] using sides x xe
  have rich {x : V} (xh : x∈H) : 2≤trianglesAt G x := by
    have dg : 3≤J.degree x := (mem_filter.mp xh).2
    have b := skeleton_degree_bound G x
    change J.degree x≤_ at b
    omega
  have inj : Set.InjOn (trianglesAt G) (H.erase e : Set V) :=
    fun _ xm _ _ eq => distinct_rich G bad (rich (mem_of_mem_erase xm)) eq
  let P := ((range H.card).erase 0).erase 1
  have inc : (H.erase e).image (trianglesAt G)⊆P := by
    intro k km; obtain ⟨u,um,rfl⟩ := mem_image.mp km
    obtain ⟨ue,uh⟩ := mem_erase.mp um
    have lo := rich uh
    exact mem_erase.mpr ⟨by omega,mem_erase.mpr ⟨by omega,mem_range.mpr (ordinary u uh ue)⟩⟩
  have cap := card_le_card inc
  rw [card_image_iff.mpr inj] at cap
  have b := OddStars.LeafCritical.balance_max G bad size m
  change 2*(H∩A).card=H.card at b
  have pos : 0<H.card := card_pos.mpr nonempty
  have one : 1<H.card := by omega
  have z : 0∈range H.card := mem_range.mpr pos
  have o : 1∈(range H.card).erase 0 := mem_erase.mpr ⟨by decide,mem_range.mpr one⟩
  have pc : P.card=H.card-1-1 := by dsimp only [P]; rw [card_erase_of_mem o,card_erase_of_mem z,card_range]
  by_cases em : e∈H
  · have drop := card_erase_add_one em; omega
  · rw [erase_eq_of_not_mem em] at cap; omega

end Graffiti384b.OddStars.ShoreCounts
#print axioms Graffiti384b.OddStars.ShoreCounts.sparse_pairs
#print axioms Graffiti384b.OddStars.ShoreCounts.at_least_two_active
