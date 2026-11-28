import FiniteUpper
namespace Graffiti384b.OddStars.SplitShore
open Finset SimpleGraph LeafCritical ShorePairs OriginalPins
open private UpperThirteen.unblocked from UpperThirteen
open private ShoreRanks.active_hit from ShoreRanks
open private ShoreCounts.in_high from ShoreCounts
open private LeafCritical.max_compl LeafCritical.balance_max from LeafCritical
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem local_bound (bad : bound G<gamma G) (one : 1∉types G) {A : Finset V}
    (mx : Maximum (patch G ∅) A) {u v : V} (ua : u∈A) (va : v∉A)
    (classify : ∀w,(patch G ∅).degree w=3 ↔ w=u ∨ w=v)
    (crit : critical (patch G ∅) A={u,v}) {x : V}
    (xh : x∈high (patch G ∅)) (xa : x∈A)
    (off : x∉crossed (patch G ∅) A u∪crossed (patch G ∅) A v) :
    let m := (high (patch G ∅)∩Aᶜ).card
    2*trianglesAt G x+3≤3*m ∨ trianglesAt G x≤m := by
  classical
  let J := patch G ∅
  let H := high J
  let N := J.neighborFinset x
  let R := N\A
  let L := N∩A
  let m := (H∩Aᶜ).card
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have cover {w : V} (act : w∈active J A) : w∈crossed J A u ∨ w∈crossed J A v := by
    obtain ⟨c,cm,hit⟩ := ShoreRanks.active_hit G bad sz mx act
    rw [crit,mem_insert,mem_singleton] at cm
    rcases cm with rfl|rfl
    · exact Or.inl hit
    · exact Or.inr hit
  have small : L.card≤1 := by
    have eq : nbr J x A=L.card := by unfold nbr; congr 1; ext; simp [L,N,and_comm]
    by_contra! big
    have act : x∈active J A := mem_filter.mpr ⟨xh,by rw [if_pos xa,eq]; omega⟩
    exact off (mem_union.mpr (cover act))
  have subR : R⊆H∩Aᶜ := fun _ wm => mem_inter.mpr
    ⟨ShoreCounts.in_high G bad sz ((J.mem_neighborFinset ..).mp (mem_sdiff.mp wm).1),mem_compl.mpr (mem_sdiff.mp wm).2⟩
  have dv : J.degree v=3 := (classify v).mpr (Or.inr rfl)
  have vh : v∈H := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have vmiss : ¬J.Adj v x := fun e => off (mem_union_right _
    (mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr e,fun eq => va (eq.mpr xa)⟩))
  have vout : v∉R := fun h => vmiss (((J.mem_neighborFinset ..).mp (mem_sdiff.mp h).1).symm)
  have more := card_le_card (insert_subset (mem_inter.mpr ⟨vh,mem_compl.mpr va⟩) subR)
  rw [card_insert_of_not_mem vout] at more
  change R.card+1≤m at more
  have parts : R.card+L.card=N.card := card_sdiff_add_card_inter ..
  by_cases see : J.Adj u x
  · right
    have ul : u∈L := mem_inter.mpr ⟨(J.mem_neighborFinset ..).mpr see.symm,ua⟩
    have eqL : L={u} := eq_singleton_iff_unique_mem.mpr ⟨ul,fun y ym => card_le_one.mp small _ ym _ ul⟩
    have whole : N=insert u R := by
      have join := sdiff_union_inter N A
      change R∪L=N at join
      rw [eqL] at join; simpa [union_comm] using join.symm
    have uoff : u∉R := fun h => (mem_sdiff.mp h).2 ua
    have cU : u∈critical J A := crit ▸ mem_insert_self ..
    obtain ⟨i,j,_,pair⟩ := card_eq_two.mp (mem_filter.mp cU).2
    have low (w : V) (wm : w∈R) (wi : w≠i) (wj : w≠j) : nbr J w R≤1 := by
      have wa : w∉A := (mem_sdiff.mp wm).2
      have upper : nbr J w Aᶜ≤1 := by
        apply Nat.le_of_not_gt
        intro many
        have act : w∈active J A := mem_filter.mpr ⟨(mem_inter.mp (subR wm)).1,by simpa [wa] using many⟩
        rcases cover act with c|c
        · rw [pair,mem_insert,mem_singleton] at c; exact c.elim wi wj
        · exact (mem_filter.mp c).2 (iff_of_false va wa)
      exact (Repair.nbr_mono J w (fun _ h => mem_compl.mpr (mem_sdiff.mp h).2)).trans upper
    have pos : R.Nonempty := by
      have d : 3≤N.card := by change 3≤(J.neighborFinset x).card; rw [card_neighborFinset_eq_degree]; exact (mem_filter.mp xh).2
      exact card_pos.mp (by omega)
    have edges := ShoreRanks.two_centers J i j R pos low
    have csub : R.filter (J.Adj u)⊆(J.neighborFinset u).erase x := fun y ym =>
      mem_erase.mpr ⟨fun eq => (mem_sdiff.mp (mem_filter.mp ym).1).2 (eq ▸ xa),(J.mem_neighborFinset ..).mpr (mem_filter.mp ym).2⟩
    have upper := card_le_card csub
    rw [card_erase_of_mem ((J.mem_neighborFinset ..).mpr see),card_neighborFinset_eq_degree,(classify u).mpr (Or.inl rfl)] at upper
    have score : trianglesAt G x=(pairs J N).card := (patch_scores G ∅ x).symm
    rw [whole,pairs_insert J uoff] at score
    change nbr J u R≤3-1 at upper
    change trianglesAt G x≤m
    omega
  · left
    have val := UpperThirteen.unblocked G bad one (x:=x) (fun w d e =>
      ((classify w).mp d).elim (fun h => see (h ▸ e)) (fun h => vmiss (h ▸ e)))
    have dg : 3≤N.card := by change 3≤(J.neighborFinset x).card; rw [card_neighborFinset_eq_degree]; exact (mem_filter.mp xh).2
    rw [←card_neighborFinset_eq_degree] at val
    change 2*trianglesAt G x+3≤3*N.card ∨ N.card=0 at val
    change 2*trianglesAt G x+3≤3*m
    omega

/-- In a missing-one failure a maximum cut separating the two fixed cubics
would have at most six high vertices. -/
theorem split_cap (bad : bound G<gamma G) (one : 1∉types G) {A : Finset V} (mx : Maximum (patch G ∅) A)
    {u v : V} (ua : u∈A) (va : v∉A) (classify : ∀w,(patch G ∅).degree w=3 ↔ w=u ∨ w=v)
    (crit : critical (patch G ∅) A={u,v}) : (high (patch G ∅)).card≤6 := by
  classical
  let J := patch G ∅
  let H := high J
  let Z := crossed J A u∪crossed J A v
  let W := H\Z
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have cU : u∈critical J A := crit ▸ mem_insert_self ..
  have cV : v∈critical J A := crit ▸ mem_insert_of_mem (mem_singleton_self _)
  have cZ := card_union_le (crossed J A u) (crossed J A v)
  rw [(mem_filter.mp cU).2,(mem_filter.mp cV).2] at cZ
  have cap : Z.card≤4 := cZ
  have mx' := LeafCritical.max_compl J mx
  have bal := LeafCritical.balance_max G bad sz mx
  have bal' := LeafCritical.balance_max G bad sz mx'
  let m := H.card/2
  have a : (H∩A).card=m := by change 2*(H∩A).card=H.card at bal; dsimp [m]; omega
  have b : (H∩Aᶜ).card=m := by change 2*(H∩Aᶜ).card=H.card at bal'; dsimp [m]; omega
  have total : H.card=2*m := by change 2*(H∩A).card=H.card at bal; omega
  have opposite (c : V) : crossed J Aᶜ c=crossed J A c := by ext w; simp [crossed]; tauto
  have crit' : critical J Aᶜ={v,u} := by
    rw [show critical J Aᶜ=critical J A by unfold critical; simp_rw [opposite],crit,pair_comm]
  by_contra! large
  change 6<H.card at large
  have inc : W.image (trianglesAt G)⊆Icc 2 ((3*m-3)/2) := by
    intro k km; obtain ⟨x,xm,rfl⟩ := mem_image.mp km
    obtain ⟨xh,off⟩ := mem_sdiff.mp xm
    have d := skeleton_degree_bound G x
    have ge : 3≤J.degree x := (mem_filter.mp xh).2
    change J.degree x≤_ at d
    refine mem_Icc.mpr ⟨by omega,?_⟩
    by_cases xa : x∈A
    · have h := local_bound G bad one mx ua va classify crit xh xa off
      change 2*trianglesAt G x+3≤3*(H∩Aᶜ).card ∨ trianglesAt G x≤(H∩Aᶜ).card at h
      omega
    · have miss : x∉crossed J Aᶜ v∪crossed J Aᶜ u := by rw [opposite,opposite,union_comm]; exact off
      have h := local_bound G bad one mx' (mem_compl.mpr va) (fun h => mem_compl.mp h ua)
        (fun w => (classify w).trans or_comm) crit' xh (mem_compl.mpr xa) miss
      change 2*trianglesAt G x+3≤3*(H∩Aᶜᶜ).card ∨ trianglesAt G x≤(H∩Aᶜᶜ).card at h
      rw [compl_compl] at h; omega
  have inj : Set.InjOn (trianglesAt G) (W:Set V) := by
    intro x xm y _ eq
    have d := skeleton_degree_bound G x
    have ge : 3≤J.degree x := (mem_filter.mp (mem_sdiff.mp xm).1).2
    change J.degree x≤_ at d
    exact distinct_rich G bad (by omega) eq
  have count := card_le_card inc
  rw [card_image_iff.mpr inj,Nat.card_Icc] at count
  have lost := card_le_card (inter_subset_right (s₁:=H) (s₂:=Z))
  have part : W.card+(H∩Z).card=H.card := card_sdiff_add_card_inter ..
  omega
end Graffiti384b.OddStars.SplitShore
#print axioms Graffiti384b.OddStars.SplitShore.split_cap
