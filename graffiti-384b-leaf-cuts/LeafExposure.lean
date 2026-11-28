import LeafCritical
namespace Graffiti384b.OddStars.LeafCritical
open Finset SimpleGraph
open private Repair.omit_set Repair.nbr_mono from Repair384b
open private OddStars.LeafCritical.max_covers OddStars.LeafCritical.max_compl OddStars.LeafCritical.balance_max OddStars.LeafCritical.nbr_erase from LeafCritical
open private OddStars.crossing OddStars.translated from CutAtVertex
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For a high vertex, count every original neighbor outside the opposite
high shore. This includes neighbors attached by unsupported edges and leaves. -/
def exposed (A : Finset V) :=
  let H := high (patch G ∅)
  H.filter (fun x => 2≤nbr G x (if x∈A then (H\A)ᶜ else (H\Aᶜ)ᶜ))

private theorem exposed_side (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) {x : V} (xa : x∈A)
    (two : 2≤nbr G x (high (patch G ∅)\A)ᶜ) :
    ∃y∈high (patch G ∅),y∈Aᶜ ∧ (patch G ∅).Adj y x ∧ nbr (patch G ∅) y A=2 := by
  classical
  let J := patch G ∅
  let H := high J
  let R := H\A
  have nox : x∉R := fun h => (mem_sdiff.mp h).2 xa
  by_contra! no
  have retained : A.erase x⊆(insert x R)ᶜ := by
    intro y ym
    obtain ⟨ne,inside⟩ := mem_erase.mp ym
    exact mem_compl.mpr (fun k => (mem_insert.mp k).elim ne (fun hr => (mem_sdiff.mp hr).2 inside))
  have val := Repair.omit_set G (insert x R) (by
    intro v vm
    rcases mem_insert.mp vm with rfl|vr
    · apply two.trans (card_le_card ?_)
      intro y ym
      obtain ⟨yr,xy⟩ := mem_filter.mp ym
      exact mem_filter.mpr ⟨mem_compl.mpr (fun k => (mem_insert.mp k).elim xy.ne.symm (mem_compl.mp yr)),xy⟩
    · obtain ⟨vh,va⟩ := mem_sdiff.mp vr
      have vo : v∈Aᶜ := mem_compl.mpr va
      have c := OddStars.LeafCritical.max_covers J (OddStars.LeafCritical.max_compl J m) v vh vo
      rw [compl_compl] at c
      have er := OddStars.LeafCritical.nbr_erase J xa v
      have less : 2≤nbr J v (A.erase x) := by
        by_cases yx : J.Adj v x
        · have nn := no v vh vo yx
          change nbr J v A≠2 at nn
          rw [if_pos yx] at er; omega
        · rw [if_neg yx,Nat.add_zero] at er; omega
      apply less.trans (card_le_card ?_)
      intro y ym
      obtain ⟨ya,vy⟩ := mem_filter.mp ym
      exact mem_filter.mpr ⟨retained ya,vy.1⟩)
  rw [card_insert_of_not_mem nox] at val
  have half := OddStars.LeafCritical.balance_max G bad size m
  change 2*(H∩A).card=H.card at half
  have part : R.card+(H∩A).card=H.card := card_sdiff_add_card_inter H A
  change H.card+1=(types G).card at size
  unfold bound at bad
  omega

/-- For every maximum cut of the triangle skeleton in the upper high-count
branch, at most four high vertices have even two original neighbors outside
the opposite high shore. -/
theorem at_most_four_exposed (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card)
    {A : Finset V} (m : Maximum (patch G ∅) A) : (exposed G A).card≤4 := by
  let J := patch G ∅
  let C := critical J A
  have inc : exposed G A⊆C.biUnion (crossed J A) := by
    intro x xm
    have two := (mem_filter.mp xm).2
    by_cases xa : x∈A
    · rw [if_pos xa] at two
      obtain ⟨y,yh,yo,yx,yt⟩ := exposed_side G bad size m xa two
      have yoff := mem_compl.mp yo
      refine mem_biUnion.mpr ⟨y,mem_filter.mpr ⟨yh,?_⟩,mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr yx,?_⟩⟩
      · change (OddStars.crossing J A y).card=2
        simpa only [OddStars.translated,if_neg yoff] using yt
      · exact fun e => yoff (e.mpr xa)
    · rw [if_neg xa] at two
      obtain ⟨y,yh,yo,yx,yt⟩ := exposed_side G bad size (OddStars.LeafCritical.max_compl _ m) (mem_compl.mpr xa) two
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
  omega

end Graffiti384b.OddStars.LeafCritical
#print axioms Graffiti384b.OddStars.LeafCritical.at_most_four_exposed
