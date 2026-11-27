import FourFrontier28

namespace Graffiti384b.Thin28
open Finset SimpleGraph
open private Repair.nbr_mono from Repair384b
open private EarAnchor.mask EarAnchor.masked from AnchorCut33
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def misses (P k : Finset V) := (P∪k)ᶜ.filter (fun v => nbr H v (P∪k)<2)
def hit (W P : Finset V) (b : ℕ) (v : V) :=
  ((W.powersetCard b).filter (fun k => v∈misses H P k)).card

theorem budget (W P : Finset V) (b : ℕ) :
    W.card.choose b*(gamma H-P.card-b)≤∑ v,hit H W P b v := by
  classical
  have per (k : Finset V) (km : k∈W.powersetCard b) : gamma H-P.card-b≤(misses H P k).card := by
    let D := (P∪k)∪misses H P k
    have dom : TwoDominates H D := by
      intro v off
      have notBase : v∉P∪k := fun h => off (mem_union_left _ h)
      have good : 2≤nbr H v (P∪k) := Nat.le_of_not_gt (fun h =>
        off (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr notBase,h⟩)))
      exact good.trans (Repair.nbr_mono H v subset_union_left)
    have up : gamma H≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    have sz : D.card≤(P∪k).card+(misses H P k).card := card_union_le .. 
    have first := card_union_le P k
    have kb := (mem_powersetCard.mp km).2
    omega
  have all := sum_le_sum per
  have mass : (∑ k∈W.powersetCard b,(misses H P k).card)=∑ v,hit H W P b v := by
    calc _ = ∑ k∈W.powersetCard b,∑ v,if v∈misses H P k then 1 else 0 := by simp
         _ = _ := by rw [sum_comm]; simp [hit,sum_boole]
  simpa [mass,card_powersetCard] using all

theorem kept {W P : Finset V} {b : ℕ} {v : V} (vp : v∈P) : hit H W P b v=0 :=
  card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun k _ h =>
    mem_compl.mp (mem_filter.mp h).1 (mem_union_left k vp)))

theorem covered {W P : Finset V} {b : ℕ} {v p q : V}
    (pq : p≠q) (vp : H.Adj v p) (vq : H.Adj v q) (pp : p∈P) (qp : q∈P) :
    hit H W P b v=0 :=
  card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun k _ h =>
    (Nat.not_lt_of_ge (PinnedColor34.two H pq vp vq (mem_union_left k pp) (mem_union_left k qp)))
      (mem_filter.mp h).2))

theorem plain {W P : Finset V} {b : ℕ} {v : V} (vw : v∈W) :
    hit H W P b v≤FiniteRange.badCount W.card b (nbr H v W) := by
  classical
  let J := EarAnchor.mask H W
  have d : J.degree v=nbr H v W := by
    rw [←card_neighborFinset_eq_degree]
    congr 1
    ext z; simp [J,nbr,EarAnchor.mask,vw]
  have lt : nbr H v W<W.card := by
    have sub : W.filter (H.Adj v)⊆W.erase v := by
      intro z zm; exact mem_erase.mpr ⟨(mem_filter.mp zm).2.ne.symm,(mem_filter.mp zm).1⟩
    have h := card_le_card sub
    rw [card_erase_of_mem vw] at h
    have pos := card_pos.mpr ⟨v,vw⟩
    change nbr H v W≤_ at h
    omega
  apply (card_le_card ?_).trans (FiniteRange.count_bad J W b (nbr H v W) v vw d.ge lt)
  intro k km
  obtain ⟨ks,fail⟩ := mem_filter.mp km
  obtain ⟨off,low⟩ := mem_filter.mp fail
  have kw := (mem_powersetCard.mp ks).1
  have inter : W∩(Wᶜ∪k)=k := by
    ext z; simp only [mem_inter,mem_union,mem_compl]; constructor
    · rintro ⟨a,h⟩; exact h.resolve_left (not_not.mpr a)
    · intro h; exact ⟨kw h,Or.inr h⟩
  have out := mem_compl.mp off
  refine mem_filter.mpr ⟨ks,mem_filter.mpr ⟨mem_sdiff.mpr ⟨vw,fun h => out (mem_union_right _ h)⟩,?_⟩⟩
  change nbr (EarAnchor.mask H W) v (Wᶜ∪k)<2
  rw [EarAnchor.masked H vw,inter]
  exact (Repair.nbr_mono H v (show k⊆P∪k from subset_union_right)).trans_lt low

theorem credited {W P : Finset V} {b : ℕ} {v z : V} (zp : z∈P) (zw : z∉W) (vz : H.Adj v z) :
    hit H W P b v≤(W.card-(if v∈W then 1 else 0)-nbr H v W).choose b := by
  classical
  let A := W.filter (H.Adj v)
  have sub : A⊆W.erase v := by
    intro w wm; exact mem_erase.mpr ⟨(mem_filter.mp wm).2.ne.symm,(mem_filter.mp wm).1⟩
  have sz : (W.erase v).card=W.card-(if v∈W then 1 else 0) := by
    by_cases vm : v∈W <;> simp [vm,card_erase_of_mem,erase_eq_of_not_mem]
  have inc : (W.powersetCard b).filter (fun k => v∈misses H P k)⊆(W.erase v\A).powersetCard b := by
    intro k km
    obtain ⟨opt,fail⟩ := mem_filter.mp km
    obtain ⟨off,low⟩ := mem_filter.mp fail
    obtain ⟨kw,kb⟩ := mem_powersetCard.mp opt
    apply mem_powersetCard.mpr ⟨?_,kb⟩
    intro w wk
    refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun h => mem_compl.mp off (mem_union_right _ (h ▸ wk)),kw wk⟩,?_⟩
    intro wa
    have two := PinnedColor34.two H (fun h : w=z => zw (h ▸ kw wk))
      (mem_filter.mp wa).2 vz (mem_union_right P wk) (mem_union_left k zp)
    omega
  have lim := card_le_card inc
  rwa [card_powersetCard,card_sdiff sub,sz] at lim

end Graffiti384b.Thin28
#print axioms Graffiti384b.Thin28.budget
#print axioms Graffiti384b.Thin28.kept
#print axioms Graffiti384b.Thin28.covered
#print axioms Graffiti384b.Thin28.plain
#print axioms Graffiti384b.Thin28.credited
