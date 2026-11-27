import HighTrial28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph HighEar Four28 EarFrame33
open private Four28.ear_one from FourFrontier28
open private CubicShore.square_frame from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The four frame vertices require no repairs. The ear and its cubic endpoint
have no external contacts, leaving at most one available pin on either side. -/
theorem cubic_endpoint (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (free : H.CliqueFree 5) {e p q s : V}
    (pq : H.Adj p q) (en : H.neighborFinset e={p,q}) (sm : s∈additional H e p q)
    (dp : H.degree p=3) : gamma H≤13 := by
  classical
  obtain ⟨se,ps,qs⟩ := (additional_mem H).mp sm
  have ep : H.Adj e p := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' : H.Adj e q := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have pn : H.neighborFinset p={e,q,s} := by
    symm
    apply eq_of_subset_of_card_le (insert_subset ((H.mem_neighborFinset ..).mpr ep.symm)
      (insert_subset ((H.mem_neighborFinset ..).mpr pq) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr ps))))
    simp [card_neighborFinset_eq_degree,dp,eq'.ne,qs.ne,se.symm]
  have ex : exterior H e p q={s} := by
    ext v; simp only [exterior,pn,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h,no⟩; exact (h.resolve_left (fun z => no (Or.inl z))).resolve_left (fun z => no (Or.inr z))
    · rintro rfl; exact ⟨Or.inr (Or.inr rfl),by simp [se,qs.ne.symm]⟩
  have single : additional H e p q={s} := by
    ext v; constructor
    · intro m; obtain ⟨ve,pv,qv⟩ := (additional_mem H).mp m
      have mem := (H.mem_neighborFinset ..).mpr pv
      rw [pn] at mem
      simpa [ve,qv.ne.symm] using mem
    · intro m; rw [mem_singleton.mp m]; exact sm
  have count := (exact_count H en ep eq' pq).2
  have cap : (pairs H ({s}:Finset V)).card≤0 := (card_filter_le ..).trans (by simp [card_powersetCard])
  change trianglesAt H p=1+(additional H e p q).card+(pairs H (exterior H e p q)).card at count
  rw [single,card_singleton,ex] at count
  have sc : trianglesAt H p=2 := by omega
  let L : Finset V := {e,s}
  let R : Finset V := {p,q}
  let W := (L∪R)ᶜ
  have ls : L.card=2 := card_pair se.symm
  have rs : R.card=2 := card_pair pq.ne
  have fr : Frame H L R := CubicShore.square_frame H ep eq' ps qs se.symm pq.ne
  have ws : W.card=24 := by rw [show W=(L∪R)ᶜ from rfl,card_compl,card_union_of_disjoint fr.1,n,ls,rs]
  have one := Four28.ear_one H pq.ne en pos
  have out (v : V) (vw : v∈W) : v≠e ∧ v≠s ∧ v≠p ∧ v≠q := by
    simpa [W,L,R,not_or,and_assoc] using vw
  have rank (v : V) (vw : v∈W) : 3≤trianglesAt H v := by
    obtain ⟨ve,_,vp,_⟩ := out v vw
    have no1 : trianglesAt H v≠1 := fun h => ve (fi (h.trans one.symm))
    have no2 : trianglesAt H v≠2 := fun h => vp (fi (h.trans sc.symm))
    have := pos v; omega
  apply paired_saving H fr ls rs ws free fi rank
  intro v vw
  obtain ⟨ve,vs,vp,vq⟩ := out v vw
  have ne : ¬H.Adj v e := by
    intro h; have m := (H.mem_neighborFinset ..).mpr h.symm; simp [en,vp,vq] at m
  have np : ¬H.Adj v p := by
    intro h; have m := (H.mem_neighborFinset ..).mpr h.symm; simp [pn,ve,vq,vs] at m
  constructor
  · change ((insert e ({s}:Finset V)).filter (H.Adj v)).card≤1
    rw [filter_insert,if_neg ne]; exact (card_filter_le ..).trans_eq (card_singleton _)
  · change ((insert p ({q}:Finset V)).filter (H.Adj v)).card≤1
    rw [filter_insert,if_neg np]; exact (card_filter_le ..).trans_eq (card_singleton _)

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.cubic_endpoint
