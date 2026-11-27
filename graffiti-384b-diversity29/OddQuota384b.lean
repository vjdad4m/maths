import OneEarFinish384b

namespace Graffiti384b.OddQuota
open Finset SimpleGraph
open private Prune.outside_zero from Prune384b
open private OneEar.deg2 from OneEarFinish384b
open private TrianglePrune.induced_cost TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All vertices of degree below two are forced into a 2-dominating set.
Optimizing omissions on the nonleaves with these forced neighbors is exact. -/
theorem rooted_value :
    gamma G+Capacity.value G (nonleaves G) (nonleaves G)ᶜ=Fintype.card V := by
  classical
  let P := nonleaves G
  obtain ⟨o,good,att⟩ := Capacity.attained G P Pᶜ
  have cap : Capacity.value G P Pᶜ≤Fintype.card V := att ▸ card_le_univ o
  have up := Capacity.seeded_value G ∅ P Pᶜ (by simp) (by simp) disjoint_compl_right (by simp)
  simp only [card_empty,zero_add] at up
  have avail : {k : ℕ | ∃ D, TwoDominates G D ∧ D.card=k}.Nonempty :=
    ⟨_,univ,by simp [TwoDominates],rfl⟩
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem avail
  change D.card=gamma G at sz
  have keep : Dᶜ⊆P := by
    intro v vm
    have inc : D.filter (G.Adj v)⊆G.neighborFinset v := fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    exact (dom v (mem_compl.mp vm)).trans ((card_le_card inc).trans_eq (card_neighborFinset_eq_degree ..))
  have eq : Pᶜ∪(P\Dᶜ)=D := by
    ext v; simp only [mem_union,mem_sdiff,mem_compl,not_not]
    by_cases vm : v∈P
    · simp [vm]
    · have vd : v∈D := Classical.byContradiction (fun h => vm (keep (mem_compl.mpr h)))
      simp [vm,vd]
  have lo := Capacity.le_value G (show Capacity.Feasible G P Pᶜ Dᶜ from
    ⟨keep,fun v vm => by rw [eq]; exact dom v (mem_compl.mp vm)⟩)
  rw [card_compl,sz] at lo
  have dg := card_le_univ D
  change gamma G+Capacity.value G P Pᶜ=_; omega

private theorem positive_half (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G)) :
    2*gamma G≤Fintype.card V := by
  have allN : nonleaves G=univ := eq_univ_of_forall (fun v => by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff G v).mp (pos v)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 G ab.ne va vb⟩)
  have sol := OneEar.unique_one G (by rw [allN]; exact card_image_le) (fun v _ => pos v)
    (fun v w _ _ a b => fi (a.trans b.symm)) (fun v w a b => fi (a.trans b.symm))
  have q : (types G).card=Fintype.card V := (card_image_of_injective _ fi).trans card_univ
  unfold bound at sol
  omega

private theorem core_data (few : (nonleaves G).card<(types G).card) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    (types G).card=P.card+1 ∧ (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let I := P.image (trianglesAt G)
  have cover : types G⊆insert 0 I := by
    intro a am; obtain ⟨v,_,rfl⟩ := mem_image.mp am
    by_cases vp : v∈P
    · exact mem_insert_of_mem (mem_image_of_mem _ vp)
    · exact mem_insert.mpr (Or.inl (Prune.outside_zero G vp))
  have low := card_le_card cover
  have next := card_insert_le 0 I
  have cap : I.card≤P.card := card_image_le
  change P.card<(types G).card at few
  have unique : Set.InjOn (trianglesAt G) (P:Set V) := card_image_iff.mp (show I.card=P.card by omega)
  have same (v : P) : trianglesAt H v=trianglesAt G v.val := Prune.counts_preserved G P Subset.rfl v
  change (types G).card=P.card+1 ∧ (∀ v : P,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H)
  refine ⟨by omega,?_,fun v w e => Subtype.ext (unique v.property w.property ((same v).symm.trans (e.trans (same w))))⟩
  intro v; rw [same]
  by_contra! z
  have m : 0∈I := (show trianglesAt G v.val=0 by omega) ▸ mem_image_of_mem (trianglesAt G) v.property
  rw [insert_eq_of_mem m] at low
  omega

/-- At minimum nonleaf count and odd diversity a failure is equivalent
to equality in the rooted omission optimum. -/
theorem failure_iff (odd : (types G).card%2=1) (few : (nonleaves G).card<(types G).card) :
    bound G<gamma G ↔ 2*Capacity.value G (nonleaves G) (nonleaves G)ᶜ=(nonleaves G).card := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨q,pos,fi⟩ := core_data G few
  change (types G).card=P.card+1 at q
  have half := positive_half H pos fi
  change 2*gamma H≤Fintype.card P at half
  rw [Fintype.card_coe] at half
  have cost := TrianglePrune.induced_cost G P
  change P.card≤gamma H+Capacity.value G P ∅ at cost
  have more := Capacity.mono_kept G (r:=P) (empty_subset Pᶜ)
  have eq := rooted_value G
  change gamma G+Capacity.value G P Pᶜ=_ at eq
  have size := card_le_univ P
  have ts : (types G).card≤Fintype.card V := (card_image_le (s:=(univ:Finset V)) (f:=trianglesAt G)).trans_eq card_univ
  change 2*gamma H≤P.card at half
  unfold bound
  change _ ↔ 2*Capacity.value G P Pᶜ=P.card
  omega

theorem core_of_failure (odd : (types G).card%2=1) (few : (nonleaves G).card<(types G).card)
    (fail : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ 2*gamma H=P.card := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨_,pos,fi⟩ := core_data G few
  have half := positive_half H pos fi
  change 2*gamma H≤Fintype.card P at half
  rw [Fintype.card_coe] at half
  have cost := TrianglePrune.induced_cost G P
  change P.card≤gamma H+Capacity.value G P ∅ at cost
  have more := Capacity.mono_kept G (r:=P) (empty_subset Pᶜ)
  have eq := (failure_iff G odd few).mp fail
  change 2*Capacity.value G P Pᶜ=P.card at eq
  change 2*gamma H≤P.card at half
  change (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ 2*gamma H=P.card
  exact ⟨pos,fi,by omega⟩

end Graffiti384b.OddQuota
#print axioms Graffiti384b.OddQuota.rooted_value
#print axioms Graffiti384b.OddQuota.failure_iff
#print axioms Graffiti384b.OddQuota.core_of_failure
