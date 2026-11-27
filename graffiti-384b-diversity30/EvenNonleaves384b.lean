import OneEarFinish384b

namespace Graffiti384b.EvenQuota
open Finset SimpleGraph
open private Prune.outside_zero from Prune384b
open private OneEar.deg2 from OneEarFinish384b
open private TrianglePrune.triangle_iff TrianglePrune.induced_cost from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A bound on an induced graph lifts whenever it makes at least as
many omissions as the original graph requires. -/
theorem lift {S : Finset V} (quota :
    ((types G).card+1)/2≤((types (G.induce (S:Set V))).card+1)/2)
    (sol : gamma (G.induce (S:Set V))≤bound (G.induce (S:Set V))) :
    gamma G≤bound G := by
  let H := G.induce (S:Set V)
  have cap : (types H).card≤S.card := by
    simpa only [types,card_univ,Fintype.card_coe] using
      (card_image_le (s:=(univ:Finset S)) (f:=trianglesAt H))
  have cost := TrianglePrune.induced_cost G S
  have up := Capacity.seeded_value G ∅ S ∅ (by simp) (by simp) (by simp) (by simp)
  simp only [card_empty,zero_add] at up
  change S.card≤gamma H+_ at cost
  change gamma H≤Fintype.card S-((types H).card+1)/2 at sol
  rw [Fintype.card_coe] at sol
  change ((types G).card+1)/2≤((types H).card+1)/2 at quota
  unfold bound
  omega

/-- At every even diversity, fewer nonleaves than triangle-count types
suffice for the catalogue inequality, at any order. -/
theorem exact_of_fewer_nonleaves (par : (types G).card%2=0)
    (few : (nonleaves G).card<(types G).card) : gamma G≤bound G := by
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
  have eq : I.card=P.card := by omega
  have unique : Set.InjOn (trianglesAt G) (P:Set V) := card_image_iff.mp eq
  have positive (v : P) : 0<trianglesAt G v.val := by
    by_contra! z
    have inside : 0∈I := (show trianglesAt G v.val=0 by omega) ▸ mem_image_of_mem (trianglesAt G) v.property
    rw [insert_eq_of_mem inside] at low
    omega
  have same (v : P) : trianglesAt H v=trianglesAt G v.val := Prune.counts_preserved G P Subset.rfl v
  have pos (v : P) : 0<trianglesAt H v := (same v) ▸ positive v
  have fi : Function.Injective (trianglesAt H) := fun v w e => Subtype.ext
    (unique v.property w.property ((same v).symm.trans (e.trans (same w))))
  have allNon : nonleaves H=univ := eq_univ_of_forall (fun v => by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 H ab.ne va vb⟩)
  have count : (types H).card=P.card := by
    change (univ.image (trianglesAt H)).card=_
    rw [card_image_of_injective _ fi,card_univ]
    exact Fintype.card_coe P
  have sol := OneEar.unique_one H (by rw [allNon]; exact card_image_le) (fun v _ => pos v)
    (fun v w _ _ vz wz => fi (vz.trans wz.symm)) (fun v w vo wo => fi (vo.trans wo.symm))
  apply lift G (S:=P) ?_ sol
  change ((types G).card+1)/2≤((types H).card+1)/2
  omega

end Graffiti384b.EvenQuota
#print axioms Graffiti384b.EvenQuota.lift
#print axioms Graffiti384b.EvenQuota.exact_of_fewer_nonleaves
