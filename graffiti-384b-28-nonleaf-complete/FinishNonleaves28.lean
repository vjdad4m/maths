import DisjointFinish28
import FiveCommonSaving28

namespace Graffiti384b.TwentyEight
open Finset SimpleGraph Core28
open private Four28.core_data from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The full catalogue inequality for 29 realized triangle counts and
28 vertices of degree at least two, with no clique or connectivity premise. -/
theorem original_bound (ty : (types G).card=29) (nl : (nonleaves G).card=28) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro fail
  let J := triangleEdges (G.induce (nonleaves G:Set V))
  have five := Sparse28.five_clique_required G ty nl fail
  obtain ⟨u,v,du,su,dv,sv,small,cover⟩ := Core28.original_clique G ty nl fail five
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data G ty nl fail
  change (J.neighborFinset u∩J.neighborFinset v).card≤1 at small
  have sep : ¬J.Adj u v := by
    intro uv
    have two := HighSquare28.adjacent_common J dv sv uv
    exact (by decide : ¬2≤1) (two.trans small)
  have saved : gamma J≤13 := by
    by_cases any : (J.neighborFinset u∩J.neighborFinset v).Nonempty
    · have one := card_pos.mpr any
      obtain ⟨c,hc⟩ := card_eq_one.mp (by omega : (J.neighborFinset u∩J.neighborFinset v).card=1)
      let B : Port28.Board J := ⟨u,v,c,du,su,dv,sv,sep,hc⟩
      exact B.cover_saving n pos fi (fun C cl => (cover C cl).1)
    · have dis := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp any)
      let B : FiveBoard28.Board J := ⟨u,v,du,su,dv,sv,sep,dis⟩
      exact B.saving n pos fi (fun C cl => (cover C cl).1)
  exact (by decide : ¬14≤13) (half.trans saved)

theorem numerical_bound (ty : (types G).card=29) (nl : (nonleaves G).card=28) :
    gamma G≤Fintype.card V-15 := by
  simpa only [bound,ty] using original_bound G ty nl

/-- Combined with the frozen quota reduction, only the two larger nonleaf
counts can occur in a failure at diversity 29. -/
theorem remaining_counts (ty : (types G).card=29) (fail : bound G<gamma G) :
    (nonleaves G).card=29 ∨ (nonleaves G).card=30 := by
  obtain ⟨_,_,_,low,high⟩ := Quota29.residual G ty fail
  have ne : (nonleaves G).card≠28 := fun h => (Nat.not_lt_of_ge (original_bound G ty h)) fail
  omega

end Graffiti384b.TwentyEight
#print axioms Graffiti384b.TwentyEight.original_bound
#print axioms Graffiti384b.TwentyEight.numerical_bound
#print axioms Graffiti384b.TwentyEight.remaining_counts
