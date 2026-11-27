import FourEar28
import FourQuartic28
namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar Core28
open private OneEar.trim_scores from OneEarFinish384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem core_data (t : (types G).card=29) (q : (nonleaves G).card=28) (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let J := triangleEdges H
    Fintype.card P=28 ∧ (∀ v,0<trianglesAt J v) ∧ Function.Injective (trianglesAt J) ∧
    14≤gamma J ∧ ∀ v w,J.Adj v w → ∃ z,J.Adj v z ∧ J.Adj w z := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let J := triangleEdges H
  have nc : Fintype.card P=28 := (Fintype.card_coe _).trans q
  obtain ⟨pos,fi,eq,_⟩ := Quota29.minimum G t q bad
  have hf : Fintype.card P≤2*gamma H := by rw [nc,show gamma H=14 from eq]
  have eq' := (Core28.profile H nc pos fi hf).2.1
  have score (v : P) : trianglesAt J v=trianglesAt H v := OneEar.trim_scores H v
  refine ⟨nc,fun v => (score v) ▸ pos v,fun a b h => fi ((score a).symm.trans (h.trans (score b))),eq'.ge,?_⟩
  intro v w vw
  obtain ⟨ed,h⟩ := vw
  rcases h with ⟨z,vz,wz⟩|a|b
  · exact ⟨z,⟨vz,Or.inl ⟨w,ed,wz.symm⟩⟩,⟨wz,Or.inl ⟨v,ed.symm,vz.symm⟩⟩⟩
  · exact ((pos v).ne' a).elim
  · exact ((pos w).ne' b).elim

private theorem ear_one {e p q : V} (pq : p≠q) (en : G.neighborFinset e={p,q})
    (pos : ∀ v,0<trianglesAt G v) : trianglesAt G e=1 := by
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair pq]
  have cap := Repair.triangles_le_choose G e; rw [de,Nat.choose_self] at cap
  have := pos e; omega

/-- The catalogue bound holds with a low fourth vertex of one of the four
listed kinds. All degrees and scores in the premise are measured in J. -/
theorem exact_low_square (t : (types G).card=29) (q : (nonleaves G).card=28) :
    let H := G.induce (nonleaves G:Set V)
    let J := triangleEdges H
    J.CliqueFree 5 → ∀ e a b s,J.Adj a b → J.neighborFinset e={a,b} → s∈additional J e a b →
      (trianglesAt J s=2 ∨ J.degree s=3 ∨ (J.degree s=4 ∧ (trianglesAt J s=3 ∨ trianglesAt J s=5))) →
      gamma G≤bound G := by
  dsimp only; intro free e a b s ab en sm profile
  by_contra! bad
  let H := G.induce (nonleaves G:Set V)
  let J := triangleEdges H
  obtain ⟨n,pos,fi,half,sup⟩ := core_data G t q bad
  obtain ⟨se,as',bs⟩ := (additional_mem J).mp sm
  have low := low_square J n ab en se.symm as'.symm bs.symm (ear_one J ab.ne en pos) pos fi free (sup s) profile
  exact (Nat.not_succ_le_self 13) (half.trans low)

/-- If a failure has a degree-four fourth vertex, its link forces another
fourth vertex and the fan has two external cubic blockers of scores two and three. -/
theorem quartic_frontier (t : (types G).card=29) (q : (nonleaves G).card=28) (bad : bound G<gamma G) :
    let H := G.induce (nonleaves G:Set V)
    let J := triangleEdges H
    J.CliqueFree 5 → ∀ e a b s,J.Adj a b → J.neighborFinset e={a,b} → s∈additional J e a b → J.degree s=4 →
      (trianglesAt J s=4 ∧ ∃ x y,leaks J s a b={x} ∧ J.neighborFinset s={a,b,x,y} ∧
        J.Adj x y ∧ y∈additional J e a b ∧ y≠s) ∧
      ∃ T Y,Fan J T Y ∧ Disjoint (T∪Y) {e,a,b} ∧ ∃ u v,
        u∉T∪Y∪{e,a,b} ∧ v∉T∪Y∪{e,a,b} ∧ J.degree u=3 ∧ J.degree v=3 ∧
        trianglesAt J u=2 ∧ trianglesAt J v=3 := by
  dsimp only; intro free e a b s ab en sm ds
  let H := G.induce (nonleaves G:Set V)
  let J := triangleEdges H
  obtain ⟨n,pos,fi,half,sup⟩ := core_data G t q bad
  obtain ⟨se,as',bs⟩ := (additional_mem J).mp sm
  have one := ear_one J ab.ne en pos
  have layout := quartic_link J n ab en se.symm as'.symm bs.symm one pos fi free half (sup s) ds
  refine ⟨layout,?_⟩
  obtain ⟨_,x,y,_,_,_,ym,ys⟩ := layout
  have two := card_le_card (insert_subset sm (singleton_subset_iff.mpr ym))
  rw [card_pair ys.symm] at two
  exact two_blockers J n pos fi free half ab.ne one en two

theorem exact_lone_quartic (t : (types G).card=29) (q : (nonleaves G).card=28) :
    let H := G.induce (nonleaves G:Set V)
    let J := triangleEdges H
    J.CliqueFree 5 → ∀ e a b s,J.Adj a b → J.neighborFinset e={a,b} →
      additional J e a b={s} → J.degree s=4 → gamma G≤bound G := by
  dsimp only; intro free e a b s ab en only ds
  by_contra! bad
  have v := quartic_frontier G t q bad free e a b s ab en (only ▸ mem_singleton_self _) ds
  obtain ⟨_,_,y,_,_,_,ym,ys⟩ := v.1
  exact ys (mem_singleton.mp (only ▸ ym))

/-- Any specified vertex can be avoided by an induced five-vertex fan. -/
theorem original_fan (t : (types G).card=29) (q : (nonleaves G).card=28) (bad : bound G<gamma G) :
    let H := G.induce (nonleaves G:Set V)
    let J := triangleEdges H
    J.CliqueFree 5 → ∀ a,∃ v∈remote J {a} 9,∃ T Y,Fan J T Y ∧ v∈T ∧ a∉T∪Y := by
  dsimp only; intro free a
  let H := G.induce (nonleaves G:Set V)
  let J := triangleEdges H
  obtain ⟨n,pos,fi,half,_⟩ := core_data G t q bad
  obtain ⟨v,m,T,Y,f,vt,_,dis⟩ := forced_fan J n pos fi free half {a} (by simp)
    (by simp)
  exact ⟨v,m,T,Y,f,vt,fun hn => disjoint_left.mp dis hn (mem_singleton_self _)⟩

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.exact_low_square
#print axioms Graffiti384b.Four28.quartic_frontier
#print axioms Graffiti384b.Four28.exact_lone_quartic
#print axioms Graffiti384b.Four28.original_fan
