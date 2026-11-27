import ThinFinish28
import QuarticFinish28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar Core28
open private Repair.triangles_le_choose from Repair384b
open private Four28.core_data Four28.ear_one from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With a single external cubic blocker, all fourth vertices on the ear
squares coincide with its sole missed vertex of the fan's central triangle. -/
theorem surviving_ear (t : (types G).card=29) (q : (nonleaves G).card=28)
    (bad : bound G<gamma G) :
    let J := triangleEdges (G.induce (nonleaves G:Set V))
    J.CliqueFree 5 → ∀ e a b,J.Adj a b → J.neighborFinset e={a,b} →
      (additional J e a b).Nonempty ∧
      (∀ s∈additional J e a b,5≤J.degree s ∧ 3≤trianglesAt J s) ∧
      ∃ T Y,Fan J T Y ∧ Disjoint (T∪Y) {e,a,b} ∧
        let C := univ.filter (fun u => u∉T∪Y∪{e,a,b} ∧ J.degree u=3)
        C.Nonempty ∧
          ((∃ u∈C,trianglesAt J u=2) ∧ (∃ v∈C,trianglesAt J v=3) ∨
            ∃ u s,C={u} ∧ additional J e a b={s} ∧ s∈T ∧ ¬J.Adj u s ∧
              ∀ z∈T,z≠s → J.Adj u z) := by
  classical
  dsimp only
  intro free e a b ab en
  let J := triangleEdges (G.induce (nonleaves G:Set V))
  let A := additional J e a b
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data G t q bad
  have se := Four28.ear_one J ab.ne en pos
  have de : J.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair ab.ne]
  have ne : A.Nonempty := nonempty_iff_ne_empty.mpr (fun h =>
    (Nat.not_lt_of_ge (Thin28.exact_no_ear_square G t q free e a b ab en h)) bad)
  have hard (s : _) (sm : s∈A) : 5≤J.degree s ∧ 3≤trianglesAt J s := by
    have low := exact_low_square G t q free e a b s ab en sm
    have no4 := exact_quartic_square G t q free e a b s ab en sm
    have ns : s≠e := ((additional_mem J).mp sm).1
    have n1 : trianglesAt J s≠1 := fun h => ns (fi (h.trans se.symm))
    have n2 : trianglesAt J s≠2 := fun h => (Nat.not_lt_of_ge (low (Or.inl h))) bad
    have n3 : J.degree s≠3 := fun h => (Nat.not_lt_of_ge (low (Or.inr (Or.inl h)))) bad
    have n4 : J.degree s≠4 := fun h => (Nat.not_lt_of_ge (no4 h)) bad
    have big : 3≤trianglesAt J s := by have positive : 0<trianglesAt J s := pos s; omega
    have d3 : 3≤J.degree s := by
      apply Nat.le_of_not_gt; intro h
      have cap := (Repair.triangles_le_choose J s).trans (Nat.choose_le_choose 2 (by omega : J.degree s≤2))
      rw [Nat.choose_self] at cap; omega
    exact ⟨by omega,big⟩
  obtain ⟨T,Y,fan,dis,_,ob⟩ := ear_fan J n pos fi free half ab.ne se en
  let C := univ.filter (fun u => u∉T∪Y∪{e,a,b} ∧ J.degree u=3)
  have hit {s z} (sm : s∈A) (zm : z∈T) (zs : z≠s) :
      ∃ u∈C,J.Adj u z ∧ ∃ x∈T,¬J.Adj u x := by
    obtain ⟨u,ue,_,uT,du,uz,extra⟩ := ob s sm z zm zs
    exact ⟨u,mem_filter.mpr ⟨mem_univ _,fun m => (mem_union.mp m).elim uT ue,du⟩,uz,extra⟩
  obtain ⟨s,sm⟩ := ne
  have size := fan.1.2
  obtain ⟨z,zm,zs⟩ := exists_ne_of_one_lt_card (show 1<T.card by omega) s
  obtain ⟨u,um,_,x,xm,miss⟩ := hit sm zm zs
  refine ⟨⟨s,sm⟩,hard,T,Y,fan,dis,⟨u,um⟩,?_⟩
  by_cases other : ∃ v∈C,v≠u
  · obtain ⟨v,vm,vu⟩ := other
    have su := cubic_scores J de (mem_filter.mp um).2.2 pos fi
    have sv := cubic_scores J de (mem_filter.mp vm).2.2 pos fi
    have diff : trianglesAt J v≠trianglesAt J u := fun h => vu (fi h)
    left
    rcases su with hu|hu <;> rcases sv with hv|hv
    · exact (diff (hv.trans hu.symm)).elim
    · exact ⟨⟨u,um,hu⟩,⟨v,vm,hv⟩⟩
    · exact ⟨⟨v,vm,hv⟩,⟨u,um,hu⟩⟩
    · exact (diff (hv.trans hu.symm)).elim
  · have eq {w} (wm : w∈C) : w=u := Classical.byContradiction (fun h => other ⟨w,wm,h⟩)
    have mEq {v} (vm : v∈A) : x=v := by
      apply Classical.byContradiction
      intro diff
      obtain ⟨w,wm,wx,_⟩ := hit vm xm diff
      exact miss (eq wm ▸ wx)
    have sing : A={x} := by
      ext v; constructor
      · exact fun vm => mem_singleton.mpr (mEq vm).symm
      · intro vm; rw [mem_singleton.mp vm,mEq sm]; exact sm
    right
    refine ⟨u,x,eq_singleton_iff_unique_mem.mpr ⟨um,fun v vm => eq vm⟩,sing,xm,miss,?_⟩
    intro w wm wx
    obtain ⟨v,vm,vw,_⟩ := hit (show x∈A from sing ▸ mem_singleton_self _) wm wx
    exact eq vm ▸ vw

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.surviving_ear
