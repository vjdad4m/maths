import RankBudgetTypes28
import EvenNonleaves384b

namespace Graffiti384b.Types28
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The catalogue inequality throughout the 28-type band, also for
disconnected graphs and regardless of the number of nonleaves. -/
theorem original_bound (t : (types G).card=28) : gamma G≤bound G := by
  classical
  by_cases few : (nonleaves G).card<(types G).card
  · exact EvenQuota.exact_of_fewer_nonleaves G (by rw [t]) few
  apply Nat.le_of_not_gt
  intro fail
  have ub := type_bound G
  have missed : ((high G).card+1)/2<((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun ge => (not_lt_of_ge (exact_of_high G ge)) fail)
  have hs : (high G).card=26 := by omega
  have sub : high G⊆nonleaves G := fun _ m => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp m).2; omega⟩
  have count : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have full {e : V} (em : e∈twos G) : contacts G e=G.neighborFinset e := by
    have inc : contacts G e⊆G.neighborFinset e := fun _ xm => (G.mem_neighborFinset ..).mpr (mem_filter.mp xm).2
    apply eq_of_subset_of_card_le inc
    rw [card_neighborFinset_eq_degree,LowSample.two_degree G em]
    by_contra! small
    have one := budget G t hs fail (E:={e}) (singleton_subset_iff.mpr em) (by
      intro x xs y ys; rw [mem_singleton.mp xs,mem_singleton.mp ys]; exact G.loopless _)
    simp only [sum_singleton] at one
    have cases : (contacts G e).card=0 ∨ (contacts G e).card=1 := by omega
    rcases cases with z|z <;> rw [z] at one
    · change 5311735+_≤1946772 at one; omega
    · change 2042975+_≤1946772 at one; omega
  have independent {e f : V} (em : e∈twos G) (fm : f∈twos G) : ¬G.Adj e f := by
    intro edge
    have hi : f∈contacts G e := (full em).symm ▸ (G.mem_neighborFinset ..).mpr edge
    exact (mem_sdiff.mp fm).2 (mem_filter.mp hi).1
  obtain ⟨e,em,f,fm,ne⟩ := one_lt_card.mp (by omega : 1<(twos G).card)
  let E : Finset V := {e,f}
  have es : E⊆twos G := insert_subset em (singleton_subset_iff.mpr fm)
  have ind : ∀x∈E,∀y∈E,¬G.Adj x y := fun _ xm _ ym => independent (es xm) (es ym)
  have ct : E.card=2 := card_pair ne
  let R := (high G).filter (fun w => ∃v∈E,G.Adj v w)
  have many : 3≤R.card := by
    by_contra! small
    have win := Repair.exact_of_low_support G E (disjoint_left.mpr (fun _ m => (mem_sdiff.mp (es m)).2))
      (fun x xm => (LowSample.two_degree G (es xm)).ge) ind (by
        change (types G).card+R.card≤(high G).card+2*E.card; omega)
    exact (not_lt_of_ge win) fail
  have support : R⊆exposed G := by
    intro w wm; obtain ⟨wh,x,xm,xw⟩ := mem_filter.mp wm
    exact mem_filter.mpr ⟨wh,x,es xm,xw.symm⟩
  have three := many.trans (card_le_card support)
  have two (x : V) (xm : x∈E) : (contacts G x).card=2 := by
    rw [full (es xm),card_neighborFinset_eq_degree,LowSample.two_degree G (es xm)]
  have earnings : (∑ x∈E,(26-(contacts G x).card).choose (10-(contacts G x).card))=1470942 := by
    calc _=∑_x∈E,(24:ℕ).choose 8 := sum_congr rfl (fun x xm => by rw [two x xm])
         _=_ := by rw [sum_const,ct]; decide
  have necessary := budget G t hs fail es ind
  rw [earnings] at necessary
  omega

theorem numerical_bound (t : (types G).card=28) : gamma G≤Fintype.card V-14 := by
  simpa only [bound,t] using original_bound G t

theorem exists_set (t : (types G).card=28) :
    ∃ D : Finset V,TwoDominates G D ∧ D.card+14≤Fintype.card V := by
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem (show {k : ℕ | ∃ d,TwoDominates G d ∧ d.card=k}.Nonempty from
    ⟨_,univ,fun _ out => (out (mem_univ _)).elim,rfl⟩)
  have n : (types G).card≤Fintype.card V := (card_image_le (s:=(univ:Finset V)) (f:=trianglesAt G)).trans_eq card_univ
  change D.card=gamma G at sz
  have sol := numerical_bound G t
  exact ⟨D,dom,by omega⟩
end Graffiti384b.Types28
#print axioms Graffiti384b.Types28.original_bound
#print axioms Graffiti384b.Types28.numerical_bound
#print axioms Graffiti384b.Types28.exists_set
