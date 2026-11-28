import EarSwitch
namespace Graffiti384b.QuarticSwitch
open Finset SimpleGraph RichRoot
open private QuarticSwitch.hits_two from EarSwitch
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All switches based at a common quartic must be blocked by the very same
remote vertex in a failure. Its entire degree budget is four. -/
theorem one_blocker {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (high : ∀x∈exchangePool G r e b,4≤G.degree x)
    (vm : v∈common G r e b) (low : G.degree v≤4) (two : 2≤(common G r e b).card)
    (bad : bound G<gamma G) : ∃x∈remoteLow G r b v,common G r e b⊆G.neighborFinset x := by
  obtain ⟨w,wm,wv⟩ := exists_ne_of_one_lt_card two v
  obtain ⟨x,xm,_⟩ := remote_for_pair G h high vm wm wv.symm bad
  have atMost := card_le_one.mp (remote_unique G h few vm low)
  refine ⟨x,xm,?_⟩
  intro u um
  by_cases uv : u=v
  · have adj := (G.mem_neighborFinset ..).mp (mem_filter.mp xm).1
    exact uv ▸ (G.mem_neighborFinset ..).mpr adj.symm
  · obtain ⟨y,ym,yu⟩ := remote_for_pair G h high vm um (Ne.symm uv) bad
    exact (atMost y ym x xm) ▸ (G.mem_neighborFinset ..).mpr yu

/-- Five common neighbors besides the ear eliminate a common quartic
without any leaf attachment or density assumption on the mate. -/
theorem five_common_quartic {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (high : ∀x∈exchangePool G r e b,4≤G.degree x)
    (vm : v∈common G r e b) (low : G.degree v≤4) (five : 5≤(common G r e b).card) : gamma G≤bound G := by
  by_contra! bad
  obtain ⟨x,xm,inc⟩ := one_blocker G h few high vm low (by omega) bad
  have le := card_le_card inc
  rw [card_neighborFinset_eq_degree] at le
  have four := (mem_filter.mp xm).2.2.2
  omega

/-- The previous dense-mate theorem can allow exterior degree four throughout
when the ear anchors have at least five other common neighbors. -/
theorem dense_mate_four {r e b z : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (rz : G.Adj r z) (leaf : G.degree z=1)
    (high : ∀x∈exchangePool G r e b,4≤G.degree x) (five : 5≤(common G r e b).card)
    (density : let S := exchangePool G r e b; let T := S.filter (G.Adj b)
      (S.card+1)/2<T.card ∨ ∃v∈T,nbr G v (S\T)<nbr G v T) : gamma G≤bound G := by
  by_contra! bad
  obtain ⟨rm,em,bm⟩ := Ear.members G h
  obtain ⟨v,vm,weak,low⟩ := low_degree_obstruction G rm em bm rz leaf h.re h.be h.rb.ne.symm density bad
  have four := high v vm
  have contacts := QuarticSwitch.hits_two G h.rb.ne (by omega : 2≤nbr G v {r,b})
  exact (not_lt_of_ge (five_common_quartic G h few high (mem_filter.mpr ⟨vm,contacts⟩) low five)) bad

end Graffiti384b.QuarticSwitch
#print axioms Graffiti384b.QuarticSwitch.one_blocker
#print axioms Graffiti384b.QuarticSwitch.five_common_quartic
#print axioms Graffiti384b.QuarticSwitch.dense_mate_four
