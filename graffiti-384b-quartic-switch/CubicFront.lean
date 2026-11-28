import CubicScores
namespace Graffiti384b.QuarticSwitch
open Finset SimpleGraph RichRoot
open private Repair.triangles_le_choose from Repair384b
open private QuarticSwitch.hits_two QuarticSwitch.no_contacts from EarSwitch
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def remoteCubics (r e b : V) := (exchangePool G r e b).filter
  (fun x => ¬G.Adj x r ∧ ¬G.Adj x b ∧ G.degree x=3)

/-- An obstruction to the switch based at a common cubic cannot see that cubic:
if it did, the two vertices would both have triangle count two. -/
theorem cubic_remote_for_pair {r e b v w : V} (h : Ear G r e b)
    (few : (nonleaves G).card<(types G).card) (vm : v∈common G r e b) (dv : G.degree v=3)
    (wm : w∈common G r e b) (vw : v≠w) (bad : bound G<gamma G) :
    ∃x∈remoteCubics G r e b,G.Adj x w ∧ ¬G.Adj x v := by
  obtain ⟨x,xs,xv,xw,weak⟩ := switch_obstruction G h vm wm vw bad
  obtain ⟨vs,vr,vb⟩ := mem_filter.mp vm
  obtain ⟨ws,wr,wb⟩ := mem_filter.mp wm
  have xf := exterior_rich G h few xs
  have vf := exterior_rich G h few vs
  have xr := (mem_erase.mp (mem_erase.mp (mem_erase.mp xs).2).2).1
  have xb := (mem_erase.mp xs).1
  have cap := (card_filter_le ({v,w}:Finset V) (G.Adj x)).trans_eq (card_pair vw)
  change nbr G x {v,w}≤2 at cap
  have no : ¬G.Adj x v := by
    intro ax
    obtain ⟨shape,score⟩ := cubic_score G dv ax.symm vr vb xr xb h.rb
    have one : nbr G x {r,b}=1 := by omega
    have dc : G.degree x=3 := by omega
    obtain ⟨_,aw⟩ := QuarticSwitch.hits_two G vw (by omega : 2≤nbr G x {v,w})
    obtain ⟨a,am⟩ := card_pos.mp (show 0<(({r,b}:Finset V).filter (G.Adj x)).card by
      change 0<nbr G x {r,b}; omega)
    obtain ⟨anchor,xa⟩ := mem_filter.mp am
    have va : G.Adj v a := (mem_insert.mp anchor).elim (fun eq => eq ▸ vr) (fun eq => mem_singleton.mp eq ▸ vb)
    have wa : G.Adj w a := (mem_insert.mp anchor).elim (fun eq => eq ▸ wr) (fun eq => mem_singleton.mp eq ▸ wb)
    have miss : ¬G.Adj w v := by
      intro adj
      have m := (G.mem_neighborFinset ..).mpr adj.symm; rw [shape] at m
      exact (mem_insert.mp m).elim xw.symm (fun m =>
        (mem_insert.mp m).elim wr.ne (fun m => wb.ne (mem_singleton.mp m)))
    have sx := (cubic_score G dc aw ax xa vw.symm wa.ne va).2
    have oneW : nbr G w {v,a}=1 := by simp [nbr,filter_insert,filter_singleton,miss,wa]
    rw [oneW] at sx
    exact xv ((quota_data G few).1 xf.1 vf.1 (by omega))
  have aw : G.Adj x w := by
    by_cases hit : G.Adj x w
    · exact hit
    · have zero : nbr G x {v,w}=0 := by simp [nbr,filter_insert,filter_singleton,no,hit]
      omega
  have one : nbr G x {v,w}=1 := by simp [nbr,filter_insert,filter_singleton,no,aw]
  have rem := QuarticSwitch.no_contacts G (by omega : nbr G x {r,b}=0)
  exact ⟨x,mem_filter.mpr ⟨xs,rem.1,rem.2,by omega⟩,aw,no⟩

theorem remote_cubic_unique {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (vm : v∈common G r e b) (dv : G.degree v=3) : (remoteCubics G r e b).card≤1 := by
  apply card_le_one.mpr
  intro x xm y ym
  obtain ⟨vs,vr,_⟩ := mem_filter.mp vm
  obtain ⟨xs,xr,_,dx⟩ := mem_filter.mp xm
  obtain ⟨ys,yr,_,dy⟩ := mem_filter.mp ym
  have xf := exterior_rich G h few xs
  have yf := exterior_rich G h few ys
  have vf := exterior_rich G h few vs
  have cap {u : V} (du : G.degree u=3) : trianglesAt G u≤3 := by
    have hi := Repair.triangles_le_choose G u; rw [du] at hi; exact hi
  have xc := cap dx; have yc := cap dy; have vc := cap dv
  have inj := (quota_data G few).1
  have nx : trianglesAt G x≠trianglesAt G v := fun eq => xr (inj xf.1 vf.1 eq ▸ vr)
  have ny : trianglesAt G y≠trianglesAt G v := fun eq => yr (inj yf.1 vf.1 eq ▸ vr)
  exact inj xf.1 yf.1 (by omega)

/-- In a failure, one remote cubic must cover every other common neighbor
of the anchors. It cannot be adjacent to the selected common cubic. -/
theorem cubic_blocker {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (vm : v∈common G r e b) (dv : G.degree v=3) (two : 2≤(common G r e b).card)
    (bad : bound G<gamma G) : ∃x∈remoteCubics G r e b,¬G.Adj x v ∧
      (common G r e b).erase v⊆G.neighborFinset x := by
  obtain ⟨w,wm,wv⟩ := exists_ne_of_one_lt_card two v
  obtain ⟨x,xm,_,no⟩ := cubic_remote_for_pair G h few vm dv wm wv.symm bad
  have unique := card_le_one.mp (remote_cubic_unique G h few vm dv)
  refine ⟨x,xm,no,?_⟩
  intro u um
  obtain ⟨uv,uc⟩ := mem_erase.mp um
  obtain ⟨y,ym,yu,_⟩ := cubic_remote_for_pair G h few vm dv uc uv.symm bad
  exact unique y ym x xm ▸ (G.mem_neighborFinset ..).mpr yu

theorem five_common_cubic {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (vm : v∈common G r e b) (dv : G.degree v=3) (five : 5≤(common G r e b).card) : gamma G≤bound G := by
  by_contra! bad
  obtain ⟨x,xm,_,sub⟩ := cubic_blocker G h few vm dv (by omega) bad
  have le := card_le_card sub
  rw [card_neighborFinset_eq_degree,(mem_filter.mp xm).2.2.2] at le
  have eq := card_erase_add_one vm
  omega

end Graffiti384b.QuarticSwitch
#print axioms Graffiti384b.QuarticSwitch.cubic_remote_for_pair
#print axioms Graffiti384b.QuarticSwitch.remote_cubic_unique
#print axioms Graffiti384b.QuarticSwitch.cubic_blocker
#print axioms Graffiti384b.QuarticSwitch.five_common_cubic
