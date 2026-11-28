import CubicFront
namespace Graffiti384b.QuarticSwitch
open Finset SimpleGraph RichRoot
open private Repair.linkEdges Repair.triangles_le_choose from Repair384b
open private QuarticSwitch.hits_two from EarSwitch
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem exterior_size {r e b v : V} (h : Ear G r e b) (vm : v∈common G r e b) :
    ((G.neighborFinset v)\{r,b}).card+2=G.degree v := by
  have sub : ({r,b}:Finset V)⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr (mem_filter.mp vm).2.1)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr (mem_filter.mp vm).2.2))
  rw [←card_neighborFinset_eq_degree,←card_pair h.rb.ne,card_sdiff_add_card_eq_card sub]

private theorem common_neighbor {r e b v w : V} (h : Ear G r e b) (vm : v∈common G r e b)
    (vw : G.Adj v w) (wr : G.Adj w r) (wb : G.Adj w b) : w∈common G r e b := by
  have en : w≠e := by
    intro eq
    have m := (G.mem_neighborFinset ..).mpr (eq ▸ vw.symm : G.Adj e v)
    rw [h.neighbors] at m
    exact (mem_insert.mp m).elim (mem_filter.mp vm).2.1.ne (fun j => (mem_filter.mp vm).2.2.ne (mem_singleton.mp j))
  exact mem_filter.mpr ⟨mem_erase.mpr ⟨wb.ne,mem_erase.mpr ⟨en,mem_erase.mpr ⟨wr.ne,
    mem_filter.mpr ⟨mem_univ _,PositivePalette.Prerequisites.deg2 G h.rb.ne wr wb⟩⟩⟩⟩,wr,wb⟩

/-- For a common cubic of score three, the necessary second common vertex exists
automatically. A failure then has a remote cubic of score two. -/
theorem simplicial_cubic_needs_two {r e b v : V} (h : Ear G r e b) (few : (nonleaves G).card<(types G).card)
    (vm : v∈common G r e b) (dv : G.degree v=3) (score : trianglesAt G v=3) (bad : bound G<gamma G) :
    ∃x∈remoteCubics G r e b,trianglesAt G x=2 ∧ ¬G.Adj x v ∧ (common G r e b).erase v⊆G.neighborFinset x := by
  have sz := exterior_size G h vm
  obtain ⟨w,wm⟩ := card_pos.mp (by omega : 0<((G.neighborFinset v)\{r,b}).card)
  obtain ⟨wn,off⟩ := mem_sdiff.mp wm
  obtain ⟨vs,vr,vb⟩ := mem_filter.mp vm
  have vw := (G.mem_neighborFinset ..).mp wn
  have eq := (cubic_score G dv vw vr vb (fun j => off (mem_insert.mpr (Or.inl j)))
    (fun j => off (mem_insert_of_mem (mem_singleton.mpr j))) h.rb).2
  obtain ⟨wr,wb⟩ := QuarticSwitch.hits_two G h.rb.ne (by omega : 2≤nbr G w {r,b})
  have wc := common_neighbor G h vm vw wr wb
  have sub := card_le_card (insert_subset vm (singleton_subset_iff.mpr wc))
  rw [card_pair vw.ne] at sub
  obtain ⟨x,xm,no,inc⟩ := cubic_blocker G h few vm dv sub bad
  have xf := exterior_rich G h few (mem_filter.mp xm).1
  have vf := exterior_rich G h few vs
  have cap := Repair.triangles_le_choose G x
  rw [(mem_filter.mp xm).2.2.2,show Nat.choose 3 2=3 by decide] at cap
  have ne : trianglesAt G x≠trianglesAt G v := fun j => (mem_filter.mp xm).2.1 ((quota_data G few).1 xf.1 vf.1 j ▸ vr)
  exact ⟨x,xm,by omega,no,inc⟩

/-- A common quartic of score at least five already supplies a successful switch,
with no lower bound on how many common neighbors the ear anchors have. -/
theorem high_score_quartic {r e b v : V} (h : Ear G r e b)
    (high : ∀x∈exchangePool G r e b,4≤G.degree x) (vm : v∈common G r e b)
    (dv : G.degree v=4) (score : 5≤trianglesAt G v) : gamma G≤bound G := by
  classical
  let N := G.neighborFinset v
  let M := (N.powersetCard 2)\Repair.linkEdges G v
  have lim : M.card≤1 := by
    have sub : Repair.linkEdges G v⊆N.powersetCard 2 := filter_subset .. 
    have eq := card_sdiff_add_card_eq_card sub
    change M.card+trianglesAt G v=(N.powersetCard 2).card at eq
    rw [card_powersetCard,show N.card=4 from (card_neighborFinset_eq_degree ..).trans dv,show Nat.choose 4 2=6 by decide] at eq
    omega
  have miss {i j : V} (im : i∈N) (jm : j∈N) (ij : i≠j) (no : ¬G.Adj i j) :
      ({i,j}:Finset V)∈M := mem_sdiff.mpr ⟨mem_powersetCard.mpr
        ⟨insert_subset im (singleton_subset_iff.mpr jm),card_pair ij⟩,fun p =>
      no ((mem_filter.mp p).2 _ (mem_insert_self ..) _ (mem_insert_of_mem (mem_singleton_self _)) ij)⟩
  obtain ⟨vs,vr,vb⟩ := mem_filter.mp vm
  have rn : r∈N := (G.mem_neighborFinset ..).mpr vr
  have bn : b∈N := (G.mem_neighborFinset ..).mpr vb
  have room := exterior_size G h vm
  let X := N\{r,b}
  have count : X.card=2 := by change X.card+2=G.degree v at room; omega
  obtain ⟨u,w,uw,shape⟩ := card_eq_two.mp count
  have um : u∈X := shape ▸ mem_insert_self ..
  have wm : w∈X := shape ▸ mem_insert_of_mem (mem_singleton_self _)
  have anchor {x : V} (xm : x∈X) (no : x∉common G r e b) :
      ∃a∈({r,b}:Finset V),({x,a}:Finset V)∈M := by
    have xn := (mem_sdiff.mp xm).1
    have out := (mem_sdiff.mp xm).2
    by_cases xr : G.Adj x r
    · have xb : ¬G.Adj x b := fun hit => no (common_neighbor G h vm ((G.mem_neighborFinset ..).mp xn) xr hit)
      exact ⟨b,mem_insert_of_mem (mem_singleton_self _),miss xn bn
        (fun eq => out (mem_insert_of_mem (mem_singleton.mpr eq))) xb⟩
    · exact ⟨r,mem_insert_self ..,miss xn rn (fun eq => out (mem_insert.mpr (Or.inl eq))) xr⟩
  have other : ∃w∈common G r e b,w≠v := by
    apply Classical.byContradiction
    intro denied
    have out {x : V} (xm : x∈X) : x∉common G r e b := fun cm =>
      denied ⟨x,cm,((G.mem_neighborFinset ..).mp (mem_sdiff.mp xm).1).ne.symm⟩
    obtain ⟨a,am,first⟩ := anchor um (out um)
    obtain ⟨c,cm,second⟩ := anchor wm (out wm)
    have eq := card_le_one.mp lim _ first _ second
    have iu : u∈({w,c}:Finset V) := eq ▸ mem_insert_self ..
    exact (mem_insert.mp iu).elim uw (fun j => (mem_sdiff.mp um).2 (mem_singleton.mp j ▸ cm))
  obtain ⟨k,km,kv⟩ := other
  apply Nat.le_of_not_gt
  intro bad
  obtain ⟨x,xm,_⟩ := remote_for_pair G h high vm km kv.symm bad
  obtain ⟨xn,xr,xb,_⟩ := mem_filter.mp xm
  have xnr : x≠r := fun eq => xb (eq ▸ h.rb)
  have xnb : x≠b := fun eq => xr (eq ▸ h.rb.symm)
  have eq := card_le_one.mp lim _ (miss xn rn xnr xr) _ (miss xn bn xnb xb)
  have ir : r∈({x,b}:Finset V) := eq ▸ mem_insert_of_mem (mem_singleton_self _)
  exact (mem_insert.mp ir).elim xnr.symm (fun j => h.rb.ne (mem_singleton.mp j))

end Graffiti384b.QuarticSwitch
#print axioms Graffiti384b.QuarticSwitch.simplicial_cubic_needs_two
#print axioms Graffiti384b.QuarticSwitch.high_score_quartic
