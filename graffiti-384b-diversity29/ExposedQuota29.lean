import Boundary384b

namespace Graffiti384b.Quota29
open Finset SimpleGraph LowSample CliqueChoice
open private Repair.full_nbr from Repair384b
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def anchors (I : Finset V) := (high G).filter (fun v => ∃ x∈I,G.Adj x v)

private theorem scarcity (t : (types G).card=29) (fail : bound G<gamma G)
    {I : Finset V} (sub : I⊆twos G) (ind : ∀ v∈I,∀ w∈I,¬G.Adj v w) :
    (high G).card+2*I.card<29+(anchors G I).card := by
  by_contra! le
  apply (not_lt_of_ge (Repair.exact_of_low_support G I
    (disjoint_left.mpr (fun _ m => (mem_sdiff.mp (sub m)).2))
    (fun v vm => (LowSample.two_degree G (sub vm)).ge) ind ?_)) fail
  rwa [t]

omit [DecidableEq V] in
private theorem single (v : V) : (anchors G {v}).card=nbr G v (high G) := by
  simp [anchors,nbr]

/-- In a failure of diversity 29, deletion of at most one vertex makes
the full set of degree-two vertices independent. -/
theorem independent_twos (t : (types G).card=29) (fail : bound G<gamma G) :
    ∃ I⊆twos G,(twos G).card≤I.card+1 ∧ ∀ v∈I,∀ w∈I,¬G.Adj v w := by
  classical
  have ht := type_bound G
  have one {v : V} (vm : v∈twos G) : 1≤nbr G v (high G) := by
    have z := scarcity G t fail (singleton_subset_iff.mpr vm) (by
      intro a am b bm; rw [mem_singleton.mp am,mem_singleton.mp bm]; exact G.loopless _)
    rw [single,card_singleton] at z
    omega
  have low {v : V} (vm : v∈twos G) : nbr G v (high G)ᶜ≤1 := by
    have := Repair.full_nbr G v (high G)
    have := LowSample.two_degree G vm
    have := one vm
    omega
  have thin {v w : V} (vm : v∈twos G) (wm : w∈twos G) (vw : G.Adj v w) :
      nbr G v (high G)≤1 := by
    have ext : 0<nbr G v (high G)ᶜ := card_pos.mpr
      ⟨w,mem_filter.mpr ⟨mem_compl.mpr (mem_sdiff.mp wm).2,vw⟩⟩
    have := Repair.full_nbr G v (high G)
    have := LowSample.two_degree G vm
    omega
  have touch {v w : V} (vm : v∈twos G) (wm : w∈twos G) (ne : v≠w)
      (v1 : nbr G v (high G)≤1) (w1 : nbr G w (high G)≤1) : G.Adj v w := by
    by_contra no
    have ind : ∀ a∈({v,w}:Finset V),∀ b∈({v,w}:Finset V),¬G.Adj a b := by
      intro a am b bm
      simp only [mem_insert,mem_singleton] at am bm
      rcases am with rfl|rfl <;> rcases bm with rfl|rfl <;> first | exact G.loopless _ | exact no | exact fun h => no h.symm
    have z := scarcity G t fail (insert_subset vm (singleton_subset_iff.mpr wm)) ind
    have eq : anchors G {v,w}=anchors G {v}∪anchors G {w} := by
      ext a; simp [anchors,and_or_left]
    rw [card_pair ne,eq] at z
    have lim := card_union_le (anchors G {v}) (anchors G {w})
    rw [single,single] at lim
    omega
  by_cases edge : ∃ x∈twos G,∃ y∈twos G,G.Adj x y
  · obtain ⟨x,xm,y,ym,xy⟩ := edge
    refine ⟨(twos G).erase x,erase_subset ..,by rw [card_erase_of_mem xm]; omega,?_⟩
    intro v vm w wm vw
    obtain ⟨vx,vt⟩ := mem_erase.mp vm
    obtain ⟨wx,wt⟩ := mem_erase.mp wm
    have xv := touch xm vt vx.symm (thin xm ym xy) (thin vt wt vw)
    have xw := touch xm wt wx.symm (thin xm ym xy) (thin wt vt vw.symm)
    exact vw.ne (card_le_one.mp (low xm) v (mem_filter.mpr ⟨mem_compl.mpr (mem_sdiff.mp vt).2,xv⟩)
      w (mem_filter.mpr ⟨mem_compl.mpr (mem_sdiff.mp wt).2,xw⟩))
  · exact ⟨twos G,Subset.rfl,by omega,fun x xm y ym xy => edge ⟨x,xm,y,ym,xy⟩⟩

/-- At least five pool vertices have a fixed degree-two neighbor at 27
high vertices, and at least four have one at 28 high vertices. -/
theorem exposed {p : Finset V} (ch : Choice G p Boundary.levels)
    (t : (types G).card=29) (q : 31≤(nonleaves G).card)
    (hh : (high G).card=27 ∨ (high G).card=28) (fail : bound G<gamma G) :
    ∃ E⊆high G\p,(if (high G).card=27 then 5 else 4)≤E.card ∧
      ∀ v∈E,∃ w∉high G\p,G.Adj v w := by
  obtain ⟨I,sub,num,ind⟩ := independent_twos G t fail
  have tsub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have total : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card tsub
  have lo := scarcity G t fail sub ind
  refine ⟨anchors G I,?_,by split_ifs <;> omega,?_⟩
  · intro z zm
    obtain ⟨zh,w,wm,wz⟩ := mem_filter.mp zm
    exact mem_sdiff.mpr ⟨zh,fun zp => (mem_sdiff.mp (sub wm)).2
      (mem_sdiff.mp (neighbors_in_pool G ch zp ((G.mem_neighborFinset ..).mpr wz.symm))).1⟩
  · intro z zm
    obtain ⟨_,w,wm,wz⟩ := mem_filter.mp zm
    exact ⟨w,fun wp => (mem_sdiff.mp (sub wm)).2 (mem_sdiff.mp wp).1,wz.symm⟩

end Graffiti384b.Quota29
#print axioms Graffiti384b.Quota29.independent_twos
#print axioms Graffiti384b.Quota29.exposed
