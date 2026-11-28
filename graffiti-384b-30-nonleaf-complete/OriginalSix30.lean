import SixAnchorSaving30
import SharedAnchorClose
import FinishNonleaves28

namespace Graffiti384b.EarMix
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
open private TrianglePrune.induced_cost from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem core (H : Finset V) (hs : H.card=27) (es : Hᶜ.card=3)
    (inj : Set.InjOn (trianglesAt G) (H:Set V)) (rich : ∀v∈H,2≤trianglesAt G v)
    (size : ∀v∉H,(G.neighborFinset v).card=2) (inside : ∀v∉H,G.neighborFinset v⊆H)
    (apart : ∀v∉H,∀w∉H,v≠w → Disjoint (G.neighborFinset v) (G.neighborFinset w)) :
    gamma G≤15 := by
  classical
  obtain ⟨e,f,g,ef,eg,fg,eq⟩ := card_eq_three.mp es
  have oe : e∉H := mem_compl.mp (eq ▸ mem_insert_self ..)
  have of' : f∉H := mem_compl.mp (eq ▸ mem_insert_of_mem (mem_insert_self ..))
  have og : g∉H := mem_compl.mp (eq ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  let A := G.neighborFinset e
  let B := G.neighborFinset f
  let C := G.neighborFinset g
  let R := A∪(B∪C)
  let W := H\R
  have ab := apart e oe f of' ef
  have bc := apart f of' g og fg
  have ca := apart g og e oe eg.symm
  have rh : R⊆H := union_subset (inside e oe) (union_subset (inside f of') (inside g og))
  have rs : R.card=6 := by
    rw [show R=G.neighborFinset e∪(G.neighborFinset f∪G.neighborFinset g) from rfl,
      card_union_of_disjoint (disjoint_union_right.mpr ⟨ab,ca.symm⟩),card_union_of_disjoint bc,
      size e oe,size f of',size g og]
  have wr : Disjoint W R := disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2)
  have full : (univ:Finset V)=insert e (insert f (insert g H)) := by
    ext v; simp only [mem_univ,true_iff,mem_insert]
    by_cases vh : v∈H
    · tauto
    · have m := mem_compl.mpr vh; rw [eq] at m
      simpa [vh] using m
  let L : Layout G := ⟨H,W,A,B,C,e,f,g,full,(sdiff_union_of_subset rh).symm,by
    rw [show W=H\R from rfl,card_sdiff rh,hs,rs],size e oe,size f of',size g og,
    oe,of',og,ef,fg,eg.symm,wr.mono_right subset_union_left,
    wr.mono_right (subset_union_left.trans subset_union_right),wr.mono_right (subset_union_right.trans subset_union_right),
    ab,bc,ca,rfl,rfl,rfl,inj,rich⟩
  exact L.saving

/-- The catalogue inequality at thirty nonleaves and diversity twenty-nine. -/
theorem original_bound (t : (types G).card=29) (q : (nonleaves G).card=30) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro fail
  obtain ⟨hs,highN,disj,_⟩ := Shared29.residual_distinct G t (by omega) fail
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  let P := nonleaves G
  let J := G.induce (P:Set V)
  let H := (high G).subtype (fun v => v∈P)
  have hp : high G⊆P := fun v vm => mem_filter.mpr ⟨mem_univ _,(by
    have := (mem_filter.mp vm).2; omega)⟩
  have hcard : H.card=27 := by
    have m := congrArg Finset.card (subtype_map_of_mem (p:=fun v => v∈P) hp)
    simpa only [H,card_map,hs] using m
  have n : Fintype.card P=30 := (Fintype.card_coe _).trans q
  have es : Hᶜ.card=3 := by rw [card_compl,n,hcard]
  have scores (w : P) : trianglesAt J w=trianglesAt G w := Prune.counts_preserved G P Subset.rfl w
  have low {w : P} (wm : w∉H) : w.val∈twos G :=
    mem_sdiff.mpr ⟨w.property,fun h => wm (mem_subtype.mpr h)⟩
  have same {w : P} (wm : w∉H) : J.neighborFinset w=(G.neighborFinset w.val).subtype (fun v => v∈P) := by
    ext x; simp only [mem_neighborFinset,mem_subtype]; rfl
  have sol := core J H hcard es (fun x xm y ym eq => Subtype.ext (inj (mem_subtype.mp xm) (mem_subtype.mp ym)
    ((scores x).symm.trans (eq.trans (scores y))))) (fun v vm => (scores v) ▸ rich v (mem_subtype.mp vm))
    (fun v vm => by
      rw [same vm]
      have sub := (highN v (low vm)).trans hp
      have m := congrArg Finset.card (subtype_map_of_mem (p:=fun v => v∈P) sub)
      simpa only [card_map,card_neighborFinset_eq_degree,LowSample.two_degree G (low vm)] using m)
    (fun v vm x xm => by
      rw [same vm] at xm
      exact mem_subtype.mpr (highN v (low vm) (mem_subtype.mp xm)))
    (fun v vm w wm ne => disjoint_left.mpr (fun z vz wz => by
      rw [same vm] at vz; rw [same wm] at wz
      exact disjoint_left.mp (disj v (low vm) w (low wm) (fun h => ne (Subtype.ext h))) (mem_subtype.mp vz) (mem_subtype.mp wz)))
  have cost := TrianglePrune.induced_cost G P
  change P.card≤gamma J+Capacity.value G P ∅ at cost
  have more := Capacity.mono_kept G (r:=P) (empty_subset Pᶜ)
  have exactSize := OddQuota.rooted_value G
  change gamma G+Capacity.value G P Pᶜ=Fintype.card V at exactSize
  change P.card=30 at q
  simp only [bound,t] at fail
  omega

theorem numerical_bound (t : (types G).card=29) (q : (nonleaves G).card=30) : gamma G≤Fintype.card V-15 := by
  simpa only [bound,t] using original_bound G t q

theorem remaining_nonleaves (t : (types G).card=29) (bad : bound G<gamma G) : (nonleaves G).card=29 := by
  rcases TwentyEight.remaining_counts G t bad with h|h
  · exact h
  · exact (Nat.not_lt_of_ge (original_bound G t h) bad).elim
end Graffiti384b.EarMix
#print axioms Graffiti384b.EarMix.core
#print axioms Graffiti384b.EarMix.original_bound
#print axioms Graffiti384b.EarMix.numerical_bound
#print axioms Graffiti384b.EarMix.remaining_nonleaves
