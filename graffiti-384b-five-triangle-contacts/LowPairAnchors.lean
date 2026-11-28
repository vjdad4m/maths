import PairSaving
import FourProfile
namespace Graffiti384b.PairMix
open Finset SimpleGraph LowSample Four29
open private LowSample.two_degree from LowSample384b
open private TrianglePrune.induced_cost from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem core (H : Finset V) (hs : H.card=27) {e f : V} (ef : e≠f) (es : Hᶜ={e,f})
    (inj : Set.InjOn (trianglesAt G) (H:Set V)) (rich : ∀v∈H,2≤trianglesAt G v)
    (size : ∀v∉H,(G.neighborFinset v).card=2) (inside : ∀v∉H,G.neighborFinset v⊆H)
    (apart : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (cap : ∀v∈roots G e f,trianglesAt G v≤12) : gamma G≤14 := by
  let A := G.neighborFinset e
  let B := G.neighborFinset f
  let R := A∪B
  let W := H\R
  have oe : e∉H := mem_compl.mp (es ▸ mem_insert_self ..)
  have of' : f∉H := mem_compl.mp (es ▸ mem_insert_of_mem (mem_singleton_self _))
  have rh : R⊆H := union_subset (inside e oe) (inside f of')
  have rs : R.card=4 := by rw [show R=G.neighborFinset e∪G.neighborFinset f from rfl,card_union_of_disjoint apart,size e oe,size f of']
  have wr : Disjoint W R := disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2)
  have full : (univ:Finset V)=insert e (insert f H) := by
    ext v; simp only [mem_univ,true_iff,mem_insert]
    by_cases vh : v∈H
    · tauto
    · have m := mem_compl.mpr vh; rw [es] at m
      simpa [vh] using m
  let L : Layout G := ⟨H,W,A,B,e,f,full,(sdiff_union_of_subset rh).symm,by
    rw [show W=H\R from rfl,card_sdiff rh,hs,rs],size e oe,size f of',oe,of',ef,
    wr.mono_right subset_union_left,wr.mono_right subset_union_right,apart,rfl,rfl,inj,rich,cap⟩
  exact L.saving

/-- A global score cap of twelve at the four reserved vertices suffices for the
catalogue inequality, independent of the numbers of triangle contacts or other exterior neighbors. -/
theorem low_anchors (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (cap : ∀v∈roots G e f,trianglesAt G v≤12) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro fail
  obtain ⟨hs,highN,disj,_⟩ := Shared29.residual_distinct G t (by omega) fail
  have D := data_of_failure G t h q fail de df ne
  let P := nonleaves G
  let J := G.induce (P:Set V)
  let H := (high G).subtype (fun v => v∈P)
  have hp : high G⊆P := fun v vm => mem_filter.mpr ⟨mem_univ _,(by have := (mem_filter.mp vm).2; omega)⟩
  have hcard : H.card=27 := by
    have m := congrArg Finset.card (subtype_map_of_mem (p:=fun v => v∈P) hp)
    simpa only [H,card_map,h] using m
  let E : P := ⟨e,mem_filter.mpr ⟨mem_univ _,de.ge⟩⟩
  let F : P := ⟨f,mem_filter.mpr ⟨mem_univ _,df.ge⟩⟩
  have en : E≠F := fun eq => ne (congrArg Subtype.val eq)
  have es : Hᶜ={E,F} := by
    ext v
    have low : v∉H ↔ v.val∈twos G := by simp [H,twos,v.property]
    rw [mem_compl,low,D.earSet,mem_insert,mem_singleton,mem_insert,mem_singleton]
    exact or_congr (show v.val=E.val ↔ v=E from Subtype.ext_iff.symm) (show v.val=F.val ↔ v=F from Subtype.ext_iff.symm)
  have scores (w : P) : trianglesAt J w=trianglesAt G w := Prune.counts_preserved G P Subset.rfl w
  have low {w : P} (wm : w∉H) : w.val∈twos G := mem_sdiff.mpr ⟨w.property,fun h => wm (mem_subtype.mpr h)⟩
  have same (w : P) : J.neighborFinset w=(G.neighborFinset w.val).subtype (fun v => v∈P) := by
    ext x; simp only [mem_neighborFinset,mem_subtype]; rfl
  have sol := core J H hcard en es (fun x xm y ym eq => Subtype.ext (D.scoreInj (mem_subtype.mp xm) (mem_subtype.mp ym)
    ((scores x).symm.trans (eq.trans (scores y))))) (fun v vm => (scores v) ▸ D.rich v (mem_subtype.mp vm))
    (fun v vm => by
      rw [same]
      have sub := (highN v (low vm)).trans hp
      have m := congrArg Finset.card (subtype_map_of_mem (p:=fun v => v∈P) sub)
      simpa only [card_map,card_neighborFinset_eq_degree,LowSample.two_degree G (low vm)] using m)
    (fun v vm x xm => by rw [same] at xm; exact mem_subtype.mpr (highN v (low vm) (mem_subtype.mp xm)))
    (disjoint_left.mpr (fun z vz wz => by
      rw [same] at vz wz
      have ee : e∈twos G := D.earSet ▸ mem_insert_self ..
      have ff : f∈twos G := D.earSet ▸ mem_insert_of_mem (mem_singleton_self _)
      exact disjoint_left.mp (disj e ee f ff ne) (mem_subtype.mp vz) (mem_subtype.mp wz)))
    (fun v vm => by
      rw [scores]
      apply cap
      change v∈J.neighborFinset E∪J.neighborFinset F at vm
      rw [same,same] at vm
      exact (mem_union.mp vm).elim (fun a => mem_union_left _ (mem_subtype.mp a)) (fun b => mem_union_right _ (mem_subtype.mp b)))
  have cost := TrianglePrune.induced_cost G P
  change P.card≤gamma J+Capacity.value G P ∅ at cost
  have more := Capacity.mono_kept G (r:=P) (empty_subset Pᶜ)
  have exactSize := OddQuota.rooted_value G
  change gamma G+Capacity.value G P Pᶜ=Fintype.card V at exactSize
  change P.card=29 at q
  simp only [bound,t] at fail
  omega
end Graffiti384b.PairMix
#print axioms Graffiti384b.PairMix.core
#print axioms Graffiti384b.PairMix.low_anchors
