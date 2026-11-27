import SeamBudget180
import WingCertificate180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restrict the neighbors of w to the given set. -/
noncomputable def prune (J : SimpleGraph V) (w : V) (P : Finset V) : SimpleGraph V where
  Adj a b := J.Adj a b ∧ (a=w → b∈P) ∧ (b=w → a∈P)
  symm _ _ e := ⟨e.1.symm,e.2.2,e.2.1⟩
  loopless _ e := e.1.ne rfl

omit [Fintype V] [DecidableEq V] in
theorem prune_le (J : SimpleGraph V) (w : V) (P : Finset V) : prune J w P≤J := fun _ _ e => e.1

omit [Fintype V] [DecidableEq V] in
theorem prune_away {J : SimpleGraph V} {w a b : V} {P : Finset V}
    (aw : a≠w) (bw : b≠w) (e : J.Adj a b) : (prune J w P).Adj a b :=
  ⟨e,fun h => (aw h).elim,fun h => (bw h).elim⟩

omit [Fintype V] [DecidableEq V] in
theorem prune_spoke {J : SimpleGraph V} {w a : V} {P : Finset V}
    (e : J.Adj w a) (ap : a∈P) : (prune J w P).Adj w a := ⟨e,fun _ => ap,fun h => (e.ne h.symm).elim⟩

/-- Any positive chord gain survives, at the old optimum, after restricting
the middle to its two spokes in the lower graph. This direction holds
whether or not the middle is a cut vertex. -/
theorem gain_preserves_pruned {J : SimpleGraph V} (jc : J.Connected) (hn : 2<Fintype.card V)
    {x y w : V} (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U : Finset V) (gain : weightedLeaves J U<weightedLeaves (J⊔edge x y) U) :
    w∈U ∧ weightedLeaves (prune J w {x,y}) U=weightedLeaves J U := by
  classical
  obtain ⟨C,cu,wc,sz,cert⟩ := (triangle_gain_iff_core J jc hn x y w xy old xw wy U).mp gain
  let D := univ\C
  let H := prune J w {x,y}
  have wx : H.Adj w x := prune_spoke xw.symm (mem_insert_self ..)
  have wY : H.Adj w y := prune_spoke wy (mem_insert_of_mem (mem_singleton_self _))
  have off {v : V} (vd : v∈D) : v≠w := fun eq => (mem_sdiff.mp vd).2 (eq ▸ wc)
  have retain {i j : V} (hi : i∈D) (hj : j∈D) (e : J.Adj i j) : H.Adj i j := prune_away (off hi) (off hj) e
  have lift {i : V} (iw : i≠w) (dom : Dominates J D i) : Dominates H (insert w D) i := by
    obtain ⟨j,jd,e⟩ := dom
    exact ⟨j,mem_insert_of_mem jd,prune_away iw (off jd) e⟩
  have finish (con : Con H (insert w D)) (dom : ∀ i∈C.erase w,Dominates H (insert w D) i) :
      weightedLeaves J U≤weightedLeaves H U := by
    have bound := weightedCore H (insert w D) U con (by
      intro i hi
      apply dom
      simpa [D] using hi)
    have sub : C.erase w⊆U\(insert w D) := by
      intro i hi
      exact mem_sdiff.mpr ⟨cu (mem_of_mem_erase hi),by simpa [D] using mem_erase.mp hi⟩
    have cap := (card_le_card sub).trans bound
    have cardinal := card_erase_add_one wc
    omega
  have one {a b : V} (wa : H.Adj w a) (wb : H.Adj w b) (h : NeedsTip J C D a b) :
      weightedLeaves J U≤weightedLeaves H U := by
    have con : Con H D := h.2.2.1.mono (fun i j e => retain i.property j.property e)
    apply finish (con_of_neighbors H con (subset_insert _ _) (by
      intro j hj no
      exact (mem_insert.mp hj).resolve_right no ▸ ⟨b,h.2.1,wb⟩))
    intro i hi
    by_cases ia : i=a
    · exact ia ▸ ⟨w,mem_insert_self ..,wa.symm⟩
    · exact lift (mem_erase.mp hi).1 (h.2.2.2.2 i (mem_of_mem_erase hi) ia)
  refine ⟨cu wc,le_antisymm (leaf_mono J (prune_le ..) U) ?_⟩
  rcases cert with ⟨ss,dom⟩|h|h
  · apply finish _ (fun i hi => lift (mem_erase.mp hi).1 (dom i (mem_of_mem_erase hi)))
    apply (connected_cuts H _).mpr
    refine ⟨⟨w,mem_insert_self ..⟩,?_⟩
    intro f hf
    have wd {j : V} (hj : j∈D) (e : H.Adj w j) : f w=f j :=
      hf w (mem_insert_self ..) j (mem_insert_of_mem hj) e
    have on : OnEdges J D f := fun i hi j hj e =>
      hf i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) (retain hi hj e)
    have same := ss.2.2.2 f on ((wd ss.1 wx).symm.trans (wd ss.2.1 wY))
    have all (i : V) (hi : i∈insert w D) : f w=f i :=
      (mem_insert.mp hi).elim (fun h => h ▸ rfl) (fun h => (wd ss.1 wx).trans (same x ss.1 i h))
    intro i hi j hj
    exact (all i hi).symm.trans (all j hj)
  · exact one wx wY h
  · exact one wY wx h

#print axioms gain_preserves_pruned
end Minimal180.CutGain
