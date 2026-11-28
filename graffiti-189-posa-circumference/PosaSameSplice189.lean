import PosaSpliceCommon189
open SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
open Graffiti189LongestPath.PosaRouteCut Graffiti189LongestPath.PosaSpliceCommon
open private Graffiti189LongestPath.FanRoutable.path_append_separated from FanLower189
set_option warningAsError true
set_option maxHeartbeats 5000000
namespace Graffiti189LongestPath.PosaSameSplice
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- If the two gap endpoints lie on the same route, splice in their
spine segment; no earlier covered spine index is lost. -/
theorem augment_same_route {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (R : OrderedPair p) (g i h : Nat) (gi : g<i) (ih : i<h) (hn : h≤p.length)
    (gL : p.getVert g∈R.left.support) (hL : p.getVert h∈R.left.support)
    (empty : ∀ j,g<j → j<h → ¬Hits R j) :
    ∃ T : OrderedPair p, Hits T i ∧
      (∀ j≤p.length,Hits R j → Hits T j) := by
  have gl := (gi.trans ih).le.trans hn
  obtain ⟨C⟩ := cut_ordered_route p R.left hp R.leftPath R.leftOrder g gl gL
  obtain ⟨D⟩ := cut_ordered_route p R.left hp R.leftPath R.leftOrder h hn hL
  obtain ⟨M,mp,mo,mb,_,ms,mc⟩ := spine_segment p hp g h (by omega) hn
  have apart := separated_cuts_disjoint R.leftPath R.leftOrder hp (gi.trans ih) gl hn C D
  let A := C.pre.append M
  have Ap : A.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated
    C.prePath mp (by
      intro z zC zM
      obtain ⟨j,eq,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zM)
      have cj := (C.preBounds j jN (eq.symm ▸ zC)).2
      have mj := (mb j jN (eq.symm ▸ zM)).1
      have ej : j=g := by omega
      exact eq.symm.trans (congrArg p.getVert ej))
  have Ao : Ordered p A := ordered_append_mid p (j:=g) rfl C.prePath C.preOrder mo
    C.preBounds mb
  have Ab : Bounds p A 0 h := bound_append p (Nat.zero_le _) (by omega : g≤h) C.preBounds mb
  let W := A.append D.suf
  have Wp : W.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated Ap D.sufPath (by
    intro z zA zD
    rw [show A=C.pre.append M from rfl,mem_support_append_iff] at zA
    rcases zA with zC|zM
    · exact (apart zC zD).elim
    obtain ⟨j,eq,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zM)
    have mj := (mb j jN (eq.symm ▸ zM)).2
    have jj := (D.sufBounds j jN (eq.symm ▸ zD)).1
    have ej : j=h := by omega
    exact eq.symm.trans (congrArg p.getVert ej))
  have Wo : Ordered p W := ordered_append_mid p (j:=h) rfl Ap Ao D.sufOrder Ab D.sufBounds
  have join : ∀ z∈W.support,z∈R.right.support → z=a ∨ z=b := by
    intro z zw zr
    rw [show W=A.append D.suf from rfl,mem_support_append_iff] at zw
    rcases zw with za|zd
    · rw [show A=C.pre.append M from rfl,mem_support_append_iff] at za
      rcases za with zc|zm
      · exact R.only z (C.pre_inc z zc) zr
      obtain ⟨j,eq,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zm)
      rcases (mb j jN (eq.symm ▸ zm)) with ⟨gj,jh⟩
      by_cases g' : j=g
      · exact R.only z ((g' ▸ eq) ▸ gL) zr
      by_cases h' : j=h
      · exact R.only z ((h' ▸ eq) ▸ hL) zr
      exact (empty j (by omega) (by omega) (Or.inr (eq.symm ▸ zr))).elim
    exact R.only z (D.suf_inc z zd) zr
  have hi : p.getVert i∈W.support := (mem_support_append_iff A D.suf).mpr (Or.inl
    ((mem_support_append_iff C.pre M).mpr (Or.inr ((mc i (ih.le.trans hn)).mpr ⟨gi.le,ih.le⟩))))
  let T : OrderedPair p :=
    ⟨W,R.right,Wp,R.rightPath,Wo,R.rightOrder,join,
      ⟨p.getVert i,Or.inl hi,internal_index_not_endpoint hp i (by omega) (by omega)⟩⟩
  refine ⟨T,Or.inl hi,?_⟩
  intro j jN hR
  rcases hR with jL|jR
  · left
    change p.getVert j∈(A.append D.suf).support
    apply (mem_support_append_iff A D.suf).mpr
    by_cases low : j≤g
    · exact Or.inl ((mem_support_append_iff C.pre M).mpr
        (Or.inl (C.keepsPre j jN low jL)))
    by_cases high : h≤j
    · exact Or.inr (D.keepsSuf j jN high jL)
    exact (empty j (by omega) (by omega) (Or.inl jL)).elim
  · exact Or.inr jR

#print axioms augment_same_route
end Graffiti189LongestPath.PosaSameSplice
