import PosaSameSplice189
open SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
open Graffiti189LongestPath.PosaRouteCut Graffiti189LongestPath.PosaSpliceCommon
open private Graffiti189LongestPath.FanRoutable.path_append_separated from FanLower189
set_option warningAsError true
set_option maxHeartbeats 6500000
namespace Graffiti189LongestPath.PosaCrossSplice
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- If a gap separates different original routes, replace their prefixes
by the initial spine segment and the chord-to-spine segment, respectively. -/
theorem augment_cross_routes {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (R : OrderedPair p) (g i h : Nat) (gi : g<i) (ih : i<h) (hn : h≤p.length)
    (gL : p.getVert g∈R.left.support) (hR : p.getVert h∈R.right.support)
    (edge : G.Adj a (p.getVert i))
    (empty : ∀ j,g<j → j<h → ¬Hits R j) :
    ∃ T : OrderedPair p, Hits T i ∧
      (∀ j≤p.length,Hits R j → Hits T j) := by
  have gl := (gi.trans ih).le.trans hn
  have il := ih.le.trans hn
  have ip : 0<i := by omega
  obtain ⟨C⟩ := cut_ordered_route p R.left hp R.leftPath R.leftOrder g gl gL
  obtain ⟨D⟩ := cut_ordered_route p R.right hp R.rightPath R.rightOrder h hn hR
  obtain ⟨Q,qp,qo,qb,_,qs,qc⟩ := spine_segment p hp 0 g (by omega) gl
  let P := Q.copy p.getVert_zero rfl
  have Pp : P.IsPath := by simpa [P] using qp
  have Po : Ordered p P := by simpa [P,Ordered,length_copy,getVert_copy] using qo
  have Pb : Bounds p P 0 g := by simpa [P,Bounds,support_copy] using qb
  have Ps : ∀ z∈P.support,z∈p.support := by simpa [P] using qs
  have Pc : ∀ j≤p.length,p.getVert j∈P.support ↔ 0≤j ∧ j≤g := by simpa [P] using qc
  obtain ⟨M,mp,mo,mb,_,ms,mc⟩ := spine_segment p hp i h (by omega) hn
  have ed0 : G.Adj (p.getVert 0) (p.getVert i) := p.getVert_zero.symm ▸ edge
  let E0 := ed0.toWalk
  have ep0 : E0.IsPath := IsPath.of_adj ed0
  have ends0 : ∀ z∈E0.support,z∈p.support → z=p.getVert 0 ∨ z=p.getVert i := by
    intro z hz _
    simpa [E0,Adj.toWalk] using hz
  have ord := ordered_exterior p hp ip il ep0 ends0
  let E := E0.copy p.getVert_zero rfl
  have Ep : E.IsPath := by simpa [E] using ep0
  have Eo : Ordered p E := by
    simpa [E,Ordered,length_copy,getVert_copy] using ord.1
  have Eb : Bounds p E 0 i := by
    simpa [E,Bounds,support_copy] using ord.2
  have Eends : ∀ z∈E.support,z=a ∨ z=p.getVert i := by
    intro z hz
    simpa [E,E0,Adj.toWalk,getVert_zero] using hz
  let X := P.append C.suf
  have Xp : X.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated Pp C.sufPath (by
    intro z zp zs
    obtain ⟨j,e,jN⟩ := mem_support_iff_exists_getVert.mp (Ps z zp)
    have a := (Pb j jN (e.symm ▸ zp)).2
    have b := (C.sufBounds j jN (e.symm ▸ zs)).1
    exact e.symm.trans (congrArg p.getVert (by omega : j=g)))
  have Xo : Ordered p X := ordered_append_mid p (j:=g) rfl Pp Po C.sufOrder Pb C.sufBounds
  let Y := E.append M
  have Yp : Y.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated
    Ep mp (by
      intro z ze zm
      rcases Eends z ze with a'|i'
      · have H : p.getVert 0∈M.support := p.getVert_zero.symm ▸ (a' ▸ zm)
        have q := (mb 0 (by omega) H).1
        omega
      · exact i')
  have Yo : Ordered p Y := ordered_append_mid p (j:=i) rfl Ep
    Eo mo Eb mb
  have Yb : Bounds p Y 0 h := bound_append p (Nat.zero_le _) (by omega : i≤h) Eb mb
  let Z := Y.append D.suf
  have Zp : Z.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated Yp D.sufPath (by
    intro z zy zd
    rw [show Y=E.append M from rfl,mem_support_append_iff] at zy
    rcases zy with ze|zm
    · rcases Eends z ze with x|x
      · have H : p.getVert 0∈D.suf.support := p.getVert_zero.symm ▸ (x ▸ zd)
        have q := (D.sufBounds 0 (by omega) H).1
        omega
      · have q := (D.sufBounds i il (x ▸ zd)).1
        omega
    obtain ⟨j,e,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zm)
    have a := (mb j jN (e.symm ▸ zm)).2
    have b := (D.sufBounds j jN (e.symm ▸ zd)).1
    exact e.symm.trans (congrArg p.getVert (by omega : j=h)))
  have Zo : Ordered p Z := ordered_append_mid p (j:=h) rfl Yp Yo D.sufOrder Yb D.sufBounds
  have only : ∀ z∈X.support,z∈Z.support → z=a ∨ z=b := by
    intro z zx zz
    rw [show X=P.append C.suf from rfl,mem_support_append_iff] at zx
    rw [show Z=Y.append D.suf from rfl,mem_support_append_iff] at zz
    have zr : z∈E.support ∨ z∈M.support ∨ z∈D.suf.support := by
      rcases zz with zy|zs
      · rw [show Y=E.append M from rfl,mem_support_append_iff] at zy
        exact zy.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr zs)
    rcases zx with zp|zc <;> rcases zr with ze|zm|zd
    · rcases Eends z ze with za|zi
      · exact Or.inl za
      · have q := (Pb i il (zi ▸ zp)).2
        omega
    · obtain ⟨j,e,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zm)
      have lo := (mb j jN (e.symm ▸ zm)).1
      have hi := (Pb j jN (e.symm ▸ zp)).2
      omega
    · obtain ⟨j,e,jN⟩ := mem_support_iff_exists_getVert.mp (Ps z zp)
      have lo := (D.sufBounds j jN (e.symm ▸ zd)).1
      have hi := (Pb j jN (e.symm ▸ zp)).2
      omega
    · rcases Eends z ze with za|zi
      · exact Or.inl za
      · exact (empty i gi ih (Or.inl (zi ▸ C.suf_inc z zc))).elim
    · obtain ⟨j,e,jN⟩ := mem_support_iff_exists_getVert.mp (ms z zm)
      obtain ⟨ij,jh⟩ := mb j jN (e.symm ▸ zm)
      by_cases eh : j=h
      · exact R.only z (C.suf_inc z zc) ((eh ▸ e) ▸ hR)
      · exact (empty j (by omega) (by omega) (Or.inl (e.symm ▸ C.suf_inc z zc))).elim
    · exact R.only z (C.suf_inc z zc) (D.suf_inc z zd)
  have iz : p.getVert i∈Z.support := (mem_support_append_iff Y D.suf).mpr (Or.inl
    ((mem_support_append_iff E M).mpr (Or.inl E.end_mem_support)))
  let T : OrderedPair p :=
    ⟨X,Z,Xp,Zp,Xo,Zo,only,
      ⟨_,Or.inr iz,internal_index_not_endpoint hp i (by omega) (by omega)⟩⟩
  refine ⟨T,Or.inr iz,?_⟩
  intro j jN t
  by_cases low : j≤g
  · exact Or.inl ((mem_support_append_iff P C.suf).mpr
      (Or.inl ((Pc j jN).mpr ⟨Nat.zero_le _,low⟩)))
  by_cases high : h≤j
  · rcases t with jL|jR
    · exact Or.inl ((mem_support_append_iff P C.suf).mpr
        (Or.inr (C.keepsSuf j jN (by omega) jL)))
    · exact Or.inr ((mem_support_append_iff Y D.suf).mpr
        (Or.inr (D.keepsSuf j jN high jR)))
  exact (empty j (by omega) (by omega) t).elim

#print axioms augment_cross_routes
end Graffiti189LongestPath.PosaCrossSplice
