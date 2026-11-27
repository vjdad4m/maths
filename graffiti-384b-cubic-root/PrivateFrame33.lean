import PrivatePalette33

namespace Graffiti384b.RootCut
open Finset SimpleGraph HighEar EarAnchor EarFrame33 CliquePivot33
open private EarAnchor.sees_in_clique from CubicAnchor33
open private HighEar.outside_cubic from HighEarPins33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem two_from {S K : Finset V} {v : V} (ks : K.card=2) (sub : K⊆S)
    (edges : ∀ w∈K,H.Adj v w) : 2≤nbr H v S := by
  have inc : K⊆S.filter (H.Adj v) := fun w m => mem_filter.mpr ⟨sub m,edges w m⟩
  simpa only [ks] using card_le_card inc

/-- Put the two ear endpoints opposite the ear and the exterior cubic.
The two clique contacts sit on the latter side. -/
theorem contact_frame {e a c u p q : V} (de : H.degree e=2) (du : H.degree u=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : a≠c) (au : a≠u) (cu : c≠u)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (an : a∉C) (cn : c∉C)
    (nc : H.neighborFinset u⊆C) (pm : p∈C\H.neighborFinset u) (qm : q∈C\H.neighborFinset u)
    (ap : H.Adj a p) (cq : H.Adj c q) :
    ∃ v,v≠u ∧ v∉R ∧ H.degree v=3 := by
  classical
  let N := H.neighborFinset u
  have ns : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
  obtain ⟨x,xn⟩ := card_pos.mp (by omega : 0<N.card)
  let K := N.erase x
  let M := C\N
  let A := K∪{a,c}
  let B := M∪{u,e}
  have ks : K.card=2 := by dsimp [K]; rw [card_erase_of_mem xn,ns]
  have ms : M.card=2 := by dsimp [M]; rw [card_sdiff nc,cl.2,ns]
  have kn : K⊆N := erase_subset _ _
  have kc : K⊆C := kn.trans nc
  have mc : M⊆C := sdiff_subset
  have ka : K⊆A := subset_union_left
  have mb : M⊆B := subset_union_left
  have dis : Disjoint K M := disjoint_left.mpr (fun _ km mm => (mem_sdiff.mp mm).2 (kn km))
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have un : u∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have aa : a∈A := mem_union_right _ (mem_insert_self ..)
  have ca : c∈A := mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))
  have ub : u∈B := mem_union_right _ (mem_insert_self ..)
  have eb : e∈B := mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))
  have front {w : V} (wc : w∈C) (wn : w∉M) : 2≤nbr H w B :=
    two_from H ms mb (fun y ym => cl.1 wc (mc ym) (fun eq => wn (eq ▸ ym)))
  have back {w : V} (wc : w∈C) (wn : w∉K) : 2≤nbr H w A :=
    two_from H ks ka (fun y ym => cl.1 wc (kc ym) (fun eq => wn (eq ▸ ym)))
  have pins : Frame H A B := by
    refine ⟨disjoint_left.mpr ?_,?_,?_⟩
    · intro w wa wb
      rcases mem_union.mp wa with wk|ends
      · rcases mem_union.mp wb with wm|oth
        · exact disjoint_left.mp dis wk wm
        · rcases (show w=u ∨ w=e by simpa using oth) with rfl|rfl
          · exact un (kc wk)
          · exact en (kc wk)
      · rcases (show w=a ∨ w=c by simpa using ends) with rfl|rfl
        · rcases mem_union.mp wb with m|m
          · exact an (mc m)
          · simp [au,ea.ne.symm] at m
        · rcases mem_union.mp wb with m|m
          · exact cn (mc m)
          · simp [cu,ec.ne.symm] at m
    · intro w wa
      rcases mem_union.mp wa with wk|ends
      · exact front (kc wk) (disjoint_left.mp dis wk)
      · rcases (show w=a ∨ w=c by simpa using ends) with rfl|rfl
        · exact PinnedColor34.two H (fun (eq : e=p) => en (eq ▸ mc pm)) ea.symm ap eb (mb pm)
        · exact PinnedColor34.two H (fun (eq : e=q) => en (eq ▸ mc qm)) ec.symm cq eb (mb qm)
    · intro w wb
      rcases mem_union.mp wb with wm|oth
      · exact back (mc wm) (disjoint_left.mp dis.symm wm)
      · rcases (show w=u ∨ w=e by simpa using oth) with rfl|rfl
        · exact two_from H ks ka (fun y ym => (H.mem_neighborFinset _ _).mp (kn ym))
        · exact PinnedColor34.two H ac ea ec aa ca
  have xk : x∉K := not_mem_erase _ _
  have xm : x∉M := fun m => (mem_sdiff.mp m).2 xn
  have xc := nc xn
  have xa : x∉A := by
    intro m
    rcases mem_union.mp m with k|h
    · exact xk k
    · rcases (show x=a ∨ x=c by simpa using h) with rfl|rfl
      · exact an xc
      · exact cn xc
  have xb : x∉B := by
    intro m
    rcases mem_union.mp m with k|h
    · exact xm k
    · rcases (show x=u ∨ x=e by simpa using h) with rfl|rfl
      · exact un xc
      · exact en xc
  obtain ⟨v,_,vb,vr,dv,_⟩ := HighEar.outside_cubic H de pos inj eb tight pins xa xb (back xc xk) (front xc xm)
  exact ⟨v,fun eq => vb (eq ▸ ub),vr,dv⟩

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.contact_frame
