import FourOffGraphSupport189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_of_neighbor_mem card_pinVertices from SmallOrderFour189
open private omitted_degree_component_bound from FourOffGraphSupport189

private theorem off_five_component_carries_all_high
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (few : ∀ x∉p.support,(Pins p x).card≤2) :
    ∃ H : OmittedComponent p, 3≤H.vertices.card ∧
      (∀ z∉p.support,4≤G.degree z → z∈H.vertices) ∧
      4≤(H.vertices.filter (fun z => 4≤G.degree z)).card := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have oc : O.card=5 := off
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨z,zo,zh⟩ : ∃ z,z∈O ∧ 4≤G.degree z := (degree x y xy).elim
    (fun h => ⟨x,hx,h⟩) (fun h => ⟨y,hy,h⟩)
  obtain ⟨T,zT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component (out.mp zo)
  let H : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
  have large : 3≤H.vertices.card := by
    have d := omitted_degree_component_bound hp H zT
    have f := few z (out.mp zo)
    omega
  have sub : H.vertices⊆O := fun _ h => out.mpr (H.off _ h)
  have subc := card_sdiff_add_card_eq_card sub
  have all (w : V) (wo : w∉p.support) (wh : 4≤G.degree w) : w∈H.vertices := by
    by_contra no
    obtain ⟨U,wU,Une,Uoff,Uclosed,Ujoined⟩ := exists_omitted_component wo
    let J : OmittedComponent p := ⟨U,Une,Uoff,Uclosed,Ujoined⟩
    have large' : 3≤J.vertices.card := by
      have d := omitted_degree_component_bound hp J wU
      have f := few w wo
      omega
    have disj : J.vertices⊆O\H.vertices := by
      intro v vm
      refine mem_sdiff.mpr ⟨out.mpr (J.off _ vm),?_⟩
      intro vh
      obtain ⟨r,_,stay⟩ := J.joined v vm w wU
      have walk {i j : V} (q : G.Walk i j) (inJ : ∀ z∈q.support,z∈J.vertices) :
          i∈H.vertices → j∈H.vertices := by
        induction q with
        | nil => exact id
        | @cons i j k adj q ih =>
          intro iH
          have incl (v : V) (hv : v∈q.support) := inJ v (by simp [hv])
          apply ih incl
          by_contra jH
          exact J.off _ (incl _ q.start_mem_support) (H.closed i iH j jH adj)
      exact no (walk r stay vh)
    have cd := card_le_card disj
    omega
  refine ⟨H,large,all,?_⟩
  let A := O.filter (fun v => 4≤G.degree v)
  let B := O.filter (fun v => ¬4≤G.degree v)
  have bsmall : B.card≤1 := by
    by_contra! nob
    have gb : 1<B.card := by omega
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp gb
    exact (degree u v ne).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have cu : A.card+B.card=O.card := filter_card_add_filter_neg_card_eq_card (s:=O) (fun v => 4≤G.degree v)
  have ad : A⊆H.vertices.filter (fun z => 4≤G.degree z) := by
    intro v h
    have hv := mem_filter.mp h
    exact mem_filter.mpr ⟨all v (out.mp hv.1) hv.2,hv.2⟩
  have cd := card_le_card ad
  omega

/-- For a disconnected five-vertex omitted graph, exactly one omitted
component has order four; the other vertex is the sole low vertex. -/
theorem off_five_disconnected_shape
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (few : ∀ x∉p.support,(Pins p x).card≤2)
    (disc : ¬∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices) :
    ∃ (H : OmittedComponent p) (x : V), x∉p.support ∧ x∉H.vertices ∧
      H.vertices.card=4 ∧ (∀ z∈H.vertices,4≤G.degree z) ∧
      ∀ z∉p.support,z=x ∨ z∈H.vertices := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  obtain ⟨H,_,all,large⟩ := off_five_component_carries_all_high degree hp off few
  obtain ⟨x,xo,xh⟩ : ∃ x,x∉p.support ∧ x∉H.vertices := by
    have e : ¬∀ z∉p.support,z∈H.vertices := fun k => disc ⟨H,k⟩
    push_neg at e
    exact e
  have sub : H.vertices⊆O := fun z h => out.mpr (H.off z h)
  have big := large.trans (card_filter_le _ _)
  have cut : (O\H.vertices).card+H.vertices.card=5 :=
    (card_sdiff_add_card_eq_card sub).trans off
  have member : x∈O\H.vertices := mem_sdiff.mpr ⟨out.mpr xo,xh⟩
  have mz := card_pos.mpr ⟨x,member⟩
  refine ⟨H,x,xo,xh,by omega,?_,?_⟩
  · intro z zh
    exact (degree z x (fun e => xh (e ▸ zh))).resolve_right
      (fun xHigh => xh (all x xo xHigh))
  · intro z zo
    by_cases zh : z∈H.vertices
    · exact .inr zh
    left
    by_contra ne
    have c := one_lt_card.mpr ⟨z,mem_sdiff.mpr ⟨out.mpr zo,zh⟩,x,member,ne⟩
    omega

/-- The lone outside vertex has exactly two pins if one-vertex deletion
does not disconnect the graph. -/
theorem singleton_pins_of_off_five_disconnected
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (xo : x∉p.support) (xh : x∉H.vertices)
    (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
    (few : (Pins p x).card≤2) :
    (Pins p x).card=2 ∧ ∀ z∉p.support,¬G.Adj x z := by
  classical
  have no (z : V) (zo : z∉p.support) : ¬G.Adj x z := by
    rcases whole z zo with rfl|zh
    · exact G.loopless _
    · exact fun za => xo (H.closed z zh x xh za.symm)
  let S : OmittedComponent p :=
    ⟨{x},by simp,(by intro z hz; have e : z=x := mem_singleton.mp hz; simpa only [e] using xo),
       (by intro z hz w _ zw; have e : z=x := mem_singleton.mp hz; subst z; exact not_not.mp (fun h => no w h zw)),
       (by
        intro v vm w wm
        have e : v=x := mem_singleton.mp vm
        have f : w=x := mem_singleton.mp wm
        subst v
        subst w
        exact ⟨.nil,by simp,by simp⟩)⟩
  have c := componentPins_card hp S 2 conn
  have sub : componentPins S⊆PinVertices p x := by
    intro z hz
    obtain ⟨inP,w,wS,a⟩ := mem_filter.mp hz
    have eq : w=x := mem_singleton.mp wS
    subst w
    obtain ⟨i,hi,e⟩ := pin_of_neighbor_mem hp xo (List.mem_toFinset.mp inP) a
    exact mem_image.mpr ⟨i,hi,e⟩
  have u := card_le_card sub
  rw [card_pinVertices hp] at u
  exact ⟨by omega,no⟩

#print axioms off_five_disconnected_shape
#print axioms singleton_pins_of_off_five_disconnected
end Graffiti189LongestPath.TwoCut.SmallOrderFour
