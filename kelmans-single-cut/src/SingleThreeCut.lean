import HandleHitting

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open HandleExtension HandleExtension.Edges.AtomicHitting FourRingCutAux FourRingCyclicEquivalence
noncomputable section
universe u

def TrivialCut {V : Type*} (c : V→Bool) : Prop :=
    (∀ x y,c x=true→c y=true→x=y) ∨ (∀ x y,c x=false→c y=false→x=y)

private theorem true_has_edge {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (cub : ∀v,G.degree v=3) (c : V→Bool)
    (small : (boundary G c).card≤3) (non : ¬TrivialCut c) :
    ∃ x y,c x=true ∧ c y=true ∧ G.Adj x y := by
  classical
  have acy : ¬(shoreGraph G c).IsAcyclic := by
    intro ac
    apply non
    left
    intro x y h k
    by_contra ne
    have large := acyclic_shore_large_cut G c cub ac h k ne
    omega
  by_contra e
  have none : shoreGraph G c=⊥ := by
    ext x y
    constructor
    · intro ed
      exact (e ⟨x.val,y.val,x.property,y.property,ed⟩).elim
    · intro ed
      exact ed.elim
  exact acy (none.symm ▸ isAcyclic_bot)

/-- If there is just one nontrivial minimum cut up to switching its
shores, plain cyclic-four Kelmans would imply a factor of this graph.
The hypothesis is on all actual cuts, not a designated decomposition. -/
theorem cyclic4_factor_implies_single_three_cut
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (promise : CyclicUniversal.{u}) (cub : ∀v,G.degree v=3) (dvd : 6∣Fintype.card V)
    (c : V→Bool) (sz : (boundary G c).card=3) (non : ¬TrivialCut c)
    (unique : ∀ k : V→Bool,(boundary G k).card≤3→¬TrivialCut k →
      k=c ∨ k=(fun x=> !(c x))) : KelmansStarter.HasP3Factor G := by
  classical
  obtain ⟨a,b,aT,bT,ab⟩ := true_has_edge cub c sz.le non
  let f : V→Bool := fun x=> !(c x)
  have sf : (boundary G f).card≤3 := (boundary_flip_card G c).trans sz |>.le
  have nf : ¬TrivialCut f := by
    intro s
    apply non
    rcases s with h|h
    · right
      intro x y xf yf
      exact h _ _ (by simp [f,xf]) (by simp [f,yf])
    · left
      intro x y xt yt
      exact h _ _ (by simp [f,xt]) (by simp [f,yt])
  obtain ⟨p,q,pT,qT,pq⟩ := true_has_edge cub f sf nf
  have pF : c p=false := by simpa [f] using pT
  have qF : c q=false := by simpa [f] using qT
  let E : Edges G := {
    a := fun s=>if s then p else a
    b := fun s=>if s then q else b
    edge := by intro s; cases s <;> assumption
    separated := by
      intro s t x hs ht
      cases s <;> cases t
      · rfl
      · have ct : c x=true := hs.elim (fun h=>h.symm ▸ aT) (fun h=>h.symm ▸ bT)
        have cf : c x=false := ht.elim (fun h=>h.symm ▸ pF) (fun h=>h.symm ▸ qF)
        exact (Bool.false_ne_true (cf.symm.trans ct)).elim
      · have cf : c x=false := hs.elim (fun h=>h.symm ▸ pF) (fun h=>h.symm ▸ qF)
        have ct : c x=true := ht.elim (fun h=>h.symm ▸ aT) (fun h=>h.symm ▸ bT)
        exact (Bool.false_ne_true (cf.symm.trans ct)).elim
      · rfl
  }
  have on (x : V) (h : E.Ends false x) : c x=true :=
    h.elim (fun h=>h.symm ▸ aT) (fun h=>h.symm ▸ bT)
  have off (x : V) (h : E.Ends true x) : c x=false :=
    h.elim (fun h=>h.symm ▸ pF) (fun h=>h.symm ▸ qF)
  have hit : HitsSmallCuts E := by
    intro k lo bad
    rcases unique k lo bad with rfl|rfl
    · exact ⟨sz.ge,true,on,off⟩
    · refine ⟨((boundary_flip_card G c).trans sz).ge,false,?_,?_⟩
      · intro x hx
        simp [on x hx]
      · intro x hx
        simp [off x hx]
  have sub : E.deleteChosen≤G := fun _ _ edge=>edge.1
  exact HandleExtension.factor_mono sub
    (factor_avoids_hitting_pair E promise cub dvd hit)

/-- A single handle cannot eliminate three disjoint nontrivial small
shores. It has only two chosen independent old edges. -/
theorem three_disjoint_shores_block_hitting
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (E : Edges G) (C : Fin 3→V→Bool)
    (small : ∀ i,(boundary G (C i)).card≤3) (non : ∀ i,¬TrivialCut (C i))
    (disj : ∀ i j, i≠j → ∀ v, C i v=true → C j v=true → False) :
    ¬HitsSmallCuts E := by
  classical
  intro hit
  have choose_side (i : Fin 3) : ∃ s,C i (E.a s)=true := by
    obtain ⟨_,b,h,k⟩ := hit (C i) (small i) (non i)
    cases hk : b
    · exact ⟨true,(k _ (Or.inl rfl)).trans (by simp [hk])⟩
    · exact ⟨false,(h _ (Or.inl rfl)).trans hk⟩
  choose pick ok using choose_side
  have inj : Function.Injective pick := by
    intro i j e
    by_contra ne
    exact disj i j ne _ (ok i) (e.symm ▸ ok j)
  have size := Fintype.card_le_of_injective pick inj
  simp at size

#print axioms three_disjoint_shores_block_hitting
#print axioms cyclic4_factor_implies_single_three_cut
end
end KelmansCactus.AtomicBridge
