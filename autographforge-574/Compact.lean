import Row574

namespace EulerDom574.Compact
open SimpleGraph Finset TriangleMatching1078 AutoGraphForge378 Graffiti326

abbrev V := Fin 10
/-- 01 and 23 are the core edges. Vertices 4–9 are degree-two connectors. -/
def edges : List (V × V) :=
  [(0,1),(2,3),(0,4),(3,4),(2,5),(1,5),(0,6),(2,6),(0,7),(3,7),(1,8),(2,8),(1,9),(3,9)]
def rel (a b : V) := (a,b) ∈ edges ∨ (b,a) ∈ edges
instance : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
def g : SimpleGraph V where
  Adj := rel
  symm := fun _ _ h => h.symm
  loopless := by change ∀ a, ¬ rel a a; decide
instance : DecidableRel g.Adj := inferInstanceAs (DecidableRel rel)

theorem connected : g.Connected := by
  have paths : ∀ v : V, v=0 ∨ rel v 0 ∨ (∃ a, rel v a ∧ rel a 0) ∨
      ∃ a b, rel v a ∧ rel a b ∧ rel b 0 := by decide
  have reach (v : V) : g.Reachable v 0 := by
    rcases paths v with e|e|⟨a,h,j⟩|⟨a,b,h,j,k⟩
    · subst v; exact Reachable.rfl
    · exact (show g.Adj v 0 from e).reachable
    · exact (show g.Adj v a from h).reachable.trans (show g.Adj a 0 from j).reachable
    · exact (show g.Adj v a from h).reachable.trans
        ((show g.Adj a b from j).reachable.trans (show g.Adj b 0 from k).reachable)
  exact ⟨fun u v => (reach u).trans (reach v).symm⟩

theorem triangleFree : TriangleFree g := by unfold TriangleFree; decide
theorem degrees : ∀ v : V, g.degree v = 2 ∨ g.degree v = 4 := by decide

private def tag : Fin 2 × Bool → V := fun (i,b) =>
  if i=0 then (if b then 1 else 0) else (if b then 3 else 2)
theorem paired : HasMaximalMatching g 2 := by
  have inject : ∀ a b, tag a = tag b → a=b := by decide
  let f : Fin 2 × Bool ↪ V := ⟨tag,fun _ _ h => inject _ _ h⟩
  have cover : ∀ u v : V, g.Adj u v → (∃ i b, tag (i,b)=u) ∨ ∃ i b, tag (i,b)=v := by decide
  refine ⟨f,by change ∀ i, rel (tag (i,false)) (tag (i,true)); decide,?_⟩
  intro u hu v hv e
  rcases cover u v e with h|h
  · exact hu ((Graffiti326.mem_support f).mpr h)
  · exact hv ((Graffiti326.mem_support f).mpr h)

theorem lower : 3 ≤ domination g := by
  obtain ⟨S,sz,dom⟩ := attained g
  by_contra! small
  obtain ⟨T,sub,count⟩ := exists_superset_card_eq (show S.card ≤ 2 by omega) (by decide)
  obtain ⟨a,b,_,eq⟩ := card_eq_two.mp count
  have missed : ∀ a b : V, ∃ v, v≠a ∧ v≠b ∧ ¬g.Adj v a ∧ ¬g.Adj v b := by decide
  obtain ⟨v,va,vb,na,nb⟩ := missed a b
  have which {u : V} (h : u ∈ S) : u=a ∨ u=b := by
    have := sub h
    simpa [eq] using this
  rcases dom v with h|⟨u,h,vu⟩
  · exact (which h).elim va vb
  · rcases which h with rfl|rfl
    · exact na vu
    · exact nb vu

theorem witness : 2 ≤ Fintype.card V ∧ g.Connected ∧ (∀ v, Even (g.degree v)) ∧
    TriangleFree g ∧ domination g=3 ∧ lineDomination g=2 ∧ minMaximalMatching g=2 := by
  have hd (v : V) : 2 ≤ g.degree v := by rcases degrees v with h|h <;> omega
  have hmin := (g.le_minDegree_of_forall_le_degree 2 hd).trans (minDegree_le_lineDomination g triangleFree)
  have hcmp := lineDomination_le_matching g
  have hm : minMaximalMatching g ≤ 2 := Nat.sInf_le paired
  have h := upper g hd
  exact ⟨by decide,connected,fun v => by rcases degrees v with h|h <;> rw [h] <;> decide,
    triangleFree,by have := lower; omega,by omega,by omega⟩

#print axioms witness
end EulerDom574.Compact
