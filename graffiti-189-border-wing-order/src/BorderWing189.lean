import WideWing189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.WideWing
open Graffiti189LongestPath.Rigidity
open private Graffiti189LongestPath.WideWing.inside_deg
  Graffiti189LongestPath.WideWing.terminalOre from WideWing189
set_option warningAsError true
namespace Graffiti189LongestPath.BorderWing
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
private lemma induced_erase_degree (S : Finset V) {v t : V} (hv : v∈S.erase t) :
    (G.induce (S : Set V)).degree ⟨v,(mem_erase.mp hv).2⟩ ≤
    (G.induce ((S.erase t : Finset V) : Set V)).degree ⟨v,hv⟩ + 1 := by
  classical
  let P := G.induce (S : Set V)
  let Q := G.induce ((S.erase t : Finset V) : Set V)
  let u : ↥(S : Set V) := ⟨v,(mem_erase.mp hv).2⟩
  let w : ↥((S.erase t : Finset V) : Set V) := ⟨v,hv⟩
  let N := (P.neighborFinset u).filter (fun q => q.val ≠ t)
  let M := (P.neighborFinset u).filter (fun q => q.val = t)
  have m : M.card ≤ 1 := by
    apply Nat.le_of_not_gt
    intro h
    obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp h
    exact ne (Subtype.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm))
  have split : P.neighborFinset u ⊆ N ∪ M := by
    intro a ha
    by_cases e : a.val=t
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨ha,e⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨ha,e⟩))
  have n : N.card ≤ (Q.neighborFinset w).card := by
    let f (a : ↥(S : Set V)) : ↥((S.erase t : Finset V) : Set V) :=
      if h : a.val ≠ t then ⟨a.val,mem_erase.mpr ⟨h,a.property⟩⟩ else w
    apply card_le_card_of_injOn f
    · intro a ha
      have h := (mem_filter.mp ha).2
      simpa only [f,dif_pos h] using
        (Q.mem_neighborFinset w ⟨a.val,mem_erase.mpr ⟨h,a.property⟩⟩).mpr
          ((P.mem_neighborFinset u a).mp (mem_filter.mp ha).1)
    · intro a ha b hb e
      have ha' : a∈N := ha
      have hb' : b∈N := hb
      have h := (mem_filter.mp ha').2
      have h' := (mem_filter.mp hb').2
      exact Subtype.ext (by simpa only [f,dif_pos h,dif_pos h'] using congrArg Subtype.val e)
  have cs := card_le_card split
  have cu := card_union_le N M
  rw [P.card_neighborFinset_eq_degree] at cs
  rw [Q.card_neighborFinset_eq_degree] at n
  change P.degree u ≤ Q.degree w+1
  omega

/-- One vertex beyond the terminal Ore range, even the single exceptional
vertex costs at most one vertex of a prescribed-terminal path. -/
theorem near_border_routes {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (d : Nat) (hd : 6≤d)
    (low : ∀ x ∈ H.vertices, d-2≤G.degree x)
    (high : ∀ x y : V, x≠y → d≤G.degree x ∨ d≤G.degree y)
    (few : ∀ x∈H.vertices, (Pins p x).card≤2)
    (small : H.vertices.card+6≤2*d)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices) (ne : x≠y) :
    ∃ q : G.Walk x y, q.IsPath ∧ (∀ w∈q.support, w∈H.vertices) ∧ H.vertices.card≤q.length+2 := by
  classical
  by_cases hl : ∃ t∈H.vertices, G.degree t<d
  swap
  · have H' : ∀ z∈H.vertices, d+2-2≤G.degree z := by
      intro z hz
      have h : d≤G.degree z := Nat.le_of_not_gt (fun h => hl ⟨z,hz,h⟩)
      omega
    -- All vertices are high, so the original terminal Ore bound is stronger.
    let J := G.induce (H.vertices : Set V)
    let u : ↥(H.vertices : Set V) := ⟨x,hx⟩
    let v : ↥(H.vertices : Set V) := ⟨y,hy⟩
    have cc : Fintype.card ↥(H.vertices : Set V) = H.vertices.card := Fintype.card_coe _
    have hdeg (s t : ↥(H.vertices : Set V)) (_ : s≠t) (_ : ¬J.Adj s t) :
        Fintype.card ↥(H.vertices : Set V)+1≤J.degree s+J.degree t := by
      have c₁ := H' s.val s.property
      have c₂ := H' t.val t.property
      have f₁ := few s.val s.property
      have f₂ := few t.val t.property
      have a₁ := Graffiti189LongestPath.WideWing.inside_deg hp H s
      have a₂ := Graffiti189LongestPath.WideWing.inside_deg hp H t
      change G.degree s.val≤(Pins p s.val).card+J.degree s at a₁
      change G.degree t.val≤(Pins p t.val).card+J.degree t at a₂
      omega
    obtain ⟨q,hq,all⟩ := Graffiti189LongestPath.WideWing.terminalOre (G:=J) hdeg
      (show u≠v from fun h => ne (congrArg Subtype.val h))
    let f : J →g G := ⟨Subtype.val,fun e => e⟩
    refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective hq,?_,?_⟩
    · intro w hw
      rw [support_map] at hw
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp hw
      exact s.property
    · have es : q.support.toFinset = univ := ext fun w =>
        ⟨fun _ => mem_univ _,fun _ => List.mem_toFinset.mpr (all w)⟩
      have c := congrArg card es
      rw [List.toFinset_card_of_nodup hq.support_nodup,length_support,card_univ,cc] at c
      simpa only [length_map] using (show H.vertices.card ≤ q.length+2 by omega)
  obtain ⟨t,ht,dt⟩ := hl
  let R := H.vertices.erase t
  let J := G.induce (R : Set V)
  have cc : Fintype.card ↥(R : Set V) = R.card := Fintype.card_coe _
  have rr : R.card+1=H.vertices.card := card_erase_add_one ht
  have hdeg (s v : ↥(R : Set V)) (_ : s≠v) (_ : ¬J.Adj s v) :
      Fintype.card ↥(R : Set V)+1≤J.degree s+J.degree v := by
    have aux (w : ↥(R : Set V)) : d-3≤J.degree w := by
      have wn := (mem_erase.mp w.property).1
      have wh := (mem_erase.mp w.property).2
      have dg := (high w.val t wn).resolve_right (Nat.not_le_of_lt dt)
      have f := few w.val wh
      have inn := Graffiti189LongestPath.WideWing.inside_deg hp H ⟨w,wh⟩
      have del := induced_erase_degree (G:=G) H.vertices w.property
      change (G.induce (H.vertices : Set V)).degree ⟨w,wh⟩ ≤ J.degree w+1 at del
      change G.degree w.val ≤ (Pins p w.val).card + (G.induce (H.vertices : Set V)).degree ⟨w,wh⟩ at inn
      omega
    have hs := aux s
    have hv := aux v
    omega
  have old (u v : V) (hu : u∈R) (hv : v∈R) (ne : u≠v) :
      ∃ q : G.Walk u v, q.IsPath ∧ (∀ w∈q.support, w∈R) ∧ q.length+1=R.card := by
    let u' : ↥(R : Set V) := ⟨u,hu⟩
    let v' : ↥(R : Set V) := ⟨v,hv⟩
    obtain ⟨q,hq,all⟩ := Graffiti189LongestPath.WideWing.terminalOre (G:=J) hdeg
      (show u'≠v' from fun h => ne (congrArg Subtype.val h))
    let f : J →g G := ⟨Subtype.val,fun e => e⟩
    refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective hq,?_,?_⟩
    · intro w hw
      rw [support_map] at hw
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp hw
      exact s.property
    · have e : q.support.toFinset = univ := ext fun w =>
        ⟨fun _ => mem_univ _,fun _ => List.mem_toFinset.mpr (all w)⟩
      have c := congrArg card e
      rw [List.toFinset_card_of_nodup hq.support_nodup,length_support,card_univ,cc] at c
      simpa only [length_map] using c
  have fromLow (u : V) (hu : u∈H.vertices) (nu : u≠t) :
      ∃ q : G.Walk t u, q.IsPath ∧ (∀ w∈q.support, w∈H.vertices) ∧ H.vertices.card≤q.length+2 := by
    let L := G.induce (H.vertices : Set V)
    let t' : ↥(H.vertices : Set V) := ⟨t,ht⟩
    have inn := Graffiti189LongestPath.WideWing.inside_deg hp H t'
    have f := few t ht
    have l := low t ht
    change G.degree t≤(Pins p t).card+L.degree t' at inn
    have two : 1<(L.neighborFinset t').card := by rw [L.card_neighborFinset_eq_degree]; omega
    obtain ⟨r,hr,s,hs,rs⟩ := one_lt_card.mp two
    obtain ⟨w,hw,eq⟩ : ∃ w∈L.neighborFinset t', w.val≠u := by
      by_cases e : r.val=u
      · exact ⟨s,hs,fun f => rs (Subtype.ext (e.trans f.symm))⟩
      · exact ⟨r,hr,e⟩
    have e : G.Adj t w.val := (L.mem_neighborFinset t' w).mp hw
    obtain ⟨q,hq,supp,long⟩ := old w.val u
      (mem_erase.mpr ⟨e.ne.symm,w.property⟩) (mem_erase.mpr ⟨nu,hu⟩) eq
    refine ⟨Walk.cons e q,?_,?_,?_⟩
    · rw [cons_isPath_iff]
      exact ⟨hq,fun h => (mem_erase.mp (supp _ h)).1 rfl⟩
    · intro w hw
      rw [support_cons,List.mem_cons] at hw
      exact hw.elim (fun e => e.symm ▸ ht) (fun h => (mem_erase.mp (supp _ h)).2)
    · simp only [length_cons]
      omega
  by_cases xe : x=t
  · subst x
    exact fromLow y hy ne.symm
  by_cases ye : y=t
  · subst y
    obtain ⟨q,hq,supp,long⟩ := fromLow x hx ne
    exact ⟨q.reverse,hq.reverse,fun w hw => supp w (by simpa using hw),by simpa using long⟩
  obtain ⟨q,hq,supp,long⟩ := old x y (mem_erase.mpr ⟨xe,hx⟩) (mem_erase.mpr ⟨ye,hy⟩) ne
  exact ⟨q,hq,fun w hw => (mem_erase.mp (supp w hw)).2,by omega⟩

theorem near_border_gap {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (d : Nat) (hd : 6≤d)
    (low : ∀ x ∈ H.vertices, d-2≤G.degree x)
    (high : ∀ x y : V, x≠y → d≤G.degree x ∨ d≤G.degree y)
    (few : ∀ x∈H.vertices, (Pins p x).card≤2)
    (small : H.vertices.card+6≤2*d)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices) (ne : x≠y)
    {i j : Nat} (hi : i∈Pins p x) (hj : j∈Pins p y) (lt : i<j) :
    i+H.vertices.card≤j := by
  obtain ⟨q,hq,off,len⟩ := near_border_routes hp H d hd low high few small hx hy ne
  have g := terminal_length_le_gap hp hi hj lt q hq (fun w hw => H.off w (off w hw))
  omega
#print axioms near_border_gap
end Graffiti189LongestPath.BorderWing
