import HandleProjection
import LaminarMinima

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux HandleExtension HandleExtension.Edges.AtomicHitting
noncomputable section

/-- For exactly three inclusion-minimal three-cut shores, two
successive handles suffice to remove all nontrivial three-cuts.
The second handle uses one half of the first subdivided old edge
and an old edge in the third shore. This is a graph-domain theorem,
not a statement about transfer of factors through both handles. -/
theorem explicit_two_handles_for_three_minimal
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (min : MinBoundaryThree G)
    {A B C : Finset V} (ma : MinimalShore G A) (mb : MinimalShore G B) (mc : MinimalShore G C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (every : ∀s,MinimalShore G s→s=A ∨ s=B ∨ s=C)
    {a a' b b' d d' : V} (aa : G.Adj a a') (bb : G.Adj b b') (dd : G.Adj d d')
    (aA : a∈A) (a'A : a'∈A) (bB : b∈B) (b'B : b'∈B) (dC : d∈C) (d'C : d'∈C) :
    ∃ E : Edges G,∃ F : Edges E.host,SmallTrivial F.host
      ∧ E.a false=a ∧ E.b false=a' ∧ E.a true=b ∧ E.b true=b'
      ∧ F.a false=Sum.inl a ∧ F.b false=Sum.inr false
      ∧ F.a true=Sum.inl d ∧ F.b true=Sum.inl d'  := by
  classical
  let E : Edges G := {
    a := fun s=>if s then b else a
    b := fun s=>if s then b' else a'
    edge := by intro s; cases s <;> assumption
    separated := by
      intro s t z hs ht
      cases s <;> cases t
      · rfl
      · have za : z∈A := hs.elim (fun h=>h.symm ▸ aA) (fun h=>h.symm ▸ a'A)
        have zb : z∈B := ht.elim (fun h=>h.symm ▸ bB) (fun h=>h.symm ▸ b'B)
        exact (disjoint_left.mp ab za zb).elim
      · have za : z∈A := ht.elim (fun h=>h.symm ▸ aA) (fun h=>h.symm ▸ a'A)
        have zb : z∈B := hs.elim (fun h=>h.symm ▸ bB) (fun h=>h.symm ▸ b'B)
        exact (disjoint_left.mp ab za zb).elim
      · rfl
  }
  have ad : a≠d := fun h=>disjoint_left.mp ac (h ▸ aA : d∈A) dC
  have ad' : a≠d' := fun h=>disjoint_left.mp ac (h ▸ aA : d'∈A) d'C
  have retained : E.host.Adj (Sum.inl d) (Sum.inl d') := by
    refine ⟨dd,?_⟩
    rintro ⟨s,right⟩
    have hd := (E.pair_ends right).1
    cases s
    · have da : d∈A := hd.elim (fun h=>h.symm ▸ aA) (fun h=>h.symm ▸ a'A)
      exact disjoint_left.mp ac da dC
    · have db : d∈B := hd.elim (fun h=>h.symm ▸ bB) (fun h=>h.symm ▸ b'B)
      exact disjoint_left.mp bc db dC
  let F : Edges E.host := {
    a := fun s=>if s then Sum.inl d else Sum.inl a
    b := fun s=>if s then Sum.inl d' else Sum.inr false
    edge := by
      intro s
      cases s
      · exact Or.inl rfl
      · exact retained
    separated := by
      intro s t z hs ht
      cases s <;> cases t
      · rfl
      · rcases hs with h|h <;> rcases ht with e|e
        · exact (ad (Sum.inl.inj (h.symm.trans e))).elim
        · exact (ad' (Sum.inl.inj (h.symm.trans e))).elim
        · cases (h.symm.trans e)
        · cases (h.symm.trans e)
      · rcases hs with h|h <;> rcases ht with e|e
        · exact (ad (Sum.inl.inj (e.symm.trans h))).elim
        · cases (e.symm.trans h)
        · exact (ad' (Sum.inl.inj (e.symm.trans h))).elim
        · cases (e.symm.trans h)
      · rfl
  }
  refine ⟨E,F,cyclic_host_of_hitting F (E.cubic cub) ?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro c low non
  obtain ⟨small,tr⟩ := nontrivial_handle_cut_projects E c cub low non
  let h := Edges.oldColor c
  obtain ⟨ct,cf⟩ := both_colours_of_nontrivial tr
  have lower := min h ct cf
  change 3≤(boundary G h).card at lower
  change (boundary G h).card≤3 at small
  have equal : (boundary G h).card=3 := by omega
  let s := univ.filter (fun v=>h v=true)
  have sc : colourOf s=h := by
    funext z
    by_cases yes : h z=true
    · have zs : z∈s := mem_filter.mpr ⟨mem_univ _,yes⟩
      exact (colour_true.mpr zs).trans yes.symm
    · have zn : z∉s := fun hm=>yes (mem_filter.mp hm).2
      exact (colour_false.mpr zn).trans (Bool.eq_false_iff.mpr yes).symm
  have sh : ShoreThree G s := by
    unfold ShoreThree
    rw [sc]
    exact ⟨equal,tr⟩
  have hue {K : Finset V} (m : MinimalShore G K) {p q : V} (pK : p∈K) (qK : q∈K) :
      h p=h q := by
    rcases minimal_wholly_on_one_side G min m sh with inside|out
    · exact ((mem_filter.mp (inside pK)).2).trans ((mem_filter.mp (inside qK)).2).symm
    · have off (x : V) (xK : x∈K) : h x=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        exact (mem_compl.mp (out xK)) (mem_filter.mpr ⟨mem_univ _,yes⟩)
      exact (off p pK).trans (off q qK).symm
  have mono : ∀ k,Edges.oldColor c (E.a k)=Edges.oldColor c (E.b k) := by
    intro k
    cases k
    · exact hue ma aA a'A
    · exact hue mb bB b'B
  obtain ⟨insert,abSame⟩ := no_new_crossing_in_tight_handle_cut E c low equal mono
  have same : h a=h b := abSame
  have dcOpp : h d≠h a := by
    intro dc
    by_cases ha : h a=true
    · obtain ⟨K,mK,ks⟩ := exists_minimal_below G (shore_compl G sh)
      have forbidden (v : V) (vK : v∈K) (yes : h v=true) : False :=
        (mem_compl.mp (ks vK)) (mem_filter.mpr ⟨mem_univ _,yes⟩)
      rcases every K mK with ea|eb|ec
      · exact forbidden a (ea.symm ▸ aA) ha
      · exact forbidden b (eb.symm ▸ bB) (same.symm.trans ha)
      · exact forbidden d (ec.symm ▸ dC) (dc.trans ha)
    · obtain ⟨K,mK,ks⟩ := exists_minimal_below G sh
      have required (v : V) (vK : v∈K) : h v=true := (mem_filter.mp (ks vK)).2
      rcases every K mK with ea|eb|ec
      · exact ha (required a (ea.symm ▸ aA))
      · exact ha (same.trans (required b (eb.symm ▸ bB)))
      · exact ha (dc.symm.trans (required d (ec.symm ▸ dC)))
  have dFlip := bool_not_eq_of_distinct dcOpp
  have eMono := hue mc dC d'C
  refine ⟨lower.trans (E.boundary_mono c),h a,?_,?_⟩
  · intro v hv
    rcases hv with e|e
    · exact e.symm ▸ (rfl : c (Sum.inl a)=h a)
    · exact e.symm ▸ insert false
  · intro v hv
    rcases hv with e|e
    · exact e.symm ▸ dFlip
    · exact e.symm ▸ (eMono.symm.trans dFlip)

theorem two_handles_for_three_minimal
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (min : MinBoundaryThree G)
    {A B C : Finset V} (ma : MinimalShore G A) (mb : MinimalShore G B) (mc : MinimalShore G C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (every : ∀s,MinimalShore G s→s=A ∨ s=B ∨ s=C)
    {a a' b b' d d' : V} (aa : G.Adj a a') (bb : G.Adj b b') (dd : G.Adj d d')
    (aA : a∈A) (a'A : a'∈A) (bB : b∈B) (b'B : b'∈B) (dC : d∈C) (d'C : d'∈C) :
    ∃ E : Edges G,∃ F : Edges E.host,SmallTrivial F.host := by
  obtain ⟨E,F,small,_⟩ := explicit_two_handles_for_three_minimal cub min ma mb mc ab ac bc every
    aa bb dd aA a'A bB b'B dC d'C
  exact ⟨E,F,small⟩

#print axioms explicit_two_handles_for_three_minimal
#print axioms two_handles_for_three_minimal
end
end KelmansCactus.AtomicBridge.OddUncross
