import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Max

/-! Written on the Wall II, #318 (open in the November 2026 catalogue).
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
The right-hand side is the number of edges of the complement, not of G.
The proof establishes a stronger criterion: deleting one vertex leaves
a graph in which every vertex has at most one nonneighbor. -/

namespace Graffiti318
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def TotalDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x, ∃ y ∈ S, G.Adj x y

def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, TotalDominating G S →
    (∀ T ⊆ S, TotalDominating G T → T = S) →
      ∀ T : Finset V, TotalDominating G T → S.card ≤ T.card

omit [Fintype V] in
private theorem total_dom_card_ge_two {G : SimpleGraph V} [Nonempty V]
    {T : Finset V} (hT : TotalDominating G T) : 2 ≤ T.card := by
  obtain ⟨a,ha,_⟩ := hT (Classical.choice ‹Nonempty V›)
  obtain ⟨b,hb,he⟩ := hT a
  have h : ({a,b} : Finset V) ⊆ T := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ha
    · simpa only [mem_singleton.mp hz] using hb
  have hh := card_le_card h
  simpa [he.ne] using hh

omit [Fintype V] in
/-- If outside v each vertex has at most one distinct nonneighbor outside v,
then every total dominating set contains a total dominating pair. -/
theorem wellTotalDominated_of_complement_matching_after_delete {G : SimpleGraph V} (v : V)
    (huniq : ∀ a x y, a ≠ v → x ≠ v → y ≠ v → a ≠ x → a ≠ y →
      ¬ G.Adj a x → ¬ G.Adj a y → x = y) : WellTotalDominated G := by
  classical
  letI : Nonempty V := ⟨v⟩
  intro S hS hmin T hT
  obtain ⟨a,ha,hva⟩ := hS v
  have ha0 : a ≠ v := hva.ne.symm
  have hpair (x : V) (hx : x ∈ S) (hax : G.Adj a x)
      (hdom : TotalDominating G ({a,x} : Finset V)) : S.card ≤ T.card := by
    have hsub : ({a,x} : Finset V) ⊆ S := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · simpa only [mem_singleton.mp hz] using hx
    rw [← hmin _ hsub hdom]
    simpa [hax.ne] using total_dom_card_ge_two hT
  by_cases hgood : ∃ x ∈ S, x ≠ v ∧ G.Adj a x
  · obtain ⟨x,hx,hx0,hax⟩ := hgood
    apply hpair x hx hax
    intro z
    by_cases hz : z = v
    · subst z
      exact ⟨a,by simp,hva⟩
    by_cases hza : G.Adj z a
    · exact ⟨a,by simp,hza⟩
    by_cases hzx : G.Adj z x
    · exact ⟨x,by simp,hzx⟩
    exfalso
    have hne1 : z ≠ a := fun he => hzx (he.symm ▸ hax)
    have hne2 : z ≠ x := fun he => hza (he.symm ▸ hax.symm)
    exact hax.ne (huniq z a x hz ha0 hx0 hne1 hne2 hza hzx)
  · obtain ⟨x,hx,hax⟩ := hS a
    have exv : x = v := by
      by_cases hne : x = v
      · exact hne
      · exact (hgood ⟨x,hx,hne,hax⟩).elim
    subst x
    apply hpair v hx hva.symm
    intro z
    by_cases hzv : G.Adj z v
    · exact ⟨v,by simp,hzv⟩
    by_cases hza : G.Adj z a
    · exact ⟨a,by simp,hza⟩
    exfalso
    have hz0 : z ≠ v := fun he => hza (he.symm ▸ hva)
    have hza' : a ≠ z := fun he => hzv (he ▸ hva.symm)
    obtain ⟨w,hw,hzw⟩ := hS z
    have hw0 : w ≠ v := fun he => hzv (he ▸ hzw)
    have hwa : a ≠ w := fun he => hza (he.symm ▸ hzw)
    have hna : ¬ G.Adj a w := fun he => hgood ⟨w,hw,hw0,he⟩
    exact hzw.ne (huniq a z w ha0 hz0 hw0 hza' hwa (fun he => hza he.symm) hna)

noncomputable def evenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact ((univ : Finset V).filter (fun x => G.dist v x % 2 = 0)).card

noncomputable def maxEven (G : SimpleGraph V) : ℕ :=
  (univ : Finset V).sup (evenCount G)

private theorem evenCount_le_compl_degree_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : evenCount G v ≤ Gᶜ.degree v + 1 := by
  classical
  let S := (univ : Finset V).filter (fun x => G.dist v x % 2 = 0)
  have hv : v ∈ S := by simp [S,SimpleGraph.dist_self]
  have hs : S.erase v ⊆ Gᶜ.neighborFinset v := by
    intro x hx
    obtain ⟨hn,hx'⟩ := mem_erase.mp hx
    have hd := (mem_filter.mp hx').2
    refine (Gᶜ.mem_neighborFinset _ _).mpr ((compl_adj G v x).mpr ⟨hn.symm,?_⟩)
    intro ha
    rw [dist_eq_one_iff_adj.mpr ha] at hd
    omega
  have hh := card_le_card hs
  have hcard := card_erase_add_one hv
  change S.card ≤ Gᶜ.degree v + 1
  rw [← hcard]
  exact Nat.add_le_add_right hh 1

/-- Exact full statement of Graffiti.pc #318. -/
theorem conjecture318 (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (_hn : 1 < Fintype.card V) (h : Gᶜ.edgeFinset.card ≤ maxEven G) :
    WellTotalDominated G := by
  classical
  letI := hc.nonempty
  obtain ⟨v,_,hv⟩ := exists_max_image univ (evenCount G) univ_nonempty
  have hm : maxEven G ≤ evenCount G v := Finset.sup_le_iff.mpr hv
  have hdeg := evenCount_le_compl_degree_add_one G v
  let R := Gᶜ.edgeFinset.filter (fun e => v ∉ e)
  have hsplit := filter_card_add_filter_neg_card_eq_card
    (s := Gᶜ.edgeFinset) (p := fun e => v ∈ e)
  rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree] at hsplit
  change Gᶜ.degree v + R.card = Gᶜ.edgeFinset.card at hsplit
  have hR : R.card ≤ 1 := by omega
  apply wellTotalDominated_of_complement_matching_after_delete v
  intro a x y ha hx hy hax hay hnax hnay
  have hxR : s(a,x) ∈ R := by
    refine mem_filter.mpr ⟨mem_edgeFinset.mpr ((compl_adj G a x).mpr ⟨hax,hnax⟩),?_⟩
    simp [ha.symm,hx.symm]
  have hyR : s(a,y) ∈ R := by
    refine mem_filter.mpr ⟨mem_edgeFinset.mpr ((compl_adj G a y).mpr ⟨hay,hnay⟩),?_⟩
    simp [ha.symm,hy.symm]
  have he := card_le_one.mp hR _ hxR _ hyR
  rcases Sym2.mk_eq_mk_iff.mp he with he | he
  · exact congrArg Prod.snd he
  · exact False.elim (hay (congrArg Prod.fst he))

#print axioms wellTotalDominated_of_complement_matching_after_delete
#print axioms conjecture318
end Graffiti318
