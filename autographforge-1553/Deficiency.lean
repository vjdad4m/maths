import HallRainbow
import Cover
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum

namespace RainbowCover1553
open Finset SimpleGraph HallRainbow1121 BullCover1125
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]

/-- Only edges from a selected vertex to the outside contribute to its load. -/
def crossExcess (S : Finset V) (k : ℕ) :=
  ∑ u ∈ S, (((G.neighborFinset u) \ S).card - k)

/-- A graph-wide estimate independent of the choice of labels. -/
def degreeExcess (k : ℕ) := ∑ u : V, (G.degree u - k)

theorem cross_le_degree_excess (S : Finset V) (k : ℕ) : crossExcess G S k ≤ degreeExcess G k := by
  calc
    _ ≤ ∑ u ∈ S, (G.degree u - k) := sum_le_sum (fun _ _ => Nat.sub_le_sub_right (card_le_card sdiff_subset) k)
    _ ≤ _ := sum_le_sum_of_subset (subset_univ S)

/-- If each outside vertex sees k vertices of S, the Hall deficiency of every
outside subset is at most the total excess load divided by k. -/
theorem deficiency (S : Finset V) {k : ℕ} (hk : 0 < k)
    (demand : ∀ v ∉ S, k ≤ (S.filter (G.Adj v)).card) (X : Finset {v // v ∉ S}) :
    X.card ≤ (X.biUnion (fun w => S.filter (G.Adj w.val))).card + crossExcess G S k / k := by
  classical
  let N := X.biUnion (fun w => S.filter (G.Adj w.val))
  let R (w : {v // v ∉ S}) (u : V) := G.Adj w.val u
  have sub : N ⊆ S := by
    intro u hu
    obtain ⟨w,_,hw⟩ := mem_biUnion.mp hu
    exact (mem_filter.mp hw).1
  have left (w) (hw : w ∈ X) : k ≤ (N.bipartiteAbove R w).card := by
    apply (demand w.val w.property).trans (card_le_card ?_)
    intro u hu
    exact (mem_bipartiteAbove _).mpr ⟨mem_biUnion.mpr ⟨w,hw,hu⟩,(mem_filter.mp hu).2⟩
  let load (u : V) := ((G.neighborFinset u) \ S).card
  have right (u : V) : (X.bipartiteBelow R u).card ≤ k + (load u-k) := by
    have cap : (X.bipartiteBelow R u).card ≤ load u := by
      apply card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
      intro w hw
      exact mem_sdiff.mpr ⟨(G.mem_neighborFinset u w.val).mpr ((mem_bipartiteBelow _).mp hw).2.symm,
        w.property⟩
    omega
  have sumEx : (∑ u ∈ N, (load u-k)) ≤ crossExcess G S k := sum_le_sum_of_subset sub
  have bound : X.card*k ≤ N.card*k + crossExcess G S k := calc
    _ = ∑ _ ∈ X, k := by simp
    _ ≤ ∑ w ∈ X, (N.bipartiteAbove R w).card := sum_le_sum left
    _ = ∑ u ∈ N, (X.bipartiteBelow R u).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ u ∈ N, (k+(load u-k)) := sum_le_sum (fun u _ => right u)
    _ = N.card*k + ∑ u ∈ N, (load u-k) := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left sumEx _
  have diff : (X.card - N.card) * k ≤ crossExcess G S k := by
    rw [Nat.sub_mul]
    omega
  have div := (Nat.le_div_iff_mul_le hk).mpr diff
  change X.card ≤ N.card + _
  omega

/-- Dummy representatives in Hall's theorem account for the uncovered outside
vertices. Each real slot or occupied dummy slot costs at most one incident edge. -/
theorem edge_cover_of_deficit (iso : IsolateFree G) (S : Finset V) (d : ℕ)
    (bound : ∀ X : Finset {v // v ∉ S},
      X.card ≤ (X.biUnion (fun w => S.filter (G.Adj w.val))).card + d) :
    edgeCoverNumber G ≤ S.card + d := by
  classical
  let W := {v // v ∉ S}
  let N (w : W) := S.filter (G.Adj w.val)
  let choices (w : W) : Finset (V ⊕ Fin d) := (N w).disjSum univ
  have hall (X : Finset W) : X.card ≤ (X.biUnion choices).card := by
    rcases X.eq_empty_or_nonempty with rfl|hne
    · simp
    · have eq : X.biUnion choices = (X.biUnion N).disjSum (univ : Finset (Fin d)) := by
        ext z
        rcases z with u|j
        · simp [choices]
        · simpa [choices] using hne
      simpa [eq,N] using bound X
  obtain ⟨mate,inj,good⟩ := (all_card_le_biUnion_card_iff_existsInjective' choices).mp hall
  have real {w : W} {u : V} (eq : mate w = Sum.inl u) : u ∈ S ∧ G.Adj w.val u := by
    have h := good w
    simpa [choices,N,eq] using h
  have incident (v : V) : ∃ e : G.edgeSet, v ∈ e.val := by
    obtain ⟨u,vu⟩ := iso v
    exact ⟨⟨s(v,u),vu⟩,Sym2.mem_iff.mpr (Or.inl rfl)⟩
  let slots := S.disjSum (univ : Finset (Fin d))
  have piece (q : V ⊕ Fin d) : ∃ P : Finset G.edgeSet, P.card ≤ 1 ∧
      (∀ u : V, q = Sum.inl u → ∃ e ∈ P, u ∈ e.val) ∧
      (∀ w : W, mate w = q → ∃ e ∈ P, w.val ∈ e.val) := by
    rcases q with u|j
    · by_cases used : ∃ w, mate w = Sum.inl u
      · obtain ⟨w,hw⟩ := used
        let e : G.edgeSet := ⟨s(w.val,u),(real hw).2⟩
        refine ⟨{e},by simp,?_,?_⟩
        · rintro v eq
          exact ⟨e,mem_singleton_self _,Sum.inl.inj eq ▸ Sym2.mem_iff.mpr (Or.inr rfl)⟩
        · intro v hv
          have eq := inj (hv.trans hw.symm)
          exact ⟨e,mem_singleton_self _,eq ▸ Sym2.mem_iff.mpr (Or.inl rfl)⟩
      · obtain ⟨e,hu⟩ := incident u
        exact ⟨{e},by simp,fun v eq => ⟨e,mem_singleton_self _,Sum.inl.inj eq ▸ hu⟩,
          fun w hw => False.elim (used ⟨w,hw⟩)⟩
    · by_cases used : ∃ w, mate w = Sum.inr j
      · obtain ⟨w,hw⟩ := used
        obtain ⟨e,he⟩ := incident w.val
        refine ⟨{e},by simp,fun _ eq => Sum.noConfusion eq,?_⟩
        intro v hv
        exact ⟨e,mem_singleton_self _,inj (hv.trans hw.symm) ▸ he⟩
      · exact ⟨∅,by simp,fun _ eq => Sum.noConfusion eq,fun w hw => False.elim (used ⟨w,hw⟩)⟩
  choose P cost inside outside using piece
  have covers : Covers G (slots.biUnion P) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨e,he,ve⟩ := inside (Sum.inl v) v rfl
      exact ⟨e,mem_biUnion.mpr ⟨Sum.inl v,by simpa [slots] using hv,he⟩,ve⟩
    · let w : W := ⟨v,hv⟩
      obtain ⟨e,he,ve⟩ := outside (mate w) w rfl
      have slot : mate w ∈ slots := by
        cases eq : mate w with
        | inl u => simpa [slots] using (real eq).1
        | inr j => simp [slots]
      exact ⟨e,mem_biUnion.mpr ⟨mate w,slot,he⟩,ve⟩
  apply (Nat.sInf_le (s:={n | ∃ P : Finset G.edgeSet, P.card=n ∧ Covers G P})
    ⟨slots.biUnion P,rfl,covers⟩).trans
  calc
    _ ≤ ∑ q ∈ slots, (P q).card := card_biUnion_le
    _ ≤ ∑ _ ∈ slots, 1 := sum_le_sum fun q _ => cost q
    _ = _ := by simp [slots]

theorem cover_of_k_dominating (iso : IsolateFree G) (S : Finset V) {k : ℕ} (hk : 0 < k)
    (demand : ∀ v ∉ S, k ≤ (S.filter (G.Adj v)).card) :
    edgeCoverNumber G ≤ S.card + crossExcess G S k / k :=
  edge_cover_of_deficit G iso S _ (deficiency G S hk demand)

end RainbowCover1553
