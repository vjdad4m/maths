import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 320

If the maximum even-distance count equals the minimum sum of distances,
a connected graph of order at least two has a universal vertex and a
pendant vertex adjacent to it. Every minimal total dominating set then
consists of the universal vertex and one other vertex.

The AI Village August 2026 catalogue audit already listed this entry among
the true results; the proof here is an independent Lean verification.
https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj309-false-one-hundred-fifty-nine
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti320
open SimpleGraph Finset
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def evenSet (H : SimpleGraph V) (r : V) : Finset V :=
  univ.filter fun v => H.dist r v % 2 = 0

def maxEven (H : SimpleGraph V) : ℕ :=
  univ.sup (fun r => (evenSet H r).card)

def transmission (H : SimpleGraph V) (r : V) : ℕ :=
  ∑ v ∈ (univ : Finset V).erase r, H.dist r v

def minTransmission (H : SimpleGraph V) : ℕ :=
  sInf (Set.range (transmission H))

def TotalDominates (H : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, H.Adj v w

def WellTotalDominated (H : SimpleGraph V) : Prop :=
  ∀ D, TotalDominates H D → (∀ E ⊆ D, TotalDominates H E → D ⊆ E) →
    ∀ E, TotalDominates H E → D.card ≤ E.card

private theorem has_neighbor (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (r : V) :
    ∃ w, G.Adj r w := by
  obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card (by omega) r
  obtain ⟨p⟩ := hc r t
  cases p with
  | nil => exact (ht rfl).elim
  | cons ha _ => exact ⟨_, ha⟩

private theorem evenSet_add_degree_le_order (r : V) :
    (evenSet G r).card + (G.neighborFinset r).card ≤ Fintype.card V := by
  have hdis : Disjoint (evenSet G r) (G.neighborFinset r) := by
    apply disjoint_left.mpr
    intro v hE hN
    have ha := (G.mem_neighborFinset _ _).mp hN
    have h := (mem_filter.mp hE).2
    rw [dist_eq_one_iff_adj.mpr ha] at h
    omega
  rw [← card_union_of_disjoint hdis]
  exact card_le_univ _

private theorem transmission_lower (hc : G.Connected) (r : V) :
    Fintype.card V - 1 ≤ transmission G r := by
  have h := Finset.sum_le_sum (s := (univ : Finset V).erase r)
    (fun a ha => Nat.succ_le_of_lt (hc.pos_dist_of_ne (Ne.symm (mem_erase.mp ha).1)))
  simpa [transmission, card_erase_of_mem (mem_univ r)] using h

theorem universal_and_pendant (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (heq : maxEven G = minTransmission G) :
    ∃ u p, G.Adj p u ∧ (∀ w, G.Adj p w → w=u) ∧ (∀ w, w≠u → G.Adj u w) := by
  haveI : Nonempty V := hc.nonempty
  obtain ⟨p,_,hp⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty
    (fun r => (evenSet G r).card)
  change maxEven G = (evenSet G p).card at hp
  obtain ⟨u,hu⟩ := Nat.sInf_mem (Set.range_nonempty (f := transmission G))
  change transmission G u = minTransmission G at hu
  obtain ⟨x,hpx⟩ := has_neighbor hc hn p
  have hx : x ∈ G.neighborFinset p := (G.mem_neighborFinset _ _).mpr hpx
  have hnbr := Finset.card_pos.mpr ⟨x,hx⟩
  have hcap := evenSet_add_degree_le_order (G := G) p
  have hlo := transmission_lower hc u
  have ht : transmission G u = Fintype.card V - 1 := by omega
  have hnbr1 : (G.neighborFinset p).card = 1 := by omega
  obtain ⟨z,hz⟩ := card_eq_one.mp hnbr1
  have hxz : x=z := mem_singleton.mp (hz ▸ hx)
  have hunique (w : V) (h : G.Adj p w) : w=x := by
    have hw := (G.mem_neighborFinset _ _).mpr h
    exact (mem_singleton.mp (hz ▸ hw)).trans hxz.symm
  have hall (w : V) (hw : w ≠ u) : G.Adj u w := by
    apply dist_eq_one_iff_adj.mp
    have hpos := hc.pos_dist_of_ne hw.symm
    by_contra he
    have hlt : 1 < G.dist u w := by omega
    have hs := Finset.sum_lt_sum (s := (univ : Finset V).erase u)
      (fun a ha => Nat.succ_le_of_lt (hc.pos_dist_of_ne (Ne.symm (mem_erase.mp ha).1)))
      ⟨w,mem_erase.mpr ⟨hw,mem_univ _⟩,hlt⟩
    have hbad : Fintype.card V - 1 < transmission G u := by
      simpa [transmission, card_erase_of_mem (mem_univ u)] using hs
    omega
  by_cases hpu : p=u
  · have hcard : (G.neighborFinset p).card = Fintype.card V - 1 := by
      have hN : G.neighborFinset p = (univ : Finset V).erase p := by
        ext w
        simp only [mem_neighborFinset,mem_erase,mem_univ,and_true]
        exact ⟨fun h => h.ne.symm, fun h => by subst p; exact hall w h⟩
      rw [hN,card_erase_of_mem (mem_univ p),card_univ]
    have ht : Fintype.card V = 2 := by omega
    have hl : ({p,x} : Finset V).card = 2 := by simp [hpx.ne]
    have hpair : ({p,x} : Finset V) = univ := by
      apply eq_of_subset_of_card_le (subset_univ _)
      rw [card_univ,hl,ht]
    -- If the graph has order two, the other endpoint is also universal.
    have hOther (w : V) (hw : w≠x) : G.Adj x w := by
      have hmem : w ∈ ({p,x} : Finset V) := hpair.symm ▸ mem_univ _
      simp only [mem_insert,mem_singleton] at hmem
      rcases hmem with rfl | h
      · exact hpx.symm
      · exact (hw h).elim
    exact ⟨x,p,hpx,hunique,hOther⟩
  · have hxu : x=u := (hunique u (hall p hpu).symm).symm
    exact ⟨u,p,hxu ▸ hpx,fun w hw => (hunique w hw).trans hxu,hall⟩

omit [Fintype V] in
private theorem universal_pendant_well_total_dominated {u p : V} (hpu : G.Adj p u)
    (hp : ∀ w, G.Adj p w → w=u) (hu : ∀ w, w≠u → G.Adj u w) :
    WellTotalDominated G := by
  intro D hD hmin E hE
  have contains_u (S : Finset V) (hS : TotalDominates G S) : u ∈ S := by
    obtain ⟨w,hw,ha⟩ := hS p
    rwa [hp w ha] at hw
  have du := contains_u D hD
  obtain ⟨x,hx,hux⟩ := hD u
  let S : Finset V := {u,x}
  have hSD : S ⊆ D := by
    intro w hw
    simp only [S,mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact du
    · exact hx
  have htotal : TotalDominates G S := by
    intro w
    by_cases hwu : w = u
    · exact ⟨x,by simp [S],hwu.symm ▸ hux⟩
    · exact ⟨u,by simp [S],(hu w hwu).symm⟩
  have hD2 : D.card ≤ 2 := by simpa [S,hux.ne] using card_le_card (hmin S hSD htotal)
  have eu := contains_u E hE
  obtain ⟨y,hy,huy⟩ := hE u
  have hE2 : 1 < E.card := one_lt_card.mpr ⟨u,eu,y,hy,huy.ne⟩
  omega

theorem conjecture320 (G : SimpleGraph V) (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (heq : maxEven G = minTransmission G) : WellTotalDominated G := by
  obtain ⟨u,p,hpu,hp,hu⟩ := universal_and_pendant hc hn heq
  exact universal_pendant_well_total_dominated hpu hp hu

#print axioms universal_and_pendant
#print axioms conjecture320
end
end Graffiti320
