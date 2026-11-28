import GapTwin189
import PinRunSeparator189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open Graffiti189LongestPath.GapTwin Graffiti189LongestPath.PinRun
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti189LongestPath.Normalize

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_edgeMin (hc : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), EdgeMin p := by
  classical
  obtain ⟨a,b,p,hp⟩ := Graffiti189LongestPath.Rigidity.exists_longest hc
  let M := (range (Fintype.card (Sym2 V)+1)).filter fun i =>
    ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧ (edgesIn G q.support.toFinset).card=i
  have pick {u v : V} {q : G.Walk u v} (hq : IsLongest q) :
      (edgesIn G q.support.toFinset).card ∈ M := by
    have h := card_le_univ (edgesIn G q.support.toFinset)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),u,v,q,hq,rfl⟩
  have hM : M.Nonempty := ⟨_,pick hp⟩
  obtain ⟨u,v,q,hq,he⟩ := (mem_filter.mp (M.min'_mem hM)).2
  exact ⟨u,v,q,hq,fun _ _ w hw => he.symm ▸ M.min'_le _ (pick hw)⟩

def EdgeMinAvoid (d : Nat) {a b : V} (p : G.Walk a b) : Prop :=
  EdgeMin p ∧ ∀ u v (q : G.Walk u v), EdgeMin q →
    ∀ x, G.degree x < d → x ∉ q.support → x ∉ p.support

theorem exists_edgeMinAvoid (hc : G.Connected) (d : Nat)
    (deg : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v) :
    ∃ (a b : V) (p : G.Walk a b), EdgeMinAvoid d p := by
  classical
  by_cases he : ∃ (a b : V) (p : G.Walk a b) (x : V),
      EdgeMin p ∧ G.degree x < d ∧ x ∉ p.support
  · obtain ⟨a,b,p,x,hp,hd,hx⟩ := he
    refine ⟨a,b,p,hp,fun u v q hq y hy hn => ?_⟩
    have eq : y = x := by
      by_contra h
      rcases deg y x h with h|h <;> omega
    simpa [eq] using hx
  · obtain ⟨a,b,p,hp⟩ := exists_edgeMin hc
    exact ⟨a,b,p,hp,fun u v q hq x hd hx =>
      (he ⟨u,v,q,x,hq,hd,hx⟩).elim⟩

/-- On an edge-minimal longest path that prefers omitting the low vertex,
high-degree omitted vertices at connectivity d−2 cannot straddle a
one-vertex gap. Together with the pin budget, their only possible double
contact is at two path positions at least three apart. -/
theorem normalized_high_omission (hc : G.Connected) (d k : ℕ) (large : 5 ≤ d)
    (slack : d ≤ k+2)
    (cap : ∀ v, (EvenFrom G v).card ≤ d+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : EdgeMinAvoid d p)
    {x : V} (hx : x ∉ p.support) (high : d ≤ G.degree x) :
    ∀ i ∈ Pins p x, (Pins p x).card+(Shell G x 4).card ≤ 2 ∧
      i+2 ∉ Pins p x := by
  classical
  intro i hi
  have ex := (Graffiti189LongestPath.pin_data hi).2
  have pb := high_omitted_pin_budget hc d k cap conn hp.1.1 hx ex high
  refine ⟨by omega,?_⟩
  intro hj
  have sub : ({i,i+2} : Finset ℕ) ⊆ Pins p x := by
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    exact ht.elim (fun e => e.symm ▸ hi) (fun e => e.symm ▸ hj)
  have hC : ({i,i+2} : Finset ℕ).card = 2 := by simp
  have eq : Pins p x = {i,i+2} := (eq_of_subset_of_card_le sub (by omega)).symm
  obtain ⟨q,hq,hout,hd⟩ := gap_two_midpoint_small hc d cap hp.1 hx high i eq
  have hb := hp.2 a b q hq (p.getVert (i+1)) (by omega) hout
  exact hb (p.getVert_mem_support (i+1))

#print axioms exists_edgeMinAvoid
#print axioms normalized_high_omission
end Graffiti189LongestPath.Normalize
