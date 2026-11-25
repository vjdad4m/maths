/-
Counterexample to Graffiti.pc #433, Written on the Wall II (December 2010).
Official source: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json

Start with a five-vertex clique. For every clique pair, add three degree-two
vertices attached just to its endpoints. Add one pendant vertex on clique
vertex 0, making it the unique maximum-degree vertex. The resulting connected
graph has order 36; the open neighborhood of its maximum-degree set has size 17.

An independent dominating set contains at most one clique vertex. If it
contains one, it must also contain the 18 degree-two vertices not adjacent
to it; if it contains none, it needs all 30 degree-two vertices. Clique
vertex 0 with its 18 nonneighbors is an independent dominating set, so i=19.

The square-degree multiplicities are 35 (five vertices), 26 (twelve),
25 (eighteen) and 17 (one). Twice the reciprocal sum is 106992/38675, whose
floor is 2; thus the conjectured bound is 17 < 19.

For a related clique-and-incidence construction used for a different bound,
see Goddard and Henning, Independent domination in graphs, §5.4,
https://doi.org/10.1016/j.disc.2012.11.031. No priority claim is made.

Replay: Lean and Mathlib v4.19.0. Exact theorem: Graffiti433.exact_counterexample.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open SimpleGraph Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 2048
set_option warningAsError true
namespace Graffiti433

abbrev V := Fin 36

def pairs : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def atPair (k v : V) : Prop :=
  5 ≤ v.val ∧ v.val < 35 ∧
    ((pairs.getD ((v.val - 5)/3) (0,0)).1 = k.val ∨
     (pairs.getD ((v.val - 5)/3) (0,0)).2 = k.val)

instance (k v : V) : Decidable (atPair k v) := by unfold atPair; infer_instance

def arc (u v : V) : Prop :=
  (u.val < 5 ∧ v.val < 5) ∨
  (u.val < 5 ∧ atPair u v) ∨ (u = 0 ∧ v = 35)

instance (u v : V) : Decidable (arc u v) := by unfold arc; infer_instance

def G : SimpleGraph V where
  Adj u v := u ≠ v ∧ (arc u v ∨ arc v u)
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (arc _ _ ∨ arc _ _)))

def SqAdj (u v : V) : Prop := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
instance (u v : V) : Decidable (SqAdj u v) := by unfold SqAdj; infer_instance

def squareDegree (u : V) := (univ.filter (SqAdj u)).card

def maxNbr : Finset V := univ.filter (fun w => ∃ v : V, G.degree v = G.maxDegree ∧ G.Adj v w)

def invSum : ℚ := ∑ v : V, (1 : ℚ) / squareDegree v

def TwoTimesFloor : ℤ := ⌊2*invSum⌋

def independent (D : Finset V) : Prop := ∀ u ∈ D, ∀ v ∈ D, ¬G.Adj u v

def dominates (D : Finset V) : Prop := ∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj u v

noncomputable def iNum : ℕ := sInf {k | ∃ D : Finset V, D.card = k ∧ independent D ∧ dominates D}

lemma connectedG : G.Connected := by
  have h : ∀ v : V, v = 0 ∨ G.Adj 0 v ∨ ∃ w : V, G.Adj 0 w ∧ G.Adj w v := by decide
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, fun v => ?_⟩
  rcases h v with rfl | e | ⟨w,h1,h2⟩
  · exact ⟨Walk.nil⟩
  · exact e.reachable
  · exact h1.reachable.trans h2.reachable

lemma maxNbr_count : maxNbr.card = 17 := by decide

lemma invSum_floor : TwoTimesFloor = 2 := by
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_ofNat, Nat.reduceAdd, Int.reduceAdd, show (2:ℚ) + 1 = 3 by norm_num]
  decide +kernel

def misses (c : V) : Finset V :=
  univ.filter (fun w : V => 5 ≤ w.val ∧ w.val < 35 ∧ ¬ G.Adj c w)

lemma missed_core : ∀ c : V, c.val < 5 → (misses c).card = 18 := by decide
lemma missed_extra : (misses 35).card = 30 := by decide
lemma clone_adj_core :
    ∀ v w : V, 5 ≤ w.val → w.val < 35 → G.Adj v w → v.val < 5 := by decide
lemma core_adj : ∀ u v : V, u.val < 5 → v.val < 5 → u ≠ v → G.Adj u v := by decide

lemma dominates_lower (D : Finset V) (hi : independent D) (hd : dominates D) :
    19 ≤ D.card := by
  classical
  by_cases hC : ∃ c ∈ D, c.val < 5
  · obtain ⟨c,hc,hcc⟩ := hC
    have hs : misses c ⊆ D := by
      intro w hw
      obtain ⟨_,hwlo,hwhi,hwn⟩ := Finset.mem_filter.mp hw
      rcases hd w with hw | ⟨u,hu,e⟩
      · exact hw
      · have huC := clone_adj_core u w hwlo hwhi e
        have huc : u = c := by
          by_contra hne
          exact hi u hu c hc (core_adj u c huC hcc hne)
        exact False.elim (hwn (huc ▸ e))
    have hm : c ∉ misses c := by
      intro h
      exact (Nat.not_le_of_lt hcc) (Finset.mem_filter.mp h).2.1
    have he := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hc,hs⟩)
    rw [Finset.card_insert_of_not_mem hm,missed_core c hcc] at he
    exact he
  · have hs : misses 35 ⊆ D := by
      intro w hw
      obtain ⟨_,hwlo,hwhi,_⟩ := Finset.mem_filter.mp hw
      rcases hd w with hw | ⟨u,hu,e⟩
      · exact hw
      · exact False.elim (hC ⟨u,hu,clone_adj_core u w hwlo hwhi e⟩)
    have hl := Finset.card_le_card hs
    rw [missed_extra] at hl
    omega

lemma iNum_exact : iNum = 19 := by
  let C : Finset V := insert 0 (misses 0)
  have hvalid : independent C ∧ dominates C := by
    have hf : (∀ u v : V, u ∈ C → v ∈ C → ¬G.Adj u v) ∧
      (∀ v : V, v ∈ C ∨ ∃ u : V, u ∈ C ∧ G.Adj u v) := by decide
    exact ⟨fun u hu v hv => hf.1 u v hu hv,hf.2⟩
  have hn : {k | ∃ D : Finset V, D.card = k ∧ independent D ∧ dominates D}.Nonempty :=
    ⟨C.card,C,rfl,hvalid⟩
  obtain ⟨D,hcard,hi,hd⟩ := Nat.sInf_mem hn
  have hb := dominates_lower D hi hd
  have hupper : iNum ≤ C.card := Nat.sInf_le (show C.card ∈ {k | ∃ D : Finset V,
    D.card = k ∧ independent D ∧ dominates D} from ⟨C,rfl,hvalid⟩)
  have hc : C.card = 19 := by decide
  change D.card = iNum at hcard
  omega

theorem exact_counterexample :
    G.Connected ∧ 3 < Fintype.card V ∧ (maxNbr.card : ℤ) * TwoTimesFloor < 2 * (iNum : ℤ) := by
  refine ⟨connectedG,by decide,?_⟩
  rw [maxNbr_count,invSum_floor,iNum_exact]
  decide

#print axioms exact_counterexample
end Graffiti433
