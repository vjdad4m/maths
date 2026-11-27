import Bound
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

namespace Theta659
open Finset SimpleGraph TriangleMatching1078 AutoGraphForge378 Graffiti326
open scoped BigOperators
variable {k : ℕ}

/-- The two hubs and the two internal vertices of each 3-edge path. -/
abbrev V (k : ℕ) := Bool × Option (Fin k)
abbrev hub (b : Bool) : V k := (b,none)
abbrev inner (i : Fin k) (b : Bool) : V k := (b,some i)

def rel : V k → V k → Prop
  | (_,none), (_,none) => False
  | (b,none), (c,some _) | (b,some _), (c,none) => b=c
  | (b,some i), (c,some j) => i=j ∧ b≠c

instance : DecidableRel (@rel k) := by
  rintro ⟨a,_|i⟩ ⟨b,_|j⟩ <;> dsimp [rel] <;> infer_instance

def graph (k : ℕ) : SimpleGraph (V k) where
  Adj := rel
  symm := by
    rintro ⟨a,_|i⟩ ⟨b,_|j⟩ h
    · exact h
    · exact h.symm
    · exact h.symm
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by rintro ⟨a,_|i⟩ h; exact h; exact h.2 rfl

instance : DecidableRel (graph k).Adj := inferInstanceAs (DecidableRel rel)

theorem order (k : ℕ) : Fintype.card (V k) = 2*k+2 := by simp [V,Fintype.card_prod]; omega

theorem connected (hk : 0<k) : (graph k).Connected := by
  let i : Fin k := ⟨0,hk⟩
  have hf : (graph k).Reachable (hub true) (hub false) :=
    (show (graph k).Adj (hub true) (inner i true) from rfl).reachable.trans
      ((show (graph k).Adj (inner i true) (inner i false) from ⟨rfl,by decide⟩).reachable.trans
      (show (graph k).Adj (inner i false) (hub false) from rfl).reachable)
  have reaches (v : V k) : (graph k).Reachable v (hub false) := by
    obtain ⟨b,_|j⟩ := v
    · cases b; exact Reachable.rfl; exact hf
    · have step := (show (graph k).Adj (inner j b) (hub b) from rfl).reachable
      cases b; exact step; exact step.trans hf
  exact ⟨fun u v => (reaches u).trans (reaches v).symm⟩

private def side : V k → Bool
  | (b,none) => b
  | (b,some _) => !b

private theorem opposite {u v : V k} (h : (graph k).Adj u v) : side u ≠ side v := by
  rcases u with ⟨a,_|i⟩ <;> rcases v with ⟨b,_|j⟩ <;> cases a <;> cases b <;> simp_all [graph,rel,side]

theorem bipartite : (graph k).Colorable 2 := by
  let color (b : Bool) : Fin 2 := if b then 1 else 0
  have inject : Function.Injective color := by
    intro a b h
    cases a <;> cases b <;> simp_all [color]
  exact ⟨Coloring.mk (fun v => color (side v)) (fun h eq => opposite h (inject eq))⟩

theorem triangle_free : TriangleFree (graph k) := by
  intro a b c ab bc ca
  have h₁ := opposite ab
  have h₂ := opposite bc
  have h₃ := opposite ca
  exact (by decide : ∀ x y z : Bool, x≠y → y≠z → ¬z≠x) _ _ _ h₁ h₂ h₃

private def middle (i : Fin k) : (graph k).edgeSet :=
  ⟨s(inner i false,inner i true),⟨rfl,by decide⟩⟩

/-- A graph edge cannot touch middle edges from different paths. -/
private theorem same_path (e : (graph k).edgeSet) {i j : Fin k} {b c : Bool}
    (h : inner i b ∈ e.val) (h' : inner j c ∈ e.val) : i=j := by
  by_contra ne
  have diff : inner i b ≠ inner j c := fun eq => ne (Option.some.inj (congrArg Prod.snd eq))
  have adj := e.property
  rw [(Sym2.mem_and_mem_iff diff).mp ⟨h,h'⟩] at adj
  exact ne adj.1

/-- The induced-matching packing bound: if every edge touches at most one
designated edge, any line-graph dominating set must have at least as many
members as the number of designated edges. -/
theorem packing_lower {U I : Type*} [Fintype U] [Fintype I] (G : SimpleGraph U)
    [DecidableRel G.Adj] (M : I → G.edgeSet)
    (apart : ∀ (e : G.edgeSet) (i j : I),
      (∃ v, v ∈ e.val ∧ v ∈ (M i).val) → (∃ w, w ∈ e.val ∧ w ∈ (M j).val) → i=j) :
    Fintype.card I ≤ lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained G
  have existsEdge (i : I) : ∃ e : ↥D, ∃ v, v ∈ e.val.val ∧ v ∈ (M i).val := by
    obtain ⟨e,he,hit⟩ := (dominates_iff G D).mp dom (M i)
    exact ⟨⟨e,he⟩,hit⟩
  choose pick hit using existsEdge
  have inj : Function.Injective pick := fun i j eq => apart (pick i).val i j (hit i) (eq ▸ hit j)
  simpa [sz] using Fintype.card_le_of_injective pick inj

theorem edge_lower : k ≤ lineDomination (graph k) := by
  have h := packing_lower (graph k) middle (by
    rintro e i j ⟨v,hv,vi⟩ ⟨w,hw,wj⟩
    rcases Sym2.mem_iff.mp vi with rfl|rfl <;> rcases Sym2.mem_iff.mp wj with rfl|rfl <;>
      exact same_path e hv hw)
  simpa using h

theorem middle_matching : HasMaximalMatching (graph k) k := by
  let f : Fin k × Bool ↪ V k := ⟨fun (i,b) => inner i b,by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    exact Prod.ext (Option.some.inj (congrArg Prod.snd eq)) (congrArg Prod.fst eq)⟩
  have mem (i : Fin k) (b : Bool) : inner i b ∈ support f :=
    (Graffiti326.mem_support f).mpr ⟨i,b,rfl⟩
  refine ⟨f,fun _ => ⟨rfl,by decide⟩,?_⟩
  rintro ⟨a,_|i⟩ ha ⟨b,_|j⟩ hb e
  · exact e
  · exact hb (mem j b)
  all_goals exact ha (mem i a)

theorem matching_exact : lineDomination (graph k) = k ∧ minMaximalMatching (graph k) = k := by
  have h₁ := @edge_lower k
  have h₂ := lineDomination_le_matching (graph k)
  have h₃ : minMaximalMatching (graph k) ≤ k := Nat.sInf_le middle_matching
  omega
end Theta659
