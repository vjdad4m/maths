import Mathlib.Tactic.Linarith
import Twin
import Row1553
import Mathlib.Algebra.Order.Archimedean.Basic

namespace RegularCover5174
open SimpleGraph Finset HallRainbow1121 TriangleMatching1078 BullCover1125 RainbowCover1553

/-- Every nonempty clique in a triangle-free graph is a vertex or an edge.
A singleton can be extended along an incident edge. -/
theorem triangle_free_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    (iso : IsolateFree G) (tri : TriangleFree G) : edgeCoverNumber G = vertexCliqueCover G := by
  classical
  apply le_antisymm _ (clique_cover_le_edge_cover G iso)
  obtain ⟨col⟩ := Nat.sInf_mem (s:={k | Gᶜ.Colorable k}) ⟨_,Gᶜ.colorable_of_fintype⟩
  let colors := univ.image (fun v : V => col v)
  have same {a b : V} (ne : a ≠ b) (h : col a = col b) : G.Adj a b := by
    by_contra no
    exact col.valid ((G.compl_adj a b).mpr ⟨ne,no⟩) h
  have one (i : ↥colors) : ∃ e : G.edgeSet, ∀ v, col v = i.val → v ∈ e.val := by
    obtain ⟨a,_,ha⟩ := mem_image.mp i.property
    by_cases pair : ∃ b, b ≠ a ∧ col b = i.val
    · obtain ⟨b,ba,hb⟩ := pair
      have ab := same ba.symm (ha.trans hb.symm)
      refine ⟨⟨s(a,b),ab⟩,fun v hv => Sym2.mem_iff.mpr ?_⟩
      by_cases va : v = a
      · exact Or.inl va
      by_cases vb : v = b
      · exact Or.inr vb
      exact False.elim (tri a b v ab (same (Ne.symm vb) (hb.trans hv.symm)) (same va (hv.trans ha.symm)))
    · obtain ⟨b,ab⟩ := iso a
      refine ⟨⟨s(a,b),ab⟩,fun v hv => ?_⟩
      have eq : v = a := Classical.byContradiction (fun ne => pair ⟨v,ne,hv⟩)
      exact Sym2.mem_iff.mpr (Or.inl eq)
  choose edge covers using one
  let edges := univ.image edge
  have good : Covers G edges := by
    intro v
    let i : ↥colors := ⟨col v,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩
    exact ⟨edge i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,covers i v rfl⟩
  have bound : edgeCoverNumber G ≤ edges.card := Nat.sInf_le ⟨edges,rfl,good⟩
  apply bound.trans
  calc
    edges.card ≤ (univ : Finset ↥colors).card := card_image_le
    _ = colors.card := by simp
    _ ≤ (univ : Finset (Fin (vertexCliqueCover G))).card := card_le_card (subset_univ _)
    _ = _ := by simp

open RegularCliques1957

theorem family_cover (n : ℕ) : edgeCoverNumber (graph n) = 2*n+3 ∧
    edgeCoverValue (graph n) = some (2*n+3) := by
  have iso : IsolateFree (graph n) := fun v =>
    ((graph n).degree_pos_iff_exists_adj v).mp (by rw [regular n v]; omega)
  have eq := (triangle_free_cover (graph n) iso (triangle_free n)).trans (clique_exact n)
  exact ⟨eq,by simp [edgeCoverValue,iso,eq]⟩

/-- The multiplicative constant two cannot be lowered even by allowing a fixed
additive term and restricting to connected regular bipartite graphs. -/
theorem sharp_affine (c A : ℚ) (hc : c < 2) : ∃ n : ℕ,
    (graph n).Connected ∧ (graph n).Colorable 2 ∧ (graph n).IsRegularOfDegree (n+2) ∧
    c * lineDomination (graph n) + A < (edgeCoverNumber (graph n) : ℚ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((A+1)/(2-c))
  have gap := (div_lt_iff₀ (show 0 < 2-c by linarith)).mp hn
  let color : (graph n).Coloring Bool := Coloring.mk Prod.fst (fun e => e.1)
  refine ⟨n,connected n,by simpa using color.colorable,regular n,?_⟩
  rw [(edge_exact n).1,(family_cover n).1]
  push_cast
  nlinarith

/-- The exact rational antecedent is true for every degree at least ten. -/
theorem row5170_counterexamples (n : ℕ) (hn : 8 ≤ n) :
    edgeCoverValue (graph n) = some (2*n+3) ∧
    (lineDomination (graph n) : ℚ) < (4/7 : ℚ)*(2*(n:ℚ)+3) + (-5/7) ∧
    (graph n).IsRegularOfDegree (n+2) := by
  refine ⟨(family_cover n).2,?_,regular n⟩
  rw [(edge_exact n).1]
  have bound : (8:ℚ) ≤ n := by exact_mod_cast hn
  push_cast
  linarith

theorem row5170_false : ¬ (∀ (G : SimpleGraph (Vertex 8)) [DecidableRel G.Adj] (r : ℕ),
    edgeCoverValue G = some r →
    (lineDomination G : ℚ) < (4/7 : ℚ)*r + (-5/7) → ¬ ∃ k, G.IsRegularOfDegree k) := by
  intro row
  obtain ⟨cover,ante,reg⟩ := row5170_counterexamples 8 (by decide)
  exact row (graph 8) 19 cover (by norm_num at ante ⊢; exact ante) ⟨10,reg⟩

#print axioms triangle_free_cover
#print axioms family_cover
#print axioms sharp_affine
#print axioms row5170_counterexamples
#print axioms row5170_false
end RegularCover5174
