/- Reproduce in a project pinned to Lean 4.19.0 / Mathlib v4.19.0 with `lake env lean Formal157.lean`. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset
open scoped BigOperators
namespace Graffiti157
variable {V : Type*} [Fintype V]

theorem predecessor (G : SimpleGraph V) (hc : G.Connected) (r v : V) (hv : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact False.elim (hv rfl)
  | cons =>
    rename_i w had p
    refine ⟨w,had,?_⟩
    have h₁ : G.dist r w + 1 ≤ G.dist r v := by
      have hl := G.dist_le p
      rw [SimpleGraph.dist_comm] at hl
      have ht : G.dist r v = G.dist v r := SimpleGraph.dist_comm
      rw [SimpleGraph.Walk.length_cons] at hp
      omega
    have h₂ := hc.dist_triangle (u := r) (v := w) (w := v)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr had.symm] at h₂
    omega

theorem parent_exists (G : SimpleGraph V) (hc : G.Connected) (r : V) :
    ∃ parent : V → V, ∀ v, v ≠ r →
      G.Adj v (parent v) ∧ G.dist r (parent v) + 1 = G.dist r v := by
  classical
  have h (v : V) : ∃ w, v ≠ r → G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
    by_cases hv : v=r
    · exact ⟨r,fun h => False.elim (h hv)⟩
    · obtain ⟨w,hw⟩ := predecessor G hc r v hv
      exact ⟨w, fun _ => hw⟩
  exact ⟨fun v => Classical.choose (h v),fun v => Classical.choose_spec (h v)⟩

def parentGraph (r : V) (p : V → V) (h : ∀ v, v ≠ r → p v ≠ v) : SimpleGraph V where
  Adj v w := (v ≠ r ∧ p v = w) ∨ (w ≠ r ∧ p w = v)
  symm _ _ := Or.symm
  loopless := fun v hv => by
    rcases hv with ⟨hn,he⟩ | ⟨hn,he⟩ <;> exact h v hn he

theorem bfs_graph (G : SimpleGraph V) (hc : G.Connected) (r : V) :
    ∃ (p : V → V) (h : ∀ v, v ≠ r → p v ≠ v),
      (∀ v, v ≠ r → G.dist r (p v)+1 = G.dist r v) ∧
      parentGraph r p h ≤ G ∧ (parentGraph r p h).Connected := by
  obtain ⟨p,hp⟩ := parent_exists G hc r
  have hn (v : V) (hv : v ≠ r) : p v ≠ v := (hp v hv).1.ne.symm
  refine ⟨p,hn,fun v hv => (hp v hv).2,?_,?_⟩
  · intro v w had
    rcases had with ⟨hv,rfl⟩ | ⟨hw,rfl⟩
    · exact (hp _ hv).1
    · exact (hp _ hw).1.symm
  · let T := parentGraph r p hn
    have hr (v : V) : T.Reachable v r := by
      generalize he : G.dist r v = k
      induction k using Nat.strongRecOn generalizing v with
      | ind k ih =>
        by_cases hv : v=r
        · subst v
          exact ⟨.nil⟩
        · have hpv := (hp v hv).2
          obtain ⟨w⟩ := ih (G.dist r (p v)) (by omega) (p v) rfl
          exact ⟨.cons (Or.inl ⟨hv,rfl⟩) w⟩
    letI : Nonempty V := ⟨r⟩
    exact ⟨fun v w => (hr v).trans (hr w).symm⟩

theorem connected_has_neighbor (H : SimpleGraph V) (hc : H.Connected)
    (hn : 1 < Fintype.card V) (v : V) : ∃ w, H.Adj v w := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact False.elim (hw rfl)
  | cons =>
    rename_i w h p
    exact ⟨_,h⟩

def IsLeaf (G : SimpleGraph V) (v : V) : Prop := ∃ w, G.Adj v w ∧ ∀ x, G.Adj v x → x=w

noncomputable def leaves (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (IsLeaf G)

def leafCounts (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ (leaves T).card = k}

noncomputable def maxLeaves (G : SimpleGraph V) : ℕ := sSup (leafCounts G)

theorem leafCounts_bounded (G : SimpleGraph V) : BddAbove (leafCounts G) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨T,_,_,rfl⟩
  exact Finset.card_le_univ (leaves T)

def eccentricity (G : SimpleGraph V) (r : V) : ℕ := Finset.univ.sup (G.dist r)

noncomputable def radius (G : SimpleGraph V) : ℕ := sInf (Set.range (eccentricity G))

noncomputable def circle (G : SimpleGraph V) (r : V) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist r v = radius G)

noncomputable def shellEdges (G : SimpleGraph V) (r : V) : ℕ := by
  classical
  exact ((G.induce (↑(circle G r) : Set V)).edgeFinset).card

noncomputable def maxRadialEdges (G : SimpleGraph V) : ℕ := by
  classical
  exact univ.sup (fun r => if eccentricity G r = radius G then shellEdges G r else 0)

theorem circle_leaf_parentGraph (G : SimpleGraph V) (r : V)
    (hcenter : eccentricity G r = radius G)
    (p : V → V) (h : ∀ v, v ≠ r → p v ≠ v)
    (hp : ∀ v, v ≠ r → G.dist r (p v)+1=G.dist r v) {v : V}
    (hv : v ∈ circle G r) :
    ∀ w, (parentGraph r p h).Adj v w → w = p v := by
  classical
  have hbound (w : V) : G.dist r w ≤ radius G := by
    rw [← hcenter]
    exact Finset.le_sup (f := G.dist r) (Finset.mem_univ w)
  have hvd : G.dist r v = radius G := (Finset.mem_filter.mp hv).2
  intro w hw
  rcases hw with ⟨_,he⟩ | ⟨hneq,he⟩
  · exact he.symm
  · have h₁ := hp w hneq
    rw [he, hvd] at h₁
    have h₂ := hbound w
    omega

theorem no_leaf_inside_circle (G : SimpleGraph V) (hc : G.Connected) (r : V)
    (hn : 1 < Fintype.card V) (hcenter : eccentricity G r = radius G)
    {v w : V} (hv : v ∈ circle G r) (hw : w ∈ circle G r)
    (hleaf : IsLeaf G v) : ¬ G.Adj v w := by
  classical
  have hRadPos : 0 < radius G := by
    obtain ⟨x,hx⟩ := Fintype.exists_ne_of_one_lt_card hn r
    have hd := hc.pos_dist_of_ne (u:=r) (v:=x) (Ne.symm hx)
    have hb : G.dist r x ≤ radius G := by
      rw [← hcenter]
      exact Finset.le_sup (f := G.dist r) (Finset.mem_univ x)
    omega
  have hvd : G.dist r v = radius G := (Finset.mem_filter.mp hv).2
  have hwd : G.dist r w = radius G := (Finset.mem_filter.mp hw).2
  have hvr : v ≠ r := by
    intro he
    rw [he, SimpleGraph.dist_self] at hvd
    omega
  obtain ⟨p,hp,hd⟩ := predecessor G hc r v hvr
  obtain ⟨x,hx,hu⟩ := hleaf
  intro hvw
  have he : p = w := (hu _ hp).trans (hu _ hvw).symm
  rw [he,hwd,hvd] at hd
  omega

noncomputable def nonLeafCircle (G : SimpleGraph V) (r : V) : Finset V := by
  classical
  exact (circle G r).filter (fun v => ¬ IsLeaf G v)

theorem shellEdges_sq (G : SimpleGraph V) (hc : G.Connected) (r : V)
    (hn : 1 < Fintype.card V) (hcenter : eccentricity G r = radius G) :
    2 * shellEdges G r ≤ (nonLeafCircle G r).card * (nonLeafCircle G r).card := by
  classical
  let R := circle G r
  let A := nonLeafCircle G r
  let H := G.induce (↑R : Set V)
  let S : Set (↑(↑R : Set V)) := {v | ¬ IsLeaf G v.1}
  have hS : H.support ⊆ S := by
    intro v hv
    obtain ⟨w,hw⟩ := (SimpleGraph.mem_support H).mp hv
    exact fun h => no_leaf_inside_circle G hc r hn hcenter v.2 w.2 h hw
  have hcEdge := SimpleGraph.card_edgeFinset_induce_of_support_subset hS
  have hub := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H.induce S)
  have he : shellEdges G r ≤ (Fintype.card ↑S).choose 2 := by
    unfold shellEdges
    rw [hcEdge] at hub
    exact hub
  have ha : Fintype.card ↑S ≤ A.card := by
    have hca := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset ↑S))
      (t := A) (fun v => v.1.1)
      (fun v _ => Finset.mem_filter.mpr ⟨v.1.2, v.2⟩)
      (fun v _ w _ he => Subtype.ext (Subtype.ext he))
    simpa using hca
  have hd := Nat.div_mul_le_self (Fintype.card ↑S * (Fintype.card ↑S - 1)) 2
  rw [Nat.choose_two_right] at he
  have hmul : Fintype.card ↑S * (Fintype.card ↑S - 1) ≤ A.card * A.card :=
    Nat.mul_le_mul ha (Nat.le_trans (Nat.sub_le _ _) ha)
  change 2 * shellEdges G r ≤ A.card * A.card
  omega

theorem leaf_count_lower (G : SimpleGraph V) (hc : G.Connected) (r : V)
    (hn : 1 < Fintype.card V) (hcenter : eccentricity G r = radius G) :
    (leaves G).card + (nonLeafCircle G r).card ≤ maxLeaves G := by
  classical
  obtain ⟨p,hp,hd,hsub,hconn⟩ := bfs_graph G hc r
  obtain ⟨T,hT,hTree⟩ := hconn.exists_isTree_le
  have hTG := hT.trans hsub
  have h₁ : leaves G ⊆ leaves T := by
    intro v hv
    have hvl : IsLeaf G v := (Finset.mem_filter.mp hv).2
    obtain ⟨w,hw⟩ := connected_has_neighbor T hTree.isConnected hn v
    obtain ⟨x,_,hx⟩ := hvl
    have hwx := hx w (hTG hw)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,hw,fun y hy => (hx y (hTG hy)).trans hwx.symm⟩
  have h₂ : nonLeafCircle G r ⊆ leaves T := by
    intro v hv
    have hvr := (Finset.mem_filter.mp hv).1
    have hh := circle_leaf_parentGraph G r hcenter p hp hd hvr
    obtain ⟨w,hw⟩ := connected_has_neighbor T hTree.isConnected hn v
    have hwx := hh w (hT hw)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,hw,fun y hy => (hh y (hT hy)).trans hwx.symm⟩
  have hdj : Disjoint (leaves G) (nonLeafCircle G r) := by
    rw [Finset.disjoint_left]
    intro v hv huv
    exact (Finset.mem_filter.mp huv).2 ((Finset.mem_filter.mp hv).2)
  have hu : leaves G ∪ nonLeafCircle G r ⊆ leaves T := Finset.union_subset h₁ h₂
  have hcard := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hdj] at hcard
  have hmax : (leaves T).card ≤ maxLeaves G :=
    le_csSup (leafCounts_bounded G) ⟨T,hTG,hTree,rfl⟩
  exact hcard.trans hmax

theorem fringe (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < Fintype.card V) :
    (leaves G).card ≤ maxLeaves G ∧
    2 * maxRadialEdges G ≤ (maxLeaves G-(leaves G).card)^2 := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨a,ha⟩ := Nat.sInf_mem (Set.range_nonempty (f := eccentricity G))
  have hcenter : eccentricity G a = radius G := ha
  have hm : (leaves G).card ≤ maxLeaves G :=
    Nat.le_trans (Nat.le_add_right _ _) (leaf_count_lower G hc a hn hcenter)
  refine ⟨hm,?_⟩
  have hs : maxRadialEdges G ≤ ((maxLeaves G-(leaves G).card)^2)/2 := by
    unfold maxRadialEdges
    apply Finset.sup_le
    intro r _
    split
    · rename_i hh
      have hl := leaf_count_lower G hc r hn hh
      have he := shellEdges_sq G hc r hn hh
      have hla : (nonLeafCircle G r).card ≤ maxLeaves G-(leaves G).card := by omega
      have hh₂ := Nat.mul_le_mul hla hla
      rw [pow_two]
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      omega
    · exact Nat.zero_le _
  omega

theorem fringe_all (G : SimpleGraph V) (hc : G.Connected) :
    (leaves G).card ≤ maxLeaves G ∧
    2 * maxRadialEdges G ≤ (maxLeaves G-(leaves G).card)^2 := by
  classical
  by_cases hn : 1 < Fintype.card V
  · exact fringe G hc hn
  · have eqv : ∀ v w : V, v=w := (Fintype.card_le_one_iff).mp (by omega)
    have hNoAdj (v w : V) : ¬ G.Adj v w := by
      rw [eqv v w]
      exact G.loopless w
    have hleaves : (leaves G).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext v
      constructor
      · intro hv
        obtain ⟨w,hw,_⟩ := (Finset.mem_filter.mp hv).2
        exact False.elim (hNoAdj v w hw)
      · simp
    have hEdges (r : V) : shellEdges G r = 0 := by
      have hb : G.induce (↑(circle G r) : Set V) = ⊥ := by
        ext v w
        change G.Adj v.1 w.1 ↔ False
        exact iff_false_intro (hNoAdj _ _)
      unfold shellEdges
      simp [hb]
    have hE : maxRadialEdges G = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold maxRadialEdges
      apply Finset.sup_le
      intro r _
      rw [hEdges]
      split <;> omega
    simp [hleaves,hE]

theorem conjecture157 (G : SimpleGraph V) (hc : G.Connected) :
    ((leaves G).card : ℝ) + Real.sqrt (2 * (maxRadialEdges G : ℝ)) ≤ (maxLeaves G : ℝ) := by
  obtain ⟨hf,hb⟩ := fringe_all G hc
  have hcast : ((2 * maxRadialEdges G : ℕ) : ℝ) ≤
      (((maxLeaves G-(leaves G).card)^2 : ℕ) : ℝ) := Nat.cast_le.mpr hb
  have hreal : (2:ℝ) * (maxRadialEdges G : ℝ) ≤
      ((maxLeaves G : ℝ) - ((leaves G).card : ℝ)) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_sub hf] using hcast
  have hnon : (0:ℝ) ≤ (maxLeaves G : ℝ) - ((leaves G).card : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr hf)
  have hr := Real.sqrt_le_iff.mpr ⟨hnon,hreal⟩
  linarith

#print axioms fringe_all
#print axioms conjecture157
end Graffiti157
