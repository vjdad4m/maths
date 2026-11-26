import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order

/-!
# Written on the Wall II, conjecture 348

Let B be the vertices outside the degree-two set that have a degree-two
neighbor. Every total dominating set D of a finite tree satisfies
2 |B| + 2 ≤ 3 |D|.

Members of B in D count themselves. Members of B outside D with a
selected degree-two neighbor charge distinct such neighbors.
Each remaining member u of B, with a chosen unselected degree-two
neighbor x, supplies three edges: from u to D, from u to x, and from x
to D. The chosen x's are distinct. Count these edges along with the
edges inside D, then use the forest edge bound.

Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti348
open Finset SimpleGraph SimpleGraph.Walk
open scoped Sym2 BigOperators
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def edgesWithin (A : Finset V) : Finset (Sym2 V) := by
  classical exact G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A)

private theorem edge_spec (A : Finset V) (a b : V) :
    s(a,b) ∈ edgesWithin G A ↔ G.Adj a b ∧ a ∈ A ∧ b ∈ A := by
  simp only [edgesWithin,mem_filter,mem_edgeFinset,SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hab,h⟩
    exact ⟨hab,h a (Sym2.mem_mk_left _ _),h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨hab,ha,hb⟩
    refine ⟨hab,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ha
    · exact hb

private theorem edge_count (hT : G.IsTree) {A : Finset V} (hA : A.Nonempty) :
    (edgesWithin G A).card + 1 ≤ A.card := by
  classical
  obtain ⟨root,hr⟩ := hA
  choose f hf hf' using (hT.existsUnique_path · root)
  have hn (w : V) (hw : w ∈ Aᶜ) : ¬(f w).Nil :=
    not_nil_of_ne (fun e => (mem_compl.mp hw) (e ▸ hr))
  have hin : Aᶜ.card ≤ (G.edgeFinset \ edgesWithin G A).card := by
    refine card_le_card_of_injOn
      (fun w : V => if hw : w ∈ Aᶜ then ((f w).firstDart (hn w hw)).edge else s(root,root)) ?_ ?_
    · intro a ha
      simp only [dif_pos ha]
      refine mem_sdiff.mpr ⟨by simp,?_⟩
      intro he
      have hh := (mem_filter.mp he).2 a
        (by exact Sym2.mem_mk_left _ _)
      exact (mem_compl.mp ha) hh
    · intro a ha b hb h
      change a ∈ Aᶜ at ha
      change b ∈ Aᶜ at hb
      simp only [dif_pos ha,dif_pos hb] at h
      wlog h' : (f a).length ≤ (f b).length generalizing a b
      · exact Eq.symm (this hb ha h.symm (le_of_not_le h'))
      rw [dart_edge_eq_iff] at h
      obtain (h | h) := h
      · exact congrArg (·.fst) h
      · have h1 : ((f a).firstDart (hn a ha)).snd = b := congrArg (·.snd) h
        have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
        · rw [length_copy, ← add_left_inj 1,length_tail_add_one (hn a ha)] at h3
          omega
        · simpa only [ne_eq,eq_mp_eq_cast,id_eq,isPath_copy] using (hf _).tail
  have hc := hT.card_edgeFinset
  have hsub : edgesWithin G A ⊆ G.edgeFinset := filter_subset _ _
  rw [card_sdiff hsub,card_compl] at hin
  have hA₀ := card_le_univ A
  have hE₀ := card_le_card hsub
  omega


def TotalDominates (D : Finset V) : Prop := ∀ x, ∃ y ∈ D, G.Adj x y

private theorem counting_internal (D : Finset V) (hD : TotalDominates G D) :
    D.card ≤ 2 * (edgesWithin G D).card := by
  classical
  let H := G.induce (D : Set V)
  have hp (v : ↑(D : Set V)) : 1 ≤ H.degree v := by
    obtain ⟨w,hw,ha⟩ := hD v.1
    exact (H.degree_pos_iff_exists_adj v).mpr ⟨⟨w,hw⟩,ha⟩
  have hs := Finset.sum_le_sum (s := (univ : Finset ↑(D : Set V))) (fun v _ => hp v)
  rw [H.sum_degrees_eq_twice_card_edges] at hs
  have hf : H.edgeFinset.card ≤ (edgesWithin G D).card := by
    apply card_le_card_of_injOn (Sym2.map (fun v : ↑(D : Set V) => v.1))
    · intro e he
      revert he
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        have ha : H.Adj a b := (mem_edgeFinset.mp he)
        exact (edge_spec G D a.1 b.1).mpr ⟨ha,a.2,b.2⟩
    · exact (Sym2.map.injective Subtype.val_injective).injOn
  exact (by simpa [Fintype.card_coe] using hs : D.card ≤ 2 * H.edgeFinset.card).trans
    (Nat.mul_le_mul_left _ hf)

def degreeTwo : Finset V := univ.filter fun v => G.degree v = 2

def outerNeighbors : Finset V := by
  classical
  exact univ.filter fun v => G.degree v ≠ 2 ∧ ∃ x, G.degree x = 2 ∧ G.Adj v x

private theorem mem_outer (v : V) :
    v ∈ outerNeighbors G ↔ G.degree v ≠ 2 ∧ ∃ x, G.degree x = 2 ∧ G.Adj v x := by
  classical
  simp [outerNeighbors]

private theorem deg_two_only {x u y z : V} (hx : G.degree x = 2)
    (hu : G.Adj x u) (hy : G.Adj x y) (huy : u ≠ y) (hz : G.Adj x z) :
    z = u ∨ z = y := by
  classical
  have hsub : ({u,y} : Finset V) ⊆ G.neighborFinset x :=
    insert_subset ((G.mem_neighborFinset _ _).mpr hu)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr hy))
  have he : ({u,y} : Finset V) = G.neighborFinset x :=
    eq_of_subset_of_card_le hsub (by simp [card_neighborFinset_eq_degree,hx,huy])
  have hz' := (G.mem_neighborFinset _ _).mpr hz
  rw [← he] at hz'
  simpa using hz'


private theorem inject_neighbors (D : Finset V) (hD : TotalDominates G D)
    (A : Finset V) (hA : ∀ u ∈ A, u ∉ D) (f : V → V)
    (h : ∀ u ∈ A, G.degree (f u) = 2 ∧ G.Adj u (f u)) :
    Set.InjOn f A := by
  intro u hu v hv he
  obtain ⟨y,hy,hay⟩ := hD (f u)
  have hfy : G.Adj (f u) v := he ▸ (h v hv).2.symm
  exact ((deg_two_only G (h u hu).1 (h u hu).2.symm hay
    (fun e => hA u hu (e ▸ hy)) hfy).resolve_right
    (fun e => hA v hv (e ▸ hy))).symm

private theorem three_edge_count (hT : G.IsTree) (D U X : Finset V)
    (hD : TotalDominates G D) (hDne : D.Nonempty)
    (hDU : Disjoint D U) (hDX : Disjoint D X) (hUX : Disjoint U X)
    (x y z : V → V) (hix : Set.InjOn x U)
    (hx : ∀ u ∈ U, x u ∈ X ∧ G.Adj u (x u))
    (hy : ∀ u ∈ U, y u ∈ D ∧ G.Adj (x u) (y u))
    (hz : ∀ u ∈ U, z u ∈ D ∧ G.Adj u (z u))
    (hcardX : X.card = U.card) : 2 * U.card + 2 ≤ D.card := by
  classical
  let F := D ∪ U ∪ X
  have hF : F.Nonempty := hDne.mono (fun _ h => mem_union_left _ (mem_union_left _ h))
  have hFD : D ⊆ F := fun _ h => mem_union_left _ (mem_union_left _ h)
  have hFU : U ⊆ F := fun _ h => mem_union_left _ (mem_union_right _ h)
  have hFX : X ⊆ F := fun _ h => mem_union_right _ h
  let tag (v : V) : Fin 3 := if v ∈ D then 0 else if v ∈ U then 1 else 2
  have tD {v : V} (h : v ∈ D) : tag v = 0 := by simp [tag,h]
  have tU {v : V} (h : v ∈ U) : tag v = 1 := by
    have hn : v ∉ D := fun hd => (disjoint_left.mp hDU) hd h
    simp [tag,h,hn]
  have tX {v : V} (h : v ∈ X) : tag v = 2 := by
    have hnd : v ∉ D := fun hd => (disjoint_left.mp hDX) hd h
    have hnu : v ∉ U := fun hu => (disjoint_left.mp hUX) hu h
    simp [tag,hnd,hnu]
  let C (c : Sym2 (Fin 3)) := (edgesWithin G F).filter fun e => e.map tag = c
  let c0 : Sym2 (Fin 3) := s(0,0)
  let c1 : Sym2 (Fin 3) := s(1,0)
  let c2 : Sym2 (Fin 3) := s(1,2)
  let c3 : Sym2 (Fin 3) := s(2,0)
  have count_between (f g : V → V) (c : Sym2 (Fin 3))
      (hs : ∀ u ∈ U, s(g u,f u) ∈ C c)
      (hi : Set.InjOn (fun u => (s(g u,f u) : Sym2 V)) U) : U.card ≤ (C c).card :=
    card_le_card_of_injOn _ hs hi
  have distinct_tags (f g : V → V) (i j : Fin 3) (hn : i ≠ j)
      (hg : ∀ u ∈ U, tag (g u) = i) (hf : ∀ u ∈ U, tag (f u) = j)
      (hi : Set.InjOn g U) : Set.InjOn (fun u => (s(g u,f u) : Sym2 V)) U := by
    intro u hu v hv he
    rcases Sym2.mk_eq_mk_iff.mp he with he | he
    · exact hi hu hv (congrArg Prod.fst he)
    · have he' : g u = f v := congrArg Prod.fst he
      exact (hn ((hg u hu).symm.trans (he' ▸ hf v hv))).elim
  have h00 : (edgesWithin G D).card ≤ (C c0).card := by
    apply card_le_card
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab,ha,hb⟩ := (edge_spec _ _ _ _).mp he
      exact mem_filter.mpr ⟨(edge_spec _ _ _ _).mpr ⟨hab,hFD ha,hFD hb⟩,
        by simp [c0,Sym2.map_pair_eq,tD ha,tD hb]⟩
  have h01 : U.card ≤ (C c1).card := by
    apply count_between z id
    · intro u hu
      exact mem_filter.mpr ⟨(edge_spec _ _ _ _).mpr ⟨(hz u hu).2,hFU hu,hFD (hz u hu).1⟩,
        by simp [c1,Sym2.map_pair_eq,tU hu,tD (hz u hu).1]⟩
    · exact distinct_tags z id 1 0 (by decide) (fun u hu => tU hu)
        (fun u hu => tD (hz u hu).1) Function.injective_id.injOn
  have h02 : U.card ≤ (C c2).card := by
    apply count_between x id
    · intro u hu
      exact mem_filter.mpr ⟨(edge_spec _ _ _ _).mpr ⟨(hx u hu).2,hFU hu,hFX (hx u hu).1⟩,
        by simp [c2,Sym2.map_pair_eq,tU hu,tX (hx u hu).1]⟩
    · exact distinct_tags x id 1 2 (by decide) (fun u hu => tU hu)
        (fun u hu => tX (hx u hu).1) Function.injective_id.injOn
  have h03 : U.card ≤ (C c3).card := by
    apply count_between y x
    · intro u hu
      exact mem_filter.mpr ⟨(edge_spec _ _ _ _).mpr ⟨(hy u hu).2,hFX (hx u hu).1,hFD (hy u hu).1⟩,
        by simp [c3,Sym2.map_pair_eq,tX (hx u hu).1,tD (hy u hu).1]⟩
    · exact distinct_tags y x 2 0 (by decide) (fun u hu => tX (hx u hu).1)
        (fun u hu => tD (hy u hu).1) hix
  have dis {a b : Sym2 (Fin 3)} (h : a ≠ b) : Disjoint (C a) (C b) :=
    disjoint_left.mpr fun _ ha hb =>
      h ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
  have hunion : (C c0 ∪ C c1 ∪ C c2 ∪ C c3) ⊆ edgesWithin G F := by
    repeat' apply union_subset
    all_goals exact filter_subset _ _
  have hedges := card_le_card hunion
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨dis (by decide : c0 ≠ c3),dis (by decide : c1 ≠ c3)⟩,dis (by decide : c2 ≠ c3)⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨dis (by decide : c0 ≠ c2),dis (by decide : c1 ≠ c2)⟩),
    card_union_of_disjoint (dis (by decide : c0 ≠ c1))] at hedges
  have hcF : F.card = D.card + U.card + X.card := by
    unfold F
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hDX,hUX⟩), card_union_of_disjoint hDU]
  have hE := edge_count G hT hF
  rw [hcF,hcardX] at hE
  have hDcount := counting_internal G D hD
  omega

/-- In fact we obtain a slack of two in the integral form. -/
theorem bound_for_dominating_set (hT : G.IsTree) (D : Finset V)
    (hD : TotalDominates G D) : 2 * (outerNeighbors G).card + 2 ≤ 3 * D.card := by
  classical
  obtain ⟨v⟩ := hT.isConnected.nonempty
  obtain ⟨d,hd,_⟩ := hD v
  have hnD : D.Nonempty := ⟨d,hd⟩
  let B := outerNeighbors G
  let B₀ := B ∩ D
  let hit (u : V) : Prop := ∃ x ∈ D, G.degree x = 2 ∧ G.Adj u x
  let B₁ := (B \ D).filter hit
  let U := (B \ D) \ B₁
  have hsplit : B.card = B₀.card + B₁.card + U.card := by
    have h₀ := card_inter_add_card_sdiff B D
    have h₁ := card_sdiff_add_card_eq_card (filter_subset hit (B \ D))
    change B₀.card + (B \ D).card = B.card at h₀
    change U.card + B₁.card = (B \ D).card at h₁
    omega
  have hB₁ (u : V) (hu : u ∈ B₁) : u ∉ D ∧ hit u := by
    exact ⟨(mem_sdiff.mp (mem_filter.mp hu).1).2,(mem_filter.mp hu).2⟩
  have hU (u : V) (hu : u ∈ U) : u ∈ B ∧ u ∉ D ∧ ¬hit u := by
    obtain ⟨h,hf⟩ := mem_sdiff.mp hu
    exact ⟨(mem_sdiff.mp h).1,(mem_sdiff.mp h).2,fun hh => hf (mem_filter.mpr ⟨h,hh⟩)⟩
  have hbudget : B₀.card + B₁.card ≤ D.card := by
    have h : ∀ u ∈ B₁, ∃ x ∈ D, G.degree x = 2 ∧ G.Adj u x :=
      fun u hu => (hB₁ u hu).2
    have h' (u : V) : ∃ x, u ∈ B₁ → x ∈ D ∧ G.degree x = 2 ∧ G.Adj u x := by
      by_cases hu : u ∈ B₁
      · obtain ⟨x,hx,ha⟩ := h u hu
        exact ⟨x,fun _ => ⟨hx,ha⟩⟩
      · exact ⟨d,fun hh => (hu hh).elim⟩
    choose f hf using h'
    have hfm (u : V) (hu : u ∈ B₁) := (hf u hu).1
    have hfa (u : V) (hu : u ∈ B₁) := (hf u hu).2
    have hi := inject_neighbors G D hD B₁ (fun u hu => (hB₁ u hu).1) f hfa
    let S := B₁.image f
    have hcS : S.card = B₁.card := card_image_of_injOn hi
    have hs : Disjoint B₀ S := by
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨y,hyB,rfl⟩ := mem_image.mp hy
      exact ((mem_outer G (f y)).mp (mem_inter.mp hx).1).1 (hfa y hyB).1
    have hsub : B₀ ∪ S ⊆ D := by
      apply union_subset inter_subset_right
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact hfm y hy
    have hh := card_le_card hsub
    rw [card_union_of_disjoint hs,hcS] at hh
    exact hh
  have hw (u : V) (hu : u ∈ U) :
      ∃ x, (G.degree x = 2 ∧ G.Adj u x) ∧ x ∉ D := by
    obtain ⟨x,hx⟩ := ((mem_outer G u).mp (hU u hu).1).2
    exact ⟨x,hx,fun h => (hU u hu).2.2 ⟨x,h,hx⟩⟩
  have hw' (u : V) : ∃ x, u ∈ U → (G.degree x = 2 ∧ G.Adj u x) ∧ x ∉ D := by
    by_cases hu : u ∈ U
    · obtain ⟨x,ha,hm⟩ := hw u hu
      exact ⟨x,fun _ => ⟨ha,hm⟩⟩
    · exact ⟨d,fun hh => (hu hh).elim⟩
  choose x hxs using hw'
  have hx (u : V) (hu : u ∈ U) := (hxs u hu).1
  have hxn (u : V) (hu : u ∈ U) := (hxs u hu).2
  have hix := inject_neighbors G D hD U (fun u hu => (hU u hu).2.1) x hx
  have has_y (u : V) : ∃ y ∈ D, G.Adj (x u) y := hD _
  have has_z (u : V) : ∃ z ∈ D, G.Adj u z := hD _
  choose y hym hya using has_y
  choose z hzm hza using has_z
  let X := U.image x
  have hcX : X.card = U.card := card_image_of_injOn hix
  have hdU : Disjoint D U := disjoint_left.mpr fun u hd hu => (hU u hu).2.1 hd
  have hdX : Disjoint D X := by
    apply disjoint_left.mpr
    intro w hd hX
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hX
    exact hxn u hu hd
  have huX : Disjoint U X := by
    apply disjoint_left.mpr
    intro w hu hx'
    obtain ⟨u,hu',rfl⟩ := mem_image.mp hx'
    exact ((mem_outer G (x u)).mp (hU _ hu).1).1 (hx u hu').1
  have hUC := three_edge_count G hT D U X hD hnD hdU hdX huX x y z hix
    (fun u hu => ⟨mem_image_of_mem x hu,(hx u hu).2⟩)
    (fun u _ => ⟨hym u,hya u⟩) (fun u _ => ⟨hzm u,hza u⟩) hcX
  change 2 * B.card + 2 ≤ 3 * D.card
  omega

def totalDominationNumber : ℕ :=
  sInf {n : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = n}

/-- Exact integral form, with a stronger additive slack. -/
theorem conjecture348 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    2 * (outerNeighbors G).card + 2 ≤ 3 * totalDominationNumber G := by
  classical
  have hall : TotalDominates G univ := by
    intro v
    obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
    obtain ⟨p⟩ := hT.isConnected v w
    cases p with
    | nil => exact (hw rfl).elim
    | cons ha _ => exact ⟨_,mem_univ _,ha⟩
  have hne : {n : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = n}.Nonempty :=
    ⟨univ.card,univ,hall,rfl⟩
  obtain ⟨D,hD,hc⟩ := Nat.sInf_mem hne
  unfold totalDominationNumber
  exact hc ▸ bound_for_dominating_set G hT D hD

/-- The literal rational inequality from the catalogue. -/
theorem catalogue348 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    (2 / 3 : ℚ) * ((outerNeighbors G).card : ℚ) ≤ (totalDominationNumber G : ℚ) := by
  have h := conjecture348 G hT hn
  have h' : (2 : ℚ) * (outerNeighbors G).card + 2 ≤ 3 * (totalDominationNumber G : ℚ) := by
    exact_mod_cast h
  linarith

#print axioms catalogue348
#print axioms conjecture348

end
end Graffiti348
