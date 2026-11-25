import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.List.Sort

/-!
# Written on the Wall II, conjecture 344

A consequence of DeLaViña, Larson, Pepper and Waller, “On total domination
and support vertices of a tree” (2010), Theorem 4 (catalogue #332).
This standalone Lean formalization proves the required bound and all
bridges to the exact catalogue statement. It does not claim research priority.

Published theorem: https://math1um.github.io/Research/r08.pdf
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti344

open SimpleGraph SimpleGraph.Walk Finset

section Tree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Leaves, support vertices, and isolated vertices of the support-induced graph. -/
def IsLeaf (v : V) : Prop := G.degree v = 1

def IsSupport (v : V) : Prop := ∃ w, G.Adj v w ∧ IsLeaf G w

def IsIsoSupport (v : V) : Prop :=
  IsSupport G v ∧ ∀ w, G.Adj v w → ¬ IsSupport G w

noncomputable def leaves : Finset V := by
  classical
  exact univ.filter (IsLeaf G)

noncomputable def supports : Finset V := by
  classical
  exact univ.filter (IsSupport G)

noncomputable def isoSupports : Finset V := by
  classical
  exact univ.filter (IsIsoSupport G)

omit [DecidableEq V] in
@[simp] theorem mem_leaves (v : V) : v ∈ leaves G ↔ IsLeaf G v := by
  classical
  simp [leaves]

omit [DecidableEq V] in
@[simp] theorem mem_supports (v : V) : v ∈ supports G ↔ IsSupport G v := by
  classical
  simp [supports]

omit [DecidableEq V] in
@[simp] theorem mem_isoSupports (v : V) : v ∈ isoSupports G ↔ IsIsoSupport G v := by
  classical
  simp [isoSupports]

def IsTotalDominating (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber : ℕ :=
  sInf {k | ∃ D : Finset V, IsTotalDominating G D ∧ D.card = k}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem totalDominationNumber_le {D : Finset V} (hD : IsTotalDominating G D) :
    totalDominationNumber G ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

variable {G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem closed_of_walk {P : V → Prop}
    (hstep : ∀ a b, P a → G.Adj a b → P b) {a b : V}
    (p : G.Walk a b) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | cons hab _ ih => exact ih (hstep _ _ ha hab)

omit [DecidableEq V] in
private theorem leaf_unique {x y z : V} (hx : IsLeaf G x)
    (hy : G.Adj x y) (hz : G.Adj x z) : y = z := by
  classical
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hx
  have hy' := (G.mem_neighborFinset x y).2 hy
  have hz' := (G.mem_neighborFinset x z).2 hz
  rw [hu] at hy' hz'
  exact (Finset.mem_singleton.mp hy').trans (Finset.mem_singleton.mp hz').symm

omit [DecidableEq V] in
private theorem leaf_of_unique {x y : V} (hy : G.Adj x y)
    (h : ∀ z, G.Adj x z → z = y) : IsLeaf G x := by
  classical
  have he : G.neighborFinset x = {y} := by
    ext z
    simp only [G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · exact h z
    · rintro rfl
      exact hy
  exact congrArg Finset.card he

private theorem leaf_not_support (hc : G.Connected) (hn : 2 < Fintype.card V)
    {x : V} (hx : IsLeaf G x) : ¬ IsSupport G x := by
  rintro ⟨y, hxy, hy⟩
  have hstep (a b : V) (ha : a = x ∨ a = y) (hab : G.Adj a b) : b = x ∨ b = y := by
    rcases ha with rfl | rfl
    · exact Or.inr (leaf_unique hx hab hxy)
    · exact Or.inl (leaf_unique hy hab hxy.symm)
  have hcover : ({x, y} : Finset V) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨p⟩ := hc x z
    simpa using closed_of_walk hstep p (Or.inl rfl)
  have he := congrArg Finset.card hcover
  simp [hxy.ne] at he
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem root_parent (ht : G.IsTree) {v r : V} (hne : v ≠ r) :
    ∃ a, G.Adj v a ∧ G.dist a r + 1 = G.dist v r ∧
      ∀ b, G.Adj v b → b ≠ a → G.dist v r + 1 = G.dist b r := by
  classical
  obtain ⟨p, hp, hdist⟩ := ht.isConnected.exists_path_of_dist v r
  have unique {x : V} {q : G.Walk x r} (hq : q.IsPath) : q.length = G.dist x r := by
    obtain ⟨q', hq', hd⟩ := ht.isConnected.exists_path_of_dist x r
    have he : (⟨q,hq⟩ : G.Path x r) = ⟨q',hq'⟩ := ht.IsAcyclic.path_unique _ _
    exact (congrArg (fun p : G.Path x r => p.val.length) he).trans hd
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ a _ hva p =>
    have htail := hp.of_cons
    have hlen : p.length = G.dist a r := unique htail
    refine ⟨a, hva, by simpa [hlen] using hdist, ?_⟩
    intro b hvb hba
    by_cases hb : b ∈ p.support
    · have hv : v ∉ p.support := (cons_isPath_iff _ _).1 hp |>.2
      have hq : (Walk.cons hvb (p.dropUntil b hb)).IsPath :=
        (htail.dropUntil hb).cons (fun hm => hv (support_dropUntil_subset _ _ hm))
      have he : (⟨.cons hva p, hp⟩ : G.Path v r) = ⟨.cons hvb (p.dropUntil b hb), hq⟩ :=
        ht.IsAcyclic.path_unique _ _
      have he' := congrArg (fun p : G.Path v r => p.val.getVert 1) he
      have hab : a = b := by simpa using he'
      exact (hba hab.symm).elim
    · have hb' : b ∉ (Walk.cons hva p).support := by
        simp [hvb.ne.symm, hb]
      have hq := hp.cons (h := hvb.symm) hb'
      simpa [hdist] using unique hq

omit [DecidableEq V] in
private theorem farthest_leaf (ht : G.IsTree) (r : V) (hr : ∃ x, x ≠ r) :
    ∃ v, IsLeaf G v ∧ ∀ x, G.dist x r ≤ G.dist v r := by
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image (univ : Finset V) (fun x => G.dist x r)
    ⟨r, mem_univ _⟩
  have hv' : ∀ x, G.dist x r ≤ G.dist v r := fun x => hv x (mem_univ x)
  have hne : v ≠ r := by
    rintro rfl
    obtain ⟨x, hx⟩ := hr
    exact hx ((ht.isConnected.dist_eq_zero_iff).1 (Nat.eq_zero_of_le_zero
      (by simpa [SimpleGraph.dist_self] using hv' x)))
  obtain ⟨a, ha, _, hb⟩ := root_parent ht hne
  refine ⟨v, leaf_of_unique ha ?_, hv'⟩
  intro b hab
  by_contra! h
  have e := hb b hab h
  have l := hv' b
  omega

omit [DecidableEq V] in
private theorem order_nontrivial (hn : 2 < Fintype.card V) : Nontrivial V :=
  Fintype.one_lt_card_iff_nontrivial.mp (by omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem has_neighbor (hc : G.Connected) [Nontrivial V] (v : V) :
    ∃ w, G.Adj v w := by
  obtain ⟨z,hz⟩ := exists_ne v
  obtain ⟨p⟩ := hc v z
  cases p with
  | nil => exact (hz rfl).elim
  | cons h _ => exact ⟨_,h⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem totalDominationNumber_attained (hc : G.Connected) (hn : 2 < Fintype.card V) :
    ∃ D : Finset V, IsTotalDominating G D ∧ D.card = totalDominationNumber G := by
  letI := order_nontrivial hn
  let s : Set ℕ := {k | ∃ D : Finset V, IsTotalDominating G D ∧ D.card = k}
  have h : s.Nonempty := ⟨Fintype.card V, univ, fun v => by
    obtain ⟨w, hw⟩ := has_neighbor hc v
    exact ⟨w, mem_univ w, hw⟩, card_univ⟩
  exact Nat.sInf_mem h

omit [DecidableEq V] in
private theorem exists_leaf (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    ∃ v, IsLeaf G v := by
  letI := order_nontrivial hn
  obtain ⟨r⟩ := ht.isConnected.nonempty
  obtain ⟨v,hv,_⟩ := farthest_leaf ht r (exists_ne r)
  exact ⟨v,hv⟩

omit [DecidableEq V] in
/-- A vertex whose neighbors are all leaves is adjacent to all other vertices. -/
private theorem star_of_all_neighbors_leaf (hc : G.Connected) {r : V}
    (hr : ∀ w, G.Adj r w → IsLeaf G w) : ∀ w, w ≠ r → G.Adj r w := by
  have hstep (a b : V) (ha : a = r ∨ G.Adj r a) (hab : G.Adj a b) :
      b = r ∨ G.Adj r b := by
    rcases ha with rfl | ha
    · exact Or.inr hab
    · exact Or.inl (leaf_unique (hr a ha) hab ha.symm)
  intro w hw
  obtain ⟨p⟩ := hc r w
  exact (closed_of_walk hstep p (Or.inl rfl)).resolve_left hw

omit [Fintype V] [DecidableRel G.Adj] in
private theorem totalDominationNumber_star_le (r : V) [Nontrivial V]
    (hstar : ∀ w, w ≠ r → G.Adj r w) : totalDominationNumber G ≤ 2 := by
  obtain ⟨s, hs⟩ := exists_ne r
  have hd : IsTotalDominating G {r,s} := by
    intro v
    by_cases h : v = r
    · exact ⟨s, by simp, h.symm ▸ hstar s hs⟩
    · exact ⟨r, by simp, (hstar v h).symm⟩
  simpa [hs.symm] using totalDominationNumber_le G hd

private noncomputable def leafOf (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : V := by
  classical
  exact if h : IsSupport G v then Classical.choose h else v

omit [DecidableEq V] in
private theorem leafOf_spec {v : V} (hv : IsSupport G v) :
    G.Adj v (leafOf G v) ∧ IsLeaf G (leafOf G v) := by
  classical
  simpa [leafOf, hv] using Classical.choose_spec hv

omit [DecidableEq V] in
private theorem supports_card_le_leaves : (supports G).card ≤ (leaves G).card := by
  apply Finset.card_le_card_of_injOn (leafOf G)
  · intro v hv
    exact (mem_leaves G _).2 (leafOf_spec ((mem_supports G _).1 hv)).2
  · intro a ha b hb hab
    have e₁ := leafOf_spec ((mem_supports G _).1 ha)
    have e₂ := leafOf_spec ((mem_supports G _).1 hb)
    exact leaf_unique e₁.2 e₁.1.symm (hab.symm ▸ e₂.1.symm)

private theorem support_leaf_disjoint (hc : G.Connected) (hn : 2 < Fintype.card V) :
    Disjoint (supports G) (leaves G) := by
  apply Finset.disjoint_left.mpr
  intro v hs hl
  exact leaf_not_support hc hn ((mem_leaves G _).1 hl) ((mem_supports G _).1 hs)

/-- The tree bound of DeLaViña, Larson, Pepper and Waller (catalogue 332). -/
theorem bound332 (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    2 * totalDominationNumber G ≤ Fintype.card V + (isoSupports G).card := by
  classical
  letI := order_nontrivial hn
  let S := supports G
  let L := leaves G
  let I := isoSupports G
  by_cases star : ∃ r, ∀ w, w ≠ r → G.Adj r w
  · obtain ⟨r, hr⟩ := star
    have hl (v : V) (hv : v ≠ r) : IsLeaf G v := by
      apply leaf_of_unique (hr v hv).symm
      intro w hvw
      by_contra! hw
      have he : (⟨Walk.cons hvw (Walk.cons (hr w hw).symm .nil),
        (Walk.IsPath.of_adj (hr w hw).symm).cons (by simp [hvw.ne, hv])⟩ : G.Path v r) =
          Path.singleton (hr v hv).symm := ht.IsAcyclic.path_unique _ _
      have he' := congrArg (fun p : G.Path v r => p.val.length) he
      simp [Path.singleton] at he'
    obtain ⟨u, hu⟩ := exists_ne r
    have hs : IsSupport G r := ⟨u, hr u hu, hl u hu⟩
    have hi : r ∈ I := (mem_isoSupports G r).2
      ⟨hs, fun w hw => leaf_not_support ht.isConnected hn (hl w hw.ne.symm)⟩
    have hp : 0 < I.card := Finset.card_pos.2 ⟨r, hi⟩
    have hγ := totalDominationNumber_star_le r hr
    change 2 * totalDominationNumber G ≤ Fintype.card V + I.card
    omega
  obtain ⟨r, hr⟩ := exists_leaf ht hn
  let U := (univ : Finset V) \ (S ∪ L)
  let color : V → Prop := fun v => (G.dist v r / 2) % 2 = 0
  have hneighbor : ∀ v, ∃ w, G.Adj v w ∧ ¬ IsLeaf G w := by
    intro v
    by_cases he : ∃ w, G.Adj v w ∧ ¬ IsLeaf G w
    · exact he
    exfalso
    refine star ⟨v, star_of_all_neighbors_leaf ht.isConnected ?_⟩
    intro w hw
    by_contra hn'
    exact he ⟨w,hw,hn'⟩
  let pick : V → V := fun v => Classical.choose (hneighbor v)
  have hp (v : V) := Classical.choose_spec (hneighbor v)
  let A := S ∪ U.filter color ∪ (I.filter (fun v => ¬ color (pick v))).image (leafOf G)
  let B := S ∪ U.filter (fun v => ¬ color v) ∪ (I.filter (fun v => color (pick v))).image (leafOf G)
  have inU (v : V) (hs : ¬ IsSupport G v) (hl : ¬ IsLeaf G v) : v ∈ U := by
    simp [U, S, L, hs, hl]
  have cover (v : V) : ∃ a ∈ A, ∃ b ∈ B, G.Adj v a ∧ G.Adj v b := by
    by_cases hsup : ∃ w, G.Adj v w ∧ IsSupport G w
    · obtain ⟨w, hw, hs⟩ := hsup
      exact ⟨w, by simp [A,S,hs], w, by simp [B,S,hs], hw, hw⟩
    have hnbr (w : V) (hw : G.Adj v w) : ¬ IsSupport G w := fun h => hsup ⟨w,hw,h⟩
    by_cases hv : IsSupport G v
    · have hI : v ∈ I := (mem_isoSupports G _).2 ⟨hv,hnbr⟩
      have hu : pick v ∈ U := inU _ (hnbr _ (hp v).1) (hp v).2
      have hleaf := leafOf_spec hv
      by_cases hcol : color (pick v)
      · exact ⟨pick v, by simp [A,hu,hcol], leafOf G v,
          mem_union_right _ (mem_image.mpr ⟨v,mem_filter.mpr ⟨hI,hcol⟩,rfl⟩),
          (hp v).1, hleaf.1⟩
      · exact ⟨leafOf G v,
          mem_union_right _ (mem_image.mpr ⟨v,mem_filter.mpr ⟨hI,hcol⟩,rfl⟩),
          pick v, by simp [B,hu,hcol], hleaf.1, (hp v).1⟩
    have hnl : ¬ IsLeaf G v := by
      intro hl
      obtain ⟨w, hw⟩ := has_neighbor ht.isConnected v
      exact hnbr w hw ⟨v, hw.symm, hl⟩
    have hner : v ≠ r := fun e => hnl (e.symm ▸ hr)
    obtain ⟨a, ha, hda, hother⟩ := root_parent ht hner
    have hnonly : ∃ b, G.Adj v b ∧ b ≠ a := by
      by_contra! h
      exact hnl (leaf_of_unique ha h)
    obtain ⟨b, hb, hba⟩ := hnonly
    have hdb := hother b hb hba
    have hcol : color a ↔ ¬ color b := by
      dsimp [color]
      omega
    have haU := inU a (hnbr a ha) (fun hl => hv ⟨a,ha,hl⟩)
    have hbU := inU b (hnbr b hb) (fun hl => hv ⟨b,hb,hl⟩)
    by_cases hc : color a
    · have hc' := hcol.mp hc
      exact ⟨a, by simp [A,haU,hc], b, by simp [B,hbU,hc'], ha,hb⟩
    · have hc' : color b := by tauto
      exact ⟨b, by simp [A,hbU,hc'], a, by simp [B,haU,hc], hb,ha⟩
  have ha : IsTotalDominating G A := by
    intro v
    obtain ⟨a,hm,_,_,he,_⟩ := cover v
    exact ⟨a,hm,he⟩
  have hb : IsTotalDominating G B := by
    intro v
    obtain ⟨_,_,b,hm,_,he⟩ := cover v
    exact ⟨b,hm,he⟩
  have hcardA : A.card ≤ S.card + (U.filter color).card +
      (I.filter (fun v => ¬ color (pick v))).card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le)
  have hcardB : B.card ≤ S.card + (U.filter (fun v => ¬ color v)).card +
      (I.filter (fun v => color (pick v))).card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le)
  have hU := Finset.filter_card_add_filter_neg_card_eq_card (s := U) color
  have hI := Finset.filter_card_add_filter_neg_card_eq_card (s := I) (fun v => color (pick v))
  have hsl : (S ∪ L).card = S.card + L.card :=
    Finset.card_union_of_disjoint (support_leaf_disjoint ht.isConnected hn)
  have hall : U.card + (S ∪ L).card = Fintype.card V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S ∪ L)), Finset.card_univ]
  have hsupports : S.card ≤ L.card := supports_card_le_leaves
  have hminA := totalDominationNumber_le G ha
  have hminB := totalDominationNumber_le G hb
  change 2 * totalDominationNumber G ≤ Fintype.card V + I.card
  omega

variable (G)

/-- The degree sequence with a separate entry for each vertex, sorted increasingly. -/
noncomputable def degreeSequence : List ℕ :=
  ((univ : Finset V).toList.map (fun v => G.degree v)).mergeSort

omit [DecidableEq V] in
private theorem degreeSequence_length : (degreeSequence G).length = Fintype.card V := by
  simp [degreeSequence]

omit [DecidableEq V] in
private theorem degreeSequence_sorted : (degreeSequence G).Sorted (· ≤ ·) := by
  unfold degreeSequence
  exact List.sorted_mergeSort' (· ≤ ·) _

omit [DecidableEq V] in
theorem degreeSequence_sum :
    (degreeSequence G).sum = 2 * G.edgeFinset.card := by
  rw [degreeSequence, (List.mergeSort_perm _ _).sum_eq, Finset.sum_map_toList,
    G.sum_degrees_eq_twice_card_edges]

/-- Largest admissible prefix of the nondecreasing degree sequence (catalogue definition 89).
The prefix sum is doubled to express the half-degree-sum cutoff exactly. -/
noncomputable def annihilationNumber : ℕ :=
  Nat.findGreatest (fun k => 2 * ((degreeSequence G).take k).sum ≤ (degreeSequence G).sum)
    (Fintype.card V)

omit [DecidableEq V] in
/-- The annihilation number attains the edge-count budget and is maximal for it. -/
theorem annihilationNumber_spec :
    annihilationNumber G ≤ Fintype.card V ∧
    ((degreeSequence G).take (annihilationNumber G)).sum ≤ G.edgeFinset.card ∧
    ∀ k ≤ Fintype.card V, ((degreeSequence G).take k).sum ≤ G.edgeFinset.card →
      k ≤ annihilationNumber G := by
  have hsum := degreeSequence_sum G
  refine ⟨Nat.findGreatest_le _, ?_, ?_⟩
  · have h : 2 * ((degreeSequence G).take (annihilationNumber G)).sum ≤
        (degreeSequence G).sum := by
      unfold annihilationNumber
      exact Nat.findGreatest_spec
        (P := fun k => 2 * ((degreeSequence G).take k).sum ≤ (degreeSequence G).sum)
        (m := 0) (Nat.zero_le _) (by simp)
    omega
  · intro k hk he
    unfold annihilationNumber
    apply Nat.le_findGreatest hk
    omega

private theorem sum_le_of_all_le {a b : List ℕ} (hlen : a.length ≤ b.length)
    (horder : ∀ x ∈ a, ∀ y ∈ b, x ≤ y) : a.sum ≤ b.sum := by
  induction a generalizing b with
  | nil => simp
  | cons x l ih =>
    cases b with
    | nil => simp at hlen
    | cons y m =>
      have hxy := horder x (by simp) y (by simp)
      have htail : l.sum ≤ m.sum := by
        apply ih (by simpa using hlen)
        intro u hu v hv
        exact horder u (by simp [hu]) v (by simp [hv])
      simp only [List.sum_cons]
      omega

omit [DecidableEq V] in
theorem half_le_annihilation : Fintype.card V / 2 ≤ annihilationNumber G := by
  let l := degreeSequence G
  let k := l.length / 2
  have hlen : k ≤ l.length := by dsimp [k]; omega
  have hl : (l.take k).length ≤ (l.drop k).length := by
    simp only [List.length_take, List.length_drop, min_eq_left hlen, k]
    omega
  have hsorted : (l.take k ++ l.drop k).Pairwise (· ≤ ·) := by
    rw [List.take_append_drop]
    exact degreeSequence_sorted G
  have hs := sum_le_of_all_le hl (List.pairwise_append.mp hsorted).2.2
  have he : (l.take k).sum + (l.drop k).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hfit : 2 * (l.take k).sum ≤ l.sum := by omega
  have hmax : k ≤ annihilationNumber G := by
    unfold annihilationNumber
    exact Nat.le_findGreatest (by simpa [l, degreeSequence_length] using hlen) hfit
  simpa [k, l, degreeSequence_length] using hmax

omit [DecidableEq V] in
private theorem two_le_annihilation_of_three_with_zero (hn : Fintype.card V = 3)
    (hzero : ∃ v, G.degree v = 0) : 2 ≤ annihilationNumber G := by
  have hlen : (degreeSequence G).length = 3 := (degreeSequence_length G).trans hn
  obtain ⟨v, hv⟩ := hzero
  have hm : 0 ∈ degreeSequence G := by
    unfold degreeSequence
    exact List.mem_mergeSort.mpr (List.mem_map.mpr ⟨v, by simp, hv⟩)
  have hsort := degreeSequence_sorted G
  have hfit : 2 * ((degreeSequence G).take 2).sum ≤ (degreeSequence G).sum := by
    generalize degreeSequence G = l at hlen hm hsort ⊢
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨x, xs⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons] at hlen
    any_goals omega
    have hab := (List.rel_of_sorted_cons hsort) b (by simp)
    have hac := (List.rel_of_sorted_cons hsort) c (by simp)
    have hbc := (List.rel_of_sorted_cons hsort.of_cons) c (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    simp [List.sum_cons]
    omega
  unfold annihilationNumber
  exact Nat.le_findGreatest (by omega) hfit

variable {G}

/-- Written on the Wall II, entry 342. -/
private theorem conjecture342 [DecidableRel Gᶜ.Adj] (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber G ≤ annihilationNumber Gᶜ + ((isoSupports G).card + 1) / 2 := by
  have hd := bound332 ht hn
  have ha := half_le_annihilation Gᶜ
  omega

variable (G)

omit [DecidableEq V] in
open scoped Classical in
/-- The isolated support predicate is exactly degree zero in the support-induced graph. -/
theorem isIsoSupport_iff_induceDegreeZero (v : V) (hv : IsSupport G v) :
    IsIsoSupport G v ↔ (G.induce {w | IsSupport G w}).degree ⟨v,hv⟩ = 0 := by
  let H := G.induce {w | IsSupport G w}
  let u : {w // IsSupport G w} := ⟨v,hv⟩
  change IsIsoSupport G v ↔ H.degree u = 0
  constructor
  · intro hi
    by_contra hnz
    obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj u).1 (by omega)
    exact hi.2 w.val hw w.prop
  · intro hz
    refine ⟨hv, fun w hw hsup => ?_⟩
    have hp := (H.degree_pos_iff_exists_adj u).2 ⟨⟨w,hsup⟩, hw⟩
    omega

/-- The graph induced by the leaves together with their open neighborhood, which is the
set of support vertices. It is used here as a graph, and may have multiple components. -/
def supportLeafGraph : SimpleGraph {v : V // IsSupport G v ∨ IsLeaf G v} :=
  G.induce {v | IsSupport G v ∨ IsLeaf G v}

noncomputable def supportLeafComponents : ℕ :=
  Nat.card (supportLeafGraph G).ConnectedComponent

variable {G}

omit [DecidableEq V] in
private theorem iso_component_unique {r w : V} (hr : IsIsoSupport G r) (hw : IsSupport G w)
    (he : (supportLeafGraph G).connectedComponentMk ⟨r, Or.inl hr.1⟩ =
       (supportLeafGraph G).connectedComponentMk ⟨w, Or.inl hw⟩) : w = r := by
  let P : {v : V // IsSupport G v ∨ IsLeaf G v} → Prop :=
    fun a => a.val = r ∨ (IsLeaf G a.val ∧ G.Adj r a.val)
  have hstep (a b : {v : V // IsSupport G v ∨ IsLeaf G v})
      (ha : P a) (hab : (supportLeafGraph G).Adj a b) : P b := by
    have hab' : G.Adj a.val b.val := hab
    rcases ha with ha | ⟨ha,har⟩
    · have hrb : G.Adj r b.val := ha ▸ hab'
      exact Or.inr ⟨b.prop.resolve_left (hr.2 _ hrb),hrb⟩
    · exact Or.inl (leaf_unique ha hab' har.symm)
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact he
  rcases closed_of_walk hstep p (Or.inl rfl) with heq | ⟨hl,hadj⟩
  · exact heq
  · exact (hr.2 _ hadj hw).elim

omit [DecidableEq V] in
private theorem finite_supportLeafComponents : Finite (supportLeafGraph G).ConnectedComponent :=
  Finite.of_surjective _ (fun c => Quot.exists_rep c)

omit [DecidableEq V] in
private theorem iso_le_supportLeafComponents :
    (isoSupports G).card ≤ supportLeafComponents G := by
  classical
  letI := finite_supportLeafComponents (G := G)
  let f : ↥(isoSupports G) → (supportLeafGraph G).ConnectedComponent :=
    fun v => (supportLeafGraph G).connectedComponentMk
      ⟨v.val, Or.inl ((mem_isoSupports G _).1 v.prop).1⟩
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact (iso_component_unique ((mem_isoSupports G _).1 v.prop)
      ((mem_isoSupports G _).1 w.prop).1 hvw).symm
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := ↥(isoSupports G)), Fintype.card_coe] at h

omit [DecidableEq V] in
private theorem supportLeafComponents_pos (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    0 < supportLeafComponents G := by
  letI := finite_supportLeafComponents (G := G)
  obtain ⟨v, hv⟩ := exists_leaf ht hn
  exact Finite.card_pos_iff.2 ⟨(supportLeafGraph G).connectedComponentMk ⟨v,Or.inr hv⟩⟩

omit [DecidableEq V] in
private theorem star_of_unique_support (ht : G.IsTree) (hn : 2 < Fintype.card V)
    (r : V) (hr : ∀ v, IsSupport G v → v = r) : ∀ w, w ≠ r → G.Adj r w := by
  letI := order_nontrivial hn
  obtain ⟨v, hv, hmax⟩ := farthest_leaf ht r (exists_ne r)
  obtain ⟨u, hvu⟩ := has_neighbor ht.isConnected v
  have hur := hr u ⟨v,hvu.symm,hv⟩
  have hvr : G.Adj v r := hur ▸ hvu
  have hmaxval : G.dist v r = 1 := dist_eq_one_iff_adj.mpr hvr
  intro w hw
  have hle := hmax w
  have hnz : G.dist w r ≠ 0 := fun h => hw (ht.isConnected.dist_eq_zero_iff.mp h)
  exact (dist_eq_one_iff_adj.mp (by omega : G.dist w r = 1)).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem compl_no_neighbors_of_star {r : V} (hstar : ∀ w, w ≠ r → G.Adj r w) :
    ∀ w, ¬Gᶜ.Adj r w := by
  intro w hw
  have e := (G.compl_adj r w).mp hw
  exact e.2 (hstar w e.1.symm)

private theorem star_case344 [DecidableRel Gᶜ.Adj] (ht : G.IsTree) (hn : 2 < Fintype.card V)
    (hc : supportLeafComponents G = 1) (hi : (isoSupports G).card = 1) :
    totalDominationNumber G ≤ annihilationNumber Gᶜ := by
  letI := order_nontrivial hn
  letI := finite_supportLeafComponents (G := G)
  letI : Subsingleton (supportLeafGraph G).ConnectedComponent :=
    Finite.card_le_one_iff_subsingleton.mp (hc.le)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < (isoSupports G).card)
  have hr' := (mem_isoSupports G _).mp hr
  have huniq (v : V) (hv : IsSupport G v) : v = r :=
    iso_component_unique hr' hv (Subsingleton.elim _ _)
  have hstar := star_of_unique_support ht hn r huniq
  have hγ := totalDominationNumber_star_le r hstar
  suffices ha : 2 ≤ annihilationNumber Gᶜ by omega
  by_cases h3 : Fintype.card V = 3
  · apply two_le_annihilation_of_three_with_zero Gᶜ h3
    refine ⟨r, ?_⟩
    have e : ¬ 0 < (Gᶜ).degree r := by
      rw [(Gᶜ).degree_pos_iff_exists_adj]
      rintro ⟨w, hw⟩
      exact compl_no_neighbors_of_star hstar w hw
    omega
  · have ha := half_le_annihilation Gᶜ
    omega

/-- Written on the Wall II, entry 344. Since annihilationNumber is positive here, natural
subtraction by one agrees with the ordinary subtraction in the catalogue. -/
theorem conjecture344 [DecidableRel Gᶜ.Adj] (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber G ≤ annihilationNumber Gᶜ - 1 + supportLeafComponents G := by
  have ha := half_le_annihilation Gᶜ
  have hc := supportLeafComponents_pos ht hn
  have hi := iso_le_supportLeafComponents (G := G)
  by_cases hcomp : supportLeafComponents G = 1
  · by_cases hiso : (isoSupports G).card = 1
    · have h := star_case344 ht hn hcomp hiso
      omega
    · have h := bound332 ht hn
      omega
  · have h := conjecture342 ht hn
    omega

#print axioms conjecture344

end Tree
end Graffiti344
